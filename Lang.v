(* Lang.v *)
(* A simple concurrent language that can be instrumented for race detection. *)
Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model. (* Make this lightweight? *)

Set Implicit Arguments.

(* Syntax *)
Definition var := nat.
Definition local := nat.
Definition lock := nat.
Definition tid := nat.

Inductive expr : Set :=
| I (n : nat)
| V (a : local)
| Plus (e1 e2 : expr)
| Max (e1 e2 : expr).

Definition ptr := (var * nat)%type.

Instance ptr_dec : EqDec_eq ptr.
Proof. eq_dec_inst. Qed.

Inductive instr : Set :=
| Assign (a : local) (e : expr)
| Load (a : local) (x : ptr)
| Store (x : ptr) (e : expr)
| Lock (m : lock)
| Unlock (m : lock)
| Spawn (t : tid) (li : list instr)
| Wait (t : tid)
| Assert_le (e1 e2 : expr)
(*| Nop*).

Instance expr_eq : EqDec_eq expr.
Proof. eq_dec_inst. Qed.

Lemma instr_eq_dec : forall i j, match j with Spawn _ _ => False | _ => True end
  -> i = j \/ i <> j.
Proof.
  destruct i, j; try solve [right; intro; clarify].
  - destruct (eq_dec a a0); [|right; intro X; inversion X]; clarify.
    destruct (eq_dec e e0); [left | right; intro X; inversion X]; clarify.
  - destruct (eq_dec a a0); [|right; intro X; inversion X]; clarify.
    destruct (eq_dec x x0); [left | right; intro X; inversion X]; clarify.
  - destruct (eq_dec x x0); [|right; intro X; inversion X]; clarify.
    destruct (eq_dec e e0); [left | right; intro X; inversion X]; clarify.
  - destruct (eq_dec m m0); [left | right; intro X; inversion X]; clarify.
  - destruct (eq_dec m m0); [left | right; intro X; inversion X]; clarify.
  - destruct (eq_dec t t0); [left | right; intro X; inversion X]; clarify.
  - destruct (eq_dec e1 e0); [|right; intro X; inversion X]; clarify.
    destruct (eq_dec e2 e3); [left | right; intro X; inversion X]; clarify.
Qed.

Definition prog := list instr.

Section Semantics.
  Definition state := list (tid * list instr).
  Definition env := tid -> local -> nat.

  Definition init_state (P : prog) := [(0, P)].
  Definition init_env (t : tid) (a : local) := 0.

  Fixpoint eval G e := match e with
  | I n => n
  | V a => G a
  | Plus e1 e2 => eval G e1 + eval G e2
  | Max e1 e2 => max (eval G e1) (eval G e2)
  end.

  (* For now, race detection will treat each block as a single location. *)
  Definition operation := @operation tid var lock.

  Inductive conc_op : Type :=
  | Read (t : tid) (x : ptr) (v : nat)
  | Write (t : tid) (x : ptr) (v : nat)
  | ARW (t : tid) (x : ptr) (v : nat) (v' : nat)
  | Alloc (t : tid) (b : var) (n : nat) | Free (t : tid) (b : var).

  Definition thread_of c :=
    match c with
    | Read t _ _ => t
    | Write t _ _ => t
    | ARW t _ _ _ => t
    | Alloc t _ _ => t
    | Free t _ => t
    end.

  Definition to_seq c :=
    match c with
    | Read _ x v => [MRead x v]
    | Write _ x v => [MWrite x v]
    | ARW _ x v v' => [MRead x v; MWrite x v']
    | Alloc _ b n => [MAlloc b n]
    | Free _ b => [MFree b]
    end.

  Definition loc_of c :=
    match c with
    | Read _ x _ => x
    | Write _ x _ => x
    | ARW _ x _ _ => x
    | Alloc _ b _ => (b, 0)
    | Free _ b => (b, 0)
    end.

  Definition write_val c :=
    match c with
    | Write _ _ v => Some v
    | ARW _ _ _ v => Some v
    | _ => None
    end.

  Definition writesb c p :=
    match c with
    | Write _ p' _ => beq p' p
    | ARW _ p' _ _ => beq p' p
    | Alloc _ b _ => beq b (fst p)
    | Free _ b => beq b (fst p)
    | _ => false
    end.

  Definition synchronizes_with c1 c2 := loc_of c1 = loc_of c2 /\
    exists t x v v', c1 = ARW t x v v' \/ c2 = ARW t x v v'.

  Fixpoint drop_b_reads b l :=
    match l with
    | [] => []
    | Read t x v :: rest => if eq_dec (fst x) b then drop_b_reads b rest
                            else Read t x v :: drop_b_reads b rest
    | ARW t x v v' :: rest => if eq_dec (fst x) b
                              then Write t x v' :: drop_b_reads b rest
                              else ARW t x v v' :: drop_b_reads b rest
    | c :: rest => c :: drop_b_reads b rest
    end.

  Hint Rewrite nth_error_single : util.

  Instance Base : @MM_base var _ _ _ _ := { thread_of := thread_of;
    to_seq := to_seq; synchronizes_with := synchronizes_with;
    drop_b_reads := drop_b_reads }.
  Proof.
    - induction ops; clarify.
      rewrite filter_app; destruct a; clarsimp.
      + destruct x as (b', ?); unfold negb, beq; clarify.
        rewrite IHops; auto.
      + destruct x as (b', ?); unfold negb, beq; simpl; destruct (eq_dec b' b);
          clarify; rewrite IHops; auto.
    - destruct c; clarsimp.
      destruct i; clarsimp; omega.
  Defined.        

  Definition upd_env G (t : tid) (a : local) (v : nat) :=
    upd G t (upd (G t) a v).

  Notation Acq t x := (ARW t%nat (x, 0) 0 (S t)).
  Notation Rel t x := (ARW t%nat (x, 0) (S t) 0).

  Inductive exec P G t :
    option operation -> option conc_op -> option state -> env -> Prop :=
  | exec_assign P1 P2 a e rest
      (Hassign : P = P1 ++ (t, Assign a e :: rest) :: P2) :
      exec P G t None None
        (Some (P1 ++ (t, rest) :: P2)) (upd_env G t a (eval (G t) e))

  | exec_load P1 P2 a x v rest
      (Hload : P = P1 ++ (t, Load a x :: rest) :: P2) :
      exec P G t (Some (rd t (fst x))) (Some (Read t x v))
        (Some (P1 ++ (t, rest) :: P2)) (upd_env G t a v)

  | exec_store P1 P2 x e rest
      (Hstore : P = P1 ++ (t, Store x e :: rest) :: P2) :
      exec P G t (Some (wr t (fst x))) (Some (Write t x (eval (G t) e)))
        (Some (P1 ++ (t, rest) :: P2)) G

  | exec_lock P1 P2 m rest
      (Hlock : P = P1 ++ (t, Lock m :: rest) :: P2) :
      exec P G t (Some (acq t m)) (Some (Acq t m))
        (Some (P1 ++ (t, rest) :: P2)) G

  | exec_unlock P1 P2 m rest
      (Hunlock : P = P1 ++ (t, Unlock m :: rest) :: P2) :
      exec P G t (Some (rel t m)) (Some (Rel t m))
        (Some (P1 ++ (t, rest) :: P2)) G

  | exec_spawn P1 P2 u li rest
      (Hspawn : P = P1 ++ (t, Spawn u li :: rest) :: P2)
      (Hnew : ~In u (map fst P)) :
      exec P G t (Some (fork t u)) None
           (Some (P1 ++ (t, rest) :: (u, li) :: P2)) G

  | exec_wait P1 P2 u rest
      (Hwait : P = P1 ++ (t, Wait u :: rest) :: P2) (Hdone : In (u, []) P) :
      exec P G t (Some (join t u)) None (Some (P1 ++ (t, rest) :: P2)) G

  | exec_assert_pass P1 P2 e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hpass : eval (G t) e1 <= eval (G t) e2) :
      exec P G t None None (Some (P1 ++ (t, rest) :: P2)) G

  | exec_assert_fail P1 P2 e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hfail : ~eval (G t) e1 <= eval (G t) e2) :
      exec P G t None None None G
  (*| exec_nop P1 P2 t rest
      (Hnop : P=P1++(t,Nop::rest)::P2):
      exec P G None None (Some (P1++(t,rest)::P2)) G*).

  Definition opt_to_list A (x : option A) :=
    match x with
    | Some a => [a]
    | None => []
    end.

  Inductive exec_star : option state -> env ->
    list operation -> list conc_op -> option state -> env -> Prop :=
  | exec_refl P G : exec_star P G [] [] P G
  | exec_step P G t o c P' G' (Hexec : exec P G t o c P' G') lo lc P'' G''
      (Hexec' : exec_star P' G' lo lc P'' G'') :
      exec_star (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc) P'' G''.

  Lemma exec_step' : forall P G t o c P' G' rd mops
    (Hexec : exec P G t o c P' G') lo lc P'' G''
    (Hexec' : exec_star P' G' lo lc P'' G'')
    (Hrd : rd = opt_to_list o ++ lo)
    (Hmops : mops = opt_to_list c ++ lc),
    exec_star (Some P) G rd mops P'' G''.
  Proof.
    clarify; eapply exec_step; eauto.
  Qed.

  Lemma exec_star_trans : forall P G P' S G' G'' e1 m1 e2 m2,
    exec_star (Some P) G e1 m1 (Some P') G' ->
    exec_star (Some P') G' e2 m2 S G''->
    exec_star (Some P) G (e1++e2) (m1++m2) S G''.
  Proof.
    intros ?????????? Hexec; induction Hexec; clarify.
    eapply exec_step'; eauto; clarsimp.
  Qed.

  Lemma exec_step_inv : forall P G t lo lc P' G' rd mops
    (Hexec : exec_star (Some P) G lo lc (Some P') G') o c P'' G''
    (Hexec' : exec P' G' t o c P'' G'')
    (Hrd : rd = lo ++ opt_to_list o)
    (Hmops : mops = lc ++ opt_to_list c),
    exec_star (Some P) G rd mops P'' G''.
  Proof.
    clarify; eapply exec_star_trans; eauto.
    eapply exec_step'; eauto.
    - apply exec_refl.
    - rewrite app_nil_r; auto.
    - rewrite app_nil_r; auto.
  Qed.

  Definition distinct (P : state) := NoDup (map fst P).

  Lemma distinct_init : forall P, distinct (init_state P).
  Proof.
    unfold init_state; clarify.
    constructor; clarify.
  Qed.

  (* up *)
  Lemma NoDup_app : forall A (l1 l2 : list A), NoDup (l1 ++ l2) <->
    NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> ~In x l2.
  Proof.
    induction l1; split; clarify.
    - inversion H; clarify.
      rewrite IHl1 in *; split; rewrite in_app in *; clarify.
      constructor; auto.
    - inversion H1; clarify.
      constructor.
      + rewrite in_app; intro; clarify.
        exploit H22; eauto.
      + rewrite IHl1; clarify.
  Qed.

  Lemma distinct_step : forall P (Hdistinct : distinct P) G t lo lc P' G'
    (Hstep : exec P G t lo lc (Some P') G'), distinct P'.
  Proof.
    unfold distinct; intros; inversion Hstep; clarify; rewrite map_app in *;
      clarify.
    rewrite NoDup_app in *; clarify.
    inversion Hdistinct21; clarify.
    rewrite in_app in Hnew; split.
    - constructor; clarify.
      + intro; clarify.
      + constructor; auto.
    - intros ? Hin; specialize (Hdistinct22 _ Hin); intro; clarify.
  Qed.

  Corollary distinct_steps : forall P G lo lc P' G'
    (Hdistinct : distinct P) (Hsteps : exec_star (Some P) G lo lc (Some P') G'),
    distinct P'.
  Proof.
    intros.
    remember (Some P) as S; remember (Some P') as S';
      generalize dependent P'; generalize dependent P; induction Hsteps;
      clarify.
    destruct P'.
    - exploit distinct_step; eauto.
    - inversion Hsteps; clarify.
  Qed.

  Definition final_state (P : option state) := match P with
    | Some ll => Forall (fun li => snd li = []) ll
    | None => True
    end.

  Context (ML : @Memory_Layout var nat _)
          (MM : @Memory_Model _ _ _ ML _ conc_op Base).

  Typeclasses eauto := 2.
  Definition result P lo lc := exists P' G',
    exec_star (Some (init_state P)) init_env lo lc P' G' /\
      (match P' with Some ll => Forall (fun li => snd li = []) ll
       | None => True end) /\ consistent lc.

End Semantics.

Notation Acq t x := (ARW t%nat (x, 0) 0 (S t)).
Notation Rel t x := (ARW t%nat (x, 0) (S t) 0).

(* Proper nested recursion (fold) for instr. *)
Fixpoint instr_rect' (P : instr -> Type) (Q : list instr -> Type)
  (f1 : forall a e, P (Assign a e))
  (f2 : forall a x, P (Load a x)) (f3 : forall x e, P (Store x e))
  (f4 : forall m, P (Lock m)) (f5 : forall m, P (Unlock m))
  (f6 : forall u, P (Wait u)) (f7 : forall e1 e2, P (Assert_le e1 e2))
  (f : forall u li, Q li -> P (Spawn u li)) (g : Q nil)
  (h : forall i li, P i -> Q li -> Q (i :: li)) (i : instr) :=
  match i as i0 return (P i0) with
    | Assign a e => f1 a e
    | Load a x => f2 a x
    | Store x e => f3 x e
    | Lock m => f4 m
    | Unlock m => f5 m
    | Spawn u li => f u li (list_rect Q g
        (fun u r => h u r (instr_rect' P Q f1 f2 f3 f4 f5 f6 f7 f g h u)) li)
    | Wait u => f6 u
    | Assert_le e1 e2 => f7 e1 e2
  end.

Notation instr_rect'' P Q base := (instr_rect' P Q
  (fun a e => base (Assign a e)) (fun a x => base (Load a x))
  (fun x e => base (Store x e)) (fun m => base (Lock m))
  (fun m => base (Unlock m)) (fun u => base (Wait u))
  (fun e1 e2 => base (Assert_le e1 e2))).

Notation instr_list_rect P Q f1 f2 g h := (list_rect Q g
  (fun u r => h u r (instr_rect'' P Q f1 f2 g h u))).

Definition instr_forall P i := instr_rect'' (fun _ => Prop) _ P
  (fun u li r => r) True (fun i li r1 r2 => r1 /\ r2) i.

Lemma instr_forall_list : forall P u li, instr_forall P (Spawn u li) <->
  Forall (instr_forall P) li.
Proof.
  unfold instr_forall; induction li; split; clarify.
  - constructor; auto.
    apply IHli; auto.
  - inversion H; clarify.
    apply IHli; auto.
Qed.

Definition state_forall P :=
  Forall (fun (e : tid * list instr) => Forall (instr_forall P) (snd e)).

Fixpoint instr_ind' (P : instr -> Prop) (Q : list instr -> Prop)
  (Hbase : forall i, match i with Spawn _ _ => True | _ => P i end)
  (IHi : forall u li (IHli : Q li), P (Spawn u li)) (Hnil : Q nil)
  (Hcons : forall i li (IHi : P i) (IHli : Q li), Q (i :: li)) i : P i :=
  match i as i0 return (P i0) with
    | Assign a e => Hbase (Assign a e)
    | Load a x => Hbase (Load a x)
    | Store x e => Hbase (Store x e)
    | Lock m => Hbase (Lock m)
    | Unlock m => Hbase (Unlock m)
    | Spawn u li => IHi u li (list_rect Q Hnil (fun u r => Hcons u r
        (instr_ind' P Q Hbase IHi Hnil Hcons u)) li)
    | Wait u => Hbase (Wait u)
    | Assert_le e1 e2 => Hbase (Assert_le e1 e2)
  end.

Lemma distinct_thread : forall P1 P2 t li P1' P2' li'
  (Hdistinct : distinct (P1 ++ (t, li) :: P2))
  (Heq : P1 ++ (t, li) :: P2 = P1' ++ (t, li') :: P2'),
  P1' = P1 /\ P2' = P2 /\ li' = li.
Proof.
  intros.
  generalize (NoDup_inj(x := t) (length (map fst P1)) (length (map fst P1'))
    Hdistinct); intro Heq'; use Heq'; [use Heq'|].
  - repeat rewrite map_length in Heq'.
    exploit app_eq_inv; eauto; clarify.
  - rewrite Heq, map_app; simpl.
    apply nth_error_split.
  - rewrite map_app; simpl.
    apply nth_error_split.
Qed.