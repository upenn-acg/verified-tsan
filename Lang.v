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

  Definition operation := @operation tid ptr lock.

  Inductive conc_op : Type :=
  | Read (t : tid) (x : ptr) (v : nat)
  | Write (t : tid) (x : ptr) (v : nat)
  | ARW (t : tid) (x : ptr) (v : nat) (v' : nat).

  Definition thread_of c :=
    match c with
    | Read t _ _ => t
    | Write t _ _ => t
    | ARW t _ _ _ => t
    end.

  Definition to_seq c :=
    match c with
    | Read _ x v => [MRead x v]
    | Write _ x v => [MWrite x v]
    | ARW _ x v v' => [MRead x v; MWrite x v']
    end.

  Definition loc_of c :=
    match c with
    | Read _ x _ => x
    | Write _ x _ => x
    | ARW _ x _ _ => x
    end.

  Definition synchronizes_with c1 c2 := loc_of c1 = loc_of c2 /\
    exists t x v v', c1 = ARW t x v v' \/ c2 = ARW t x v v'.

  Instance var_eq : EqDec_eq var. eq_dec_inst. Qed.
 
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

  Instance Base : @MM_base _ _ var_eq _ _ := { thread_of := thread_of;
    to_seq := to_seq; synchronizes_with := synchronizes_with;
    drop_b_reads := drop_b_reads }.
  Proof.
    - induction ops; clarify.
      rewrite filter_app; destruct a; clarify.
      + destruct x as (b', ?); unfold negb, beq; clarify.
        rewrite IHops; auto.
      + rewrite IHops; auto.
      + destruct x as (b', ?); unfold negb, beq; simpl; destruct (eq_dec b' b);
          clarify; rewrite IHops; auto.
    - destruct c; clarsimp.
      destruct i; clarsimp; omega.
  Defined.        

  Definition upd_env G (t : tid) (a : local) (v : nat) :=
    upd G t (upd (G t) a v).

  Inductive exec P G :
    option operation -> option conc_op -> option state -> env -> Prop :=
  | exec_assign P1 P2 t a e rest
      (Hassign : P = P1 ++ (t, Assign a e :: rest) :: P2) :
      exec P G None None
        (Some (P1 ++ (t, rest) :: P2)) (upd_env G t a (eval (G t) e))

  | exec_load P1 P2 t a x v rest
      (Hload : P = P1 ++ (t, Load a x :: rest) :: P2) :
      exec P G (Some (rd t x)) (Some (Read t x v))
        (Some (P1 ++ (t, rest) :: P2)) (upd_env G t a v)

  | exec_store P1 P2 t x e rest
      (Hstore : P = P1 ++ (t, Store x e :: rest) :: P2) :
      exec P G (Some (wr t x)) (Some (Write t x (eval (G t) e)))
        (Some (P1 ++ (t, rest) :: P2)) G

  | exec_lock P1 P2 t m rest
      (Hlock : P = P1 ++ (t, Lock m :: rest) :: P2) :
      exec P G (Some (acq t m)) (Some (ARW t (m, 0) 0 (S t)))
        (Some (P1 ++ (t, rest) :: P2)) G
  | exec_unlock P1 P2 t m rest
      (Hlock : P = P1 ++ (t, Unlock m :: rest) :: P2) :
      exec P G (Some (rel t m)) (Some (ARW t (m, 0) (S t) 0))
        (Some (P1 ++ (t, rest) :: P2)) G

  | exec_spawn P1 P2 t u li rest
      (Hspawn : P = P1 ++ (t, Spawn u li :: rest) :: P2) :
      exec P G (Some (fork t u)) None
           (Some (P1 ++ (t, rest) :: (u, li) :: P2)) G

  | exec_wait P1 P2 t u rest
      (Hwait : P = P1 ++ (t, Wait u :: rest) :: P2) (Hdone : In (u, []) P) :
      exec P G (Some (join t u)) None (Some (P1 ++ (t, rest) :: P2)) G

  | exec_assert_pass P1 P2 t e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hpass : eval (G t) e1 <= eval (G t) e2) :
      exec P G None None (Some (P1 ++ (t, rest) :: P2)) G

  | exec_assert_fail P1 P2 t e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hfail : ~eval (G t) e1 <= eval (G t) e2) :
      exec P G None None None G
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
  | exec_step P G o c P' G' (Hexec : exec P G o c P' G') lo lc P'' G''
      (Hexec' : exec_star P' G' lo lc P'' G'') :
      exec_star (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc) P'' G''.

  Set Printing All.
 
  Context (ML : Memory_Layout nat var_eq) (MM : @Memory_Model _ _ _ ML _ conc_op Base).

  Definition result P lo lc := exists P' G',
    exec_star (Some (init_state P)) init_env lo lc P' G' /\
      (match P' with Some ll => Forall (fun li => snd li = []) ll
       | None => True end) /\ consistent lc.

End Semantics.
