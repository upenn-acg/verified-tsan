Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import FunctionalExtensionality.
Require Import HBRaceDetector.
Set Implicit Arguments.

Section Sim_Proofs.

Context (ML : @Memory_Layout var nat _).

Context (meta : metadata).

Hypothesis Hmetalocs_disjoint: forall t l x y z, 
  (t<zt -> x< zv -> C+t <> X+x )/\ 
  (z<zv -> x< zv -> R+z <> X+x )/\ 
  (y<zv -> x< zv -> W + y<> X+x) /\ 
  (l<zl -> x< zv -> L+l <> X+x )/\
  (l<zl -> t< zt -> C+t <> L+l ).

Notation C' := C.
Notation L' := L.
Notation R' := R.
Notation W' := W.
Notation X' := X.

Hypothesis Hs_x : forall (x0 : nat) m ,
         x0 < zv -> can_read m (X + x0, 0) 0 /\ can_write m (X + x0, 0).


Hypothesis Hmetalocs_disjoint_CX: forall t x, (t < zt -> x < zv -> C' + t <> X' + x).
Hypothesis Hmetalocs_disjoint_RX: forall z x,   (z < zv -> x < zv -> R' + z <> X' + x).
Hypothesis Hmetalocs_disjoint_CR: forall t x, (t < zt -> x < zv -> C' + t <> R' + x).
Hypothesis Hmetalocs_disjoint_CW: forall t x, (t < zt -> x < zv -> C' + t <> W' +x ).
Hypothesis Hmetalocs_disjoint_LR: forall l x, (l < zl -> x < zv -> L' +l  <> R' + x).
Hypothesis Hmetalocs_disjoint_LW: forall l x, (l < zl -> x < zv -> L' + l <> W' + x).
Hypothesis Hmetalocs_disjoint_WX: forall y x,  (y < zv -> x < zv -> W' + y <> X' + x).
Hypothesis Hmetalocs_disjoint_WR: forall y x, (y < zv -> x < zv -> W' + y <> R' + x).
Hypothesis Hmetalocs_disjoint_LX: forall l x,  (l < zl -> x < zv -> L' + l <> X' + x).
Hypothesis Hmetalocs_disjoint_CL: forall l t,  (l < zl -> t < zt -> C' + t <> L' + l).

Hint Resolve Htmp.
Hint Resolve Hnonoverlap.

Lemma can_read_thread' : forall m p v t,   consistent (m ++ [Read t p v]) ->
     can_read m p v .
Proof.
  unfold can_read, consistent, SC; setoid_rewrite lower_app; clarify.
Qed.

Lemma write_any_SC: forall t v m p
 (Hcon: consistent (m++[Write t p v ])),  can_write m p. 
Proof.
  intros. 
  unfold can_write, consistent, SC in *.  intros. rewrite lower_app in *. 
  rewrite lower_app in Hcon. rewrite lower_single in *. rewrite lower_single in Hcon.
  simpl. simpl in Hcon. rewrite write_any_value. eauto.
Qed.

  
Lemma acq_con: forall m t0 x 
 (Hcon: consistent m ) (Hx2: x < zv), consistent (m ++[Acq t0 (X+x)]).
Proof.
  intros.
  specialize(Hs_x m Hx2); inversion Hs_x; clarify;
  apply can_arw_SC; auto.
Qed.

Lemma clocks_sim_acq : forall m t0 x s
 (Hcon: consistent m) (Hx2: x < zv) (Hs: clocks_sim m s), clocks_sim (m ++ [Acq t0 (X+x)]) s.
Proof.
  intros.
  inversion Hs as [ Hs_c (Hs_l, Hs_rw)]; clarify.
  unfold clocks_sim. split;[|split;[|split]]; intros.
  exploit acq_con; eauto.
  intro Hacq_con.
  instantiate (1:=t0) in Hacq_con.
  -unfold clock_match. intros. 
   destruct (lt_dec t zt); clarify.
   specialize(Hs_c t H). unfold clock_match in Hs_c. specialize(Hs_c t1). 
   destruct (lt_dec t1 zt); clarify.
   split; auto.
   +apply can_read_SC; auto.
    { constructor; clarify. }
    { constructor; clarify.  specialize(Hmetalocs_disjoint_CX H Hx2). intro Heq. inversion Heq; clarify. }
    
   +apply can_write_SC; auto.
    { constructor; clarify. }
  -unfold clock_match. intros.
   destruct (lt_dec t zt); simpl.
   specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t).
   split; auto.
   +apply can_read_SC; clarify.
    apply acq_con; auto.
    { constructor; clarify. }
    { constructor; clarify. specialize(Hmetalocs_disjoint_LX H Hx2). intro Heq; inversion Heq; clarify. }
   +apply can_write_SC; clarify.
    apply acq_con; auto.
    constructor; clarify.
   +specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t). clarify.
  -unfold clock_match. intros; destruct (lt_dec t zt); clarify;
   specialize(Hs_rw v H); unfold clock_match in Hs_rw; inversion Hs_rw.
   +clarify. specialize(Hs_rw1 t). clarify. split; auto.
    *apply can_read_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
     { constructor; clarify. specialize(Hmetalocs_disjoint_RX H Hx2). intro Heq; inversion Heq; clarify. }
     
    *apply can_write_SC; auto.
     apply acq_con; auto.
     constructor; clarify.
   +specialize(H0 t). clarify.
  
   -unfold clock_match. intros; destruct (lt_dec t zt); clarify;
    specialize(Hs_rw v H); unfold clock_match in Hs_rw; inversion Hs_rw.
    +clarify. specialize(Hs_rw2 t). clarify. split; auto.
    *apply can_read_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
     { constructor; clarify. specialize(Hmetalocs_disjoint_WX H Hx2). intro Heq; inversion Heq; clarify. }
     
    *apply can_write_SC; auto.
     apply acq_con; auto.
     constructor; clarify.
   +specialize(H1 t). clarify.
Qed.

Hypothesis zt_non_zero : zt <> 0.

Lemma map_fst : forall (X Y: Type) l1 l2, Forall2 (fun (x y: X*Y) => fst x =fst y) l1 l2 -> map fst l1 = map fst l2.
Proof.
  intros A B l1.
  induction l1; clarify.
  -inversion H; clarify. 
  -destruct l2; clarify.
   +inversion H; clarify.
   +inversion H; clarify.
    specialize(IHl1 l2 H5). clarify.
    rewrite IHl1, H3.
    auto.
Qed.


Lemma in_mops_max_vc': forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_max_vc vc1 vc2 vs1 vs2 t n)),
  match c with 
  | Write tc p _ => fst p = vc2
  | Read tc p _  => fst p = vc1 \/ fst p = vc2
  | _ => False
  end.
Proof.
  induction n; intros; destruct vs1; clarify; destruct vs2; clarify.
  destruct c; clarify; exploit IHn; eauto.
Qed.

Lemma in_mops_max_vcn: forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_max_vc vc1 vc2 vs1 vs2 t n)),
  match c with 
  | Write tc (a,b) _ => a = vc2 /\ b < n
  | Read tc (a,b) _  => (a = vc1 \/ a = vc2) /\ b < n
  | _ => False
  end.
Proof.
  induction n; intros; destruct vs1; clarify; destruct vs2; clarify.
  destruct c; clarify; exploit IHn; eauto; destruct x; clarify.
Qed.

Check mops_max_vc_con_cc.
Lemma mops_inc_vc'_con : forall m ops u t v
  (Hu: u < zt) (Ht: t < zt) (Hprog: Forall prog_op ops)
  (Hcan_read: can_read (m++ops) (C'+u,u) v ) (Hcan_write: can_write m (C'+u, u)),
                           consistent (m ++ ops++ mops_inc_vc' (C' + u) v t u).
Proof.
  clarify.
  unfold mops_inc_vc'.
  rewrite split_app, app_assoc. apply can_write_thread. apply can_write_SC; clarify.
  -rewrite app_assoc. apply can_read_thread; auto. 
  -rewrite Forall_app; split; clarify.
   rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
Qed.   


Definition initialized m p :=
  exists v, last_op (lower(MM_base := Base) m) (Ptr p) (MWrite p v).

Definition in_range_dec i a b : {a <= i < b} + {~a <= i < b}.
Proof.
  destruct (le_dec a i); [|right; omega].
  destruct (lt_dec i b); [left; auto | right; omega].
Qed.

Definition meta_loc_dec x : {meta_loc x} + {~meta_loc x}.
Proof.
  unfold meta_loc.
  destruct (in_range_dec (fst x) C (C + zt)); [left; auto|].
  destruct (in_range_dec (fst x) L (L + zl)); [left; auto|].
  destruct (in_range_dec (fst x) R (R + zv)); [left; auto|].
  destruct (in_range_dec (fst x) W (W + zv)); [left; auto|].
  destruct (in_range_dec (fst x) X (X + zv)); [left; auto|].
  right; intro; clarify.
Qed.


Definition mem_sim' (m1 m2 : list conc_op) :=
  filter (fun c => if meta_loc_dec (loc_of c) then false else true) m2 = m1.




Definition bounded V z := forall t, ~t < z -> V t = 0.

Lemma clock_match_bounded : forall m V x, clock_match m V x -> bounded V zt.
Proof.
  unfold clock_match, bounded; intros.
  specialize (H t); clarify.
Qed.




Lemma bounded_le_dec : forall z V V', bounded V z -> vc_le V V' \/
  exists t, t < z /\ V t > V' t /\ forall t', t < t' -> V t' <= V' t'.
Proof.
  induction z; intros.
  - left; intro; rewrite H; omega.
  - destruct (le_dec (V z) (V' z)).
    specialize (IHz (upd V z 0) V'); use IHz.
    destruct IHz as [IHz | IHz]; [left | right].
    + intro t; unfold upd in IHz; specialize (IHz t); clarify.
    + unfold upd in IHz; destruct IHz as (t & ? & IHz); exists t.
      destruct (eq_dec z t); [exfalso; omega | clarify].
      specialize (IHz2 t'); clarify.
    + repeat intro; specialize (H t); unfold upd; clarify; omega.
    + right; exists z; split; [omega | split; [omega | clarify]].
      specialize (H t'); omega.
Qed.

Lemma first_gt_spec : forall vs1 vs2 v1 v2, first_gt vs1 vs2 = Some (v1, v2)
  <-> v1 > v2 /\
    exists i, nth_error vs1 i = Some v1 /\ nth_error vs2 i = Some v2 /\
    forall j v1' v2', j < i -> nth_error vs1 j = Some v1' ->
      nth_error vs2 j = Some v2' -> v1' <= v2'.
Proof.
  induction vs1; clarify.
  { split; clarsimp. }
  destruct vs2; clarify.
  { split; clarsimp. }
  destruct (a <=? n) eqn: Hle.
  - rewrite leb_le in Hle.
    rewrite IHvs1; split; clarify.
    + exists (S x); clarify.
      destruct j; clarify.
      exploit lt_S_n; eauto.
    + destruct x; clarify; try omega.
      exists x; clarify.
      specialize (H222 (S j)); clarify.
  - assert (~a <= n) by (intro; rewrite <- leb_le in *; clarify).
    split; clarify.
    + split; [omega|].
      exists 0; clarify; omega.
    + destruct x; clarify.
      specialize (H0222 0); clarify.
      exploit H0222; auto; omega.
Qed.

Definition mods_loc i x :=
  match i with
  | Store y _ => y = x
  | Lock y => x = (y, 0)
  | Unlock y => x = (y, 0)
  | _ => False
  end.

(*if a prog step does not modify x, then we could read the same value of x*)
Lemma can_read_step : forall P P1 P2 t i rest x v (Hdistinct : distinct P)
  (HP : P = P1 ++ (t, i :: rest) :: P2) (Hnot_mods : ~mods_loc i x) m
  G o c P' G' (Hstep : exec P G t o c P' G')
  (Hcon : consistent (m ++ opt_to_list c)),
  can_read (m ++ opt_to_list c) x v <-> can_read m x v.
Proof.
  intros.
  inversion Hstep; clarify; exploit distinct_thread; eauto; clarify;
    try (rewrite app_nil_r; reflexivity).
  - unfold can_read; rewrite <- app_assoc; apply read_noop_SC; auto.
  - unfold can_read; rewrite <- app_assoc; simpl.
    rewrite loc_valid_SC; auto; split; clarify.
  - unfold can_read; rewrite <- app_assoc; simpl.
    rewrite loc_valid_SC; auto; split; clarify.
  - unfold can_read; rewrite <- app_assoc; simpl.
    rewrite loc_valid_SC; auto; split; clarify.
Qed.

Lemma exec_other_thread : forall P t li (Hin : In (t, li) P) t' (Ht' : t' <> t)
  G o c P' G' (Hstep : exec P G t' o c (Some P') G'), In (t, li) P'.
Proof.
  intros; inversion Hstep; clarify; rewrite in_app in *; clarify.
Qed.

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

Definition instr_result t i G v :=
  match i with
  | Assign a e => Some (None, None, None, Some (a, eval G e),
      fun (P : state) => True)
  | Load a x => Some (None, Some (rd t (fst x)), Some (Read t x v), Some (a, v),
      fun P => True)
  | Store x e => Some (None, Some (wr t (fst x)), Some (Write t x (eval G e)),
      None, fun P => True)
  | Lock m => Some (None, Some (acq t m), Some (Acq t m), None, fun P => True)
  | Unlock m => Some (None, Some (rel t m), Some (Rel t m), None, fun P => True)
  | Spawn u li => Some (Some (u, li), Some (fork t u), None, None,
      fun P => ~In u (map fst P))
  | Wait u => Some (None, Some (join t u), None, None, fun P => In (u, []) P)
  | Assert_le e1 e2 => if le_dec (eval G e1) (eval G e2) then
      Some (None, None, None, None, fun P => True) else None
  end.

Lemma upd_triv1 : forall (G : env) t, upd G t (G t) = G.
Proof.
  intros; extensionality x; apply VectorClocks.upd_triv.
Qed.

Lemma exec_result : forall P G t o c P' G'
  (Hexec : exec P G t o c P' G'),
  exists P1 i li P2 v, P = P1 ++ (t, i :: li) :: P2 /\
    match instr_result t i (G t) v with
    | Some (th, o1, c1, u1, f) => G' = match u1 with Some (a, v) =>
        upd_env G t a v | None => G end /\ o1 = o /\ c1 = c /\
        P' = Some (P1 ++ (t, li) :: opt_to_list th ++ P2) /\ f P
    | None => G' = G /\ P' = None
    end.
Proof.
  intros; inversion Hexec; clarify; do 4 eexists; try (exists v);
    try (exists 0); repeat eexists; eauto; clarify.
Qed.

Hint Constructors exec.

Lemma result_exec : forall P P1 t i li P2 G v
  (HP : P = P1 ++ (t, i :: li) :: P2),
  match instr_result t i (G t) v with
  | Some (th, o, c, u1, f) => f P -> exec P G t o c
      (Some (P1 ++ (t, li) :: opt_to_list th ++ P2))
      (match u1 with Some (a, v) => upd_env G t a v | None => G end)
  | None => exec P G t None None None G
  end.
Proof.
  destruct i; clarify.
  destruct (le_dec (eval (G t) e1) (eval (G t) e2)); eauto.
Qed.

Lemma forall_step : forall P S (Hforall : state_forall P S)
  G t o c S' G' (Hstep : exec S G t o c (Some S') G'), state_forall P S'.
Proof.
  unfold state_forall; intros.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite Forall_app in *; clarify.
  inversion Hforall2 as [|?? Ha]; inversion Ha; constructor; clarify.
  rewrite Forall_app; clarify.
  destruct o0; clarify.
  destruct i; clarify.
  constructor; clarify.
  rewrite <- instr_forall_list; eauto.
Qed.

Corollary forall_steps : forall P S (Hforall : state_forall P S)
  G o c S' G' (Hsteps : exec_star (Some S) G o c (Some S') G'),
  state_forall P S'.
Proof.
  intros; remember (Some S) as P1; remember (Some S') as P2;
    generalize dependent S; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  apply (IHHsteps s); auto.
  eapply forall_step; eauto.
Qed.

Definition instr_size := instr_rect'' _ _ (fun _ => 1) (fun _ li r => S r)
  0 (fun _ _ r1 r2 => r1 + r2).



Fixpoint instr_list_size l :=
  match l with
  | [] => 0
  | i :: rest => instr_size i + instr_list_size rest
  end.

Lemma instr_list_size_app : forall l1 l2, instr_list_size (l1 ++ l2) =
  instr_list_size l1 + instr_list_size l2.
Proof.
  induction l1; clarify.
  rewrite IHl1; omega.
Qed.

Fixpoint size (P : state) :=
  match P with
  | [] => 0
  | (_, l) :: rest =>  instr_list_size l + size rest
  end.

Lemma size_app : forall P1 P2, size (P1 ++ P2) = size P1 + size P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; destruct a; omega.
Qed.

Lemma spawn_size : forall u li, instr_size (Spawn u li) =
  S (instr_list_size li).
Proof. induction li; clarify. Qed.

Lemma size_decr : forall P G t o c P' G' (Hstep : exec P G t o c (Some P') G'),
  size P' < size P.
Proof.
  intros; inversion Hstep; subst; repeat rewrite size_app; try (clarify; omega).
  unfold size at 4; fold size.
  unfold instr_list_size at 1; fold instr_list_size.
  rewrite spawn_size; simpl; omega.
Qed.

Lemma size_steps : forall P G o c P' G'
  (Hsteps : exec_star (Some P) G o c (Some P') G'), size P' <= size P.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit size_decr; eauto.
  specialize (IHHsteps _ eq_refl _ eq_refl); omega.
Qed.

Lemma iexec_decr : forall P G t o c P' G' (Hstep : iexec P G t o c P' G'),
  size P' < size P.
Proof.
  intros; inversion Hstep; subst; repeat rewrite size_app; clarify;
    repeat rewrite instr_list_size_app; try (clarify; omega).
  unfold instr_list_size at 4; fold instr_list_size.
  rewrite spawn_size; simpl; omega.
Qed.

Lemma iexec_step' : forall P G t lo lc P' G' rd mops
  (Hstep : iexec P G t lo lc P' G') lo' lc' P'' G''
  (Hsteps : iexec_star P' G' lo' lc' P'' G'')
  (Hrd : rd = lo ++ lo') (Hmops : mops = lc ++ lc'),
  iexec_star P G rd mops P'' G''.
Proof.
  clarify; eapply iexec_step; eauto.
Qed.

Lemma exec_next : forall P G t o c P' G' (Hexec : exec P G t o c P' G')
  (Hdistinct : distinct P) Pa Pb i li (Hin : P = Pa ++ (t, i :: li) :: Pb),
  exists v,
  match instr_result t i (G t) v with
  | Some (th, o1, c1, u1, f) => G' = match u1 with Some (a, v) =>
      upd_env G t a v | None => G end /\ o1 = o /\ c1 = c /\
      P' = Some (Pa ++ (t, li) :: opt_to_list th ++ Pb) /\ f P
  | None => G' = G /\ P' = None end.
Proof.
  intros; exploit exec_result; eauto; intros (? & i' & ? & ? & v & ?).
  clarify.
  exploit distinct_thread; eauto; clarify; eauto.
Qed.

Lemma distinct_in : forall P (Hdistinct : distinct P) t li1 li2
  (Hin1 : In (t, li1) P) (Hin2 : In (t, li2) P), li1 = li2.
Proof.
  intros.
  generalize (in_split _ _ Hin1), (in_split _ _ Hin2); clarify.
  exploit distinct_thread; eauto; clarify.
Qed.

Lemma step_thread : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G') (Hdistinct : distinct P)
  li (Ht : In (t, li) P),
  exists i li', li = i :: li' /\ In (t, li') P'.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify].
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  repeat eexists; eauto; rewrite in_app; clarify.
Qed.

Inductive exec_star_minus t : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_m P G : exec_star_minus t P G [] [] P G
| exec_step_m P G t' o c P' G' (Hin : t' <> t)
    (Hexec : exec P G t' o c P' G') lo lc P'' G''
    (Hexec' : exec_star_minus t P' G' lo lc P'' G'') :
    exec_star_minus t (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc)
                P'' G''.

Lemma NoDup_id_inj : forall A B l (x y : A * B) (Hids : NoDup (map fst l))
 (Hx : In x l) (Hy : In y l) (Heq : fst x = fst y), x = y.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  rewrite map_app in Hids; clarify.
  generalize (NoDup_remove_2 _ _ _ Hids); rewrite in_app in *; intro H.
  destruct Hx; clarify; contradiction H; repeat rewrite in_map_iff; eauto.
Qed.

Lemma cons_neq : forall A (x : A) l, x :: l <> l.
Proof.
  repeat intro.
  assert (length (x :: l) = length l) by (rewrite H; auto); clarify.
  exploit n_Sn; eauto.
Qed.

Lemma exec_mono : forall P G lo lc P' G' t (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  li (Hin : In (t, li) P) li' (Hin' : In (t, li') P'),
  exists n, li' = skipn n li.
Proof.
  intros ?????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  - generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    exists 0; auto.
  - destruct P'; [|inversion Hsteps; clarify].
    exploit distinct_step; eauto; intro.
    specialize (IHHsteps s); clarify.
    specialize (IHHsteps _ eq_refl).
    destruct (eq_dec t0 t); clarify.
    + exploit step_thread; eauto; clarify.
      specialize (IHHsteps _ H02 _ Hin'); destruct IHHsteps as [n ?].
      exists (S n); clarify.
    + exploit exec_other_thread; try apply Hexec; eauto.
Qed.

Lemma skip_cons_neq : forall A (x : A) l n, x :: l <> skipn n l.
Proof.
  repeat intro.
  assert (length (x :: l) = length (skipn n l)) by (rewrite H; auto).
  rewrite skipn_length in *; clarify; omega.
Qed.

Lemma exec_maintain : forall P G lo lc P' G' t li (Hdistinct : distinct P)
  (Hin : In (t, li) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exec_star_minus t (Some P) G lo lc (Some P') G'.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  - apply exec_refl_m.
  - destruct P'; [|inversion Hsteps; clarify].
    exploit distinct_step; eauto; intro.
    specialize (IHHsteps s); clarify.
    destruct (eq_dec t0 t); clarify.
    { exploit step_thread; eauto; clarify.
      exploit exec_mono; eauto; intros (n & Hmono).
      exploit skip_cons_neq; eauto; clarify. }
    exploit exec_other_thread; try apply Hexec; eauto; clarify.
    specialize (IHHsteps _ eq_refl); clarify.
    eapply exec_step_m; eauto.
Qed.      

Fixpoint t_steps P G t n lo lc P' G' :=
  match n with
  | 0 => lo = [] /\ lc = [] /\ P' = Some P /\ G' = G
  | S n' => exists o c P1 G1, exec P G t o c P1 G1 /\
      exists lo1 lc1 P2 G2 lo2 lc2, exec_star_minus t P1 G1 lo1 lc1 P2 G2 /\
      match P2 with
      | Some P2 => t_steps P2 G2 t n' lo2 lc2 P' G' /\
          lo = opt_to_list o ++ lo1 ++ lo2 /\ lc = opt_to_list c ++ lc1 ++ lc2
      | None => lo = opt_to_list o ++ lo1 /\ lc = opt_to_list c ++ lc1 /\
          P' = None /\ G' = G2 /\ n' = 0
      end
  end.

Lemma exec_minus_exec : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G'),
  exec_star P G lo lc P' G'.
Proof.
  intros; induction Hminus; clarify;
    [apply exec_refl | eapply exec_step; eauto].
Qed.

Lemma exec_other_threads : forall P t li (Hin : In (t, li) P)
  G o c P' G' (Hsteps : exec_star_minus t (Some P) G o c (Some P') G'),
  In (t, li) P'.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit exec_other_thread; eauto.
Qed.

Lemma t_steps_exec : forall t n P G lo lc P' G'
  (Ht_steps : t_steps P G t n lo lc P' G'),
  exec_star (Some P) G lo lc P' G'.
Proof.
  induction n; simpl; intros.
  - clarify; apply exec_refl.
  - destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2 &
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    + repeat rewrite app_assoc; eapply exec_star_trans; [|apply IHn; eauto].
      eapply exec_step; eauto.
      eapply exec_minus_exec; eauto.
    + eapply exec_step; eauto.
      eapply exec_minus_exec; eauto.
Qed.

Lemma t_steps_length : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G') li1 li2
  (Hin : In (t, li1 ++ li2) P) (Hin' : In (t, li2) P'), n = length li1.
Proof.
  induction n; simpl; intros.
  - clarify.
    generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    destruct li1; clarify.
    assert (length (i :: li1 ++ li2) = length li2) by (rewrite H1; auto).
    simpl in *; rewrite app_length in *; omega.
  - destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2 &
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    destruct P1; [|inversion Hminus; clarify].
    exploit distinct_step; eauto; intro Hdistinct1.
    exploit distinct_steps; eauto.
    { eapply exec_minus_exec; eauto. }
    intro Hdistinct'.
    specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1).
    exploit step_thread; eauto; clarify.
    destruct li1; clarify.
    { exploit exec_mono.
      { apply Hdistinct1. }
      { eapply exec_star_trans; [eapply exec_minus_exec | eapply t_steps_exec];
          eauto. }
      { eauto. }
      { eauto. }
      clarify; exploit skip_cons_neq; eauto; clarify. }
    erewrite IHn; eauto.
    eapply exec_other_threads; eauto.
Qed.

Lemma exec_step_inv_m : forall t P G lo lc P' G'
  (Hsteps : exec_star_minus t P G lo lc (Some P') G') o c P'' G'' t'
  (Hstep : exec P' G' t' o c P'' G'') (Hdiff : t' <> t),
  exec_star_minus t P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  intros ????????.
  remember (Some P') as S; generalize dependent P'; induction Hsteps; clarify.
  - generalize (exec_step_m Hdiff Hstep (exec_refl_m _ _ _)); clarsimp.
  - specialize (IHHsteps _ eq_refl _ _ _ _ _ Hstep Hdiff).
    repeat rewrite <- app_assoc; eapply exec_step_m; try apply Hexec; eauto.
Qed.

Lemma t_steps_add_t : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G')
  o c P'' G'' (Hexec : exec P' G' t o c P'' G''),
  t_steps P G t (S n) (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  induction n; simpl; intros.
  - clarify.
    repeat eexists; eauto.
    + apply exec_refl_m.
    + destruct P''; clarify; repeat rewrite app_nil_r; auto.
  - destruct Ht_steps as (o' & c' & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2
      & lc2 & Hminus & Hrest).
    do 5 eexists; eauto.
    do 7 eexists; eauto.
    destruct P2; clarify.
    destruct P1; [|inversion Hminus; clarify].
    generalize (distinct_step Hdistinct Htstep); intro.
    exploit distinct_steps; eauto.
    { eapply exec_minus_exec; eauto. }
    intro Hdistinct'.
    specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1 _ _ _ _ Hexec); clarify.
    split.
    + repeat eexists; eauto.
    + repeat rewrite <- app_assoc; auto.
Qed.

Lemma t_steps_add_other : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G')
  t' o c P'' G'' (Hexec : exec P' G' t' o c P'' G'') (Hdiff : t' <> t)
  (Hnz : n <> 0),
  t_steps P G t n (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  induction n; [clarify | simpl; intros].
  destruct Ht_steps as (o' & c' & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2
    & lc2 & Hminus & Hrest).
  destruct P2; clarify.
  destruct P1; [|inversion Hminus; clarify].
  generalize (distinct_step Hdistinct Htstep); intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro Hdistinct'.
  specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1 _ _ _ _ _ Hexec); clarify.
  do 5 eexists; eauto.
  destruct n.
  - clarify; do 7 eexists; [eapply exec_step_inv_m; eauto|].
    destruct P''; clarify; repeat rewrite app_nil_r;
      repeat rewrite <- app_assoc; auto.
  - do 7 eexists; eauto.
    split; [apply IHn; auto|].
    repeat rewrite <- app_assoc; auto.
Qed.

Lemma t_steps_extend : forall P' G' lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  P G t n lo0 lc0 (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo0 lc0 (Some P') G')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hlen : length li1 <> 0) (Hn : n <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (lo0 ++ lo) (lc0 ++ lc) (Some P'') G''.
Proof.
  intros ???????.
  remember (Some P') as S; remember (Some P'') as S'; generalize dependent P'';
    generalize dependent P'; induction Hsteps; clarify.
  { repeat rewrite app_nil_r; erewrite <- t_steps_length; eauto. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl).
  destruct (eq_dec t0 t); clarify.
  - exploit t_steps_add_t; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
  - exploit t_steps_add_other; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
Qed.

Corollary exec_thread : forall P G t o c P' G' (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G') lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hlen : length li1 <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (opt_to_list o ++ lo) (opt_to_list c ++ lc)
    (Some P'') G''.
Proof.
  intros; eapply t_steps_extend with (n := 1); eauto.
  simpl; repeat eexists; eauto.
  - apply exec_refl_m.
  - clarify; repeat rewrite app_nil_r; auto.
Qed.

(* up *)
Lemma NoDup_filter : forall A f (l : list A) (Hnodup : NoDup l),
  NoDup (filter f l).
Proof.
  induction l; clarify.
  inversion Hnodup; clarify.
  constructor; auto.
  rewrite filter_In; intro; clarify.
Qed.

Inductive exec_star_t t : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_t P G : exec_star_t t P G [] [] P G
| exec_step_t P G o c P' G' (Hexec : exec P G t o c P' G') lo lc P'' G''
    (Hexec' : exec_star_t t P' G' lo lc P'' G'') :
    exec_star_t t (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc)
                  P'' G''.

Lemma exec_minus_trans : forall t P G P' S G' G'' e1 m1 e2 m2,
  exec_star_minus t (Some P) G e1 m1 (Some P') G' ->
  exec_star_minus t (Some P') G' e2 m2 S G''->
  exec_star_minus t (Some P) G (e1++e2) (m1++m2) S G''.
Proof.
  intros ??????????? Hexec; induction Hexec; clarify.
  repeat rewrite <- app_assoc; eapply exec_step_m; eauto.
Qed.

Lemma exec_minus_env : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G'), G' t = G t.
Proof.
  intros; induction Hminus; auto.
  rewrite IHHminus.
  exploit exec_result; eauto; intros (? & i & li & ? & v & ?); clarify.
  destruct (instr_result t' i (G t') v) as [((((?, ?), ?), u1), ?)|];
    [destruct u1 as [(?, ?)|]|]; clarify.
  unfold upd_env, upd; clarify.
Qed.

Lemma upd_comm : forall (G : env) t t' Gt Gt' (Hdiff : t' <> t),
  upd (upd G t Gt) t' Gt' = upd (upd G t' Gt') t Gt.
Proof.
  intros; extensionality a; unfold upd; clarify.
Qed.

Notation upd_env' G t u := (match u with Some (a, v) => upd_env G t a v
  | None => G end).

Lemma result_env : forall t t' (Hdiff : t' <> t) u1 G,
  upd_env' G t u1 t' = G t'.
Proof.
  destruct u1 as [(?, ?)|]; unfold upd_env, upd; clarify.
Qed.

Lemma result_comm : forall G u1 u1' t t' (Hdiff : t' <> t),
  upd_env' (upd_env' G t u1) t' u1' = upd_env' (upd_env' G t' u1') t u1.
Proof.
  destruct u1 as [(?, ?)|], u1' as [(?, ?)|]; clarify.
  unfold upd_env; do 2 (rewrite VectorClocks.upd_old; auto).
  apply upd_comm; auto.
Qed.

Lemma exec_swap : forall t P G o c P' G' t' o' c' P'' G''
  (Hdiff : t' <> t) (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G')
  (Hstep' : exec P' G' t' o' c' (Some P'') G'')
  (Hspawn : forall li rest, ~In (t, Spawn t' li :: rest) P)
  (Hwait : forall i rest, In (t, [i]) P -> ~In (t', Wait t :: rest) P)
  (Hjoin : forall u rest rest', In (t, Spawn u [] :: rest) P ->
     ~In (t', Wait u :: rest') P),
  exists P1 G1, exec P G t' o' c' (Some P1) G1 /\
                exec P1 G1 t o c (Some P'') G''.
Proof.
  intros.
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_step; eauto; intro Hdistinct''.
  exploit exec_result; eauto; intros (P'a & i' & li' & P'b & v' & HP' & ?);
    clarify.
  destruct (instr_result t' i' (G' t') v') as [((((?, ?), ?), u1'), ?)|]
    eqn: Hresult'; clarify.
  exploit exec_result; [apply Hstep|]; intros (Pa & i & li & Pb & v & HP & ?);
    clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), u1), ?)|]
    eqn: Hresult; clarify.
  rewrite result_env in Hresult'; auto.
  assert (~In (t', i' :: li') (opt_to_list o1)) as Hout.
  { specialize (Hspawn (i' :: li') li); rewrite in_app in Hspawn; clarify.
    destruct o1; clarify.
    intro; destruct i; clarify. }
  assert (In (t', i' :: li') (Pa ++ (t, i :: li) :: Pb)).
  { assert (In (t', i' :: li') (P'a ++ (t', i' :: li') :: P'b)) as Hin
      by (rewrite in_app; clarify).
    rewrite H2 in Hin; rewrite in_app in *; clarify.
    rewrite in_app in *; destruct Hin; clarify. }
  exploit in_split; eauto; intros (P1a & P1b & HP').
  exploit (result_exec(P := Pa ++ (t, i :: li) :: Pb));
    [apply HP' | setoid_rewrite Hresult'; intro Hstep'1].
  use Hstep'1.
  do 3 eexists; eauto.
  assert (t <> t') as Hdiff' by auto.
  rewrite <- (result_env Hdiff' u1') in Hresult; auto.
  exploit exec_other_thread; try apply Hstep'1.
  { rewrite in_app; clarify. }
  { auto. }
  intro; exploit in_split; eauto; intros (P1'a & P1'b & HP1').
  exploit result_exec; [apply HP1' | setoid_rewrite Hresult; intro Hstep1].
  assert (~In (t, i :: li) (opt_to_list o0)) as Hout'.
  { destruct o0; clarify.
    intro; destruct i'; clarify.
    contradiction H2222.
    assert (In (t, li) (P'a ++ (t', Spawn t (i :: li) :: li') :: P'b)) as Hin
      by (rewrite H2, in_app; clarify).
    rewrite in_map_iff; setoid_rewrite in_app; rewrite in_app in Hin;
      destruct Hin; clarify.
    - do 2 eexists; [|left; eauto]; auto.
    - do 2 eexists; [|right; right; eauto]; auto. }
  assert (P'a ++ (t', li') :: opt_to_list o0 ++ P'b =
    P1'a ++ (t, li) :: opt_to_list o1 ++ P1'b) as Heq.
  { clear - H2 HP' HP1' Hdiff Hdistinct Hdistinct'' Hout Hout'.
    destruct (le_dec (length P1a) (length P1'a)).
    - exploit app_eq_inv_ge; eauto; intros (l1' & ?); clarify; clear HP1' l.
      destruct l1'; clarify.
      assert (length (opt_to_list o0) <= length l1').
      { destruct o0; clarify.
        destruct l1'; clarify; [|omega].
        contradiction Hout'; auto. }
      exploit app_eq_inv_ge; eauto; clarify.
      exploit NoDup_inj.
      { eauto. }
      { rewrite map_app; apply nth_error_split. }
      { rewrite HP', map_app, nth_error_plus; instantiate (1 := S _); simpl.
        rewrite map_app; apply nth_error_split. }
      rewrite (split_app P1a), app_assoc in HP'; intro.
      exploit app_eq_inv; try apply HP'; clarsimp.
      destruct (le_dec (length P'a) (length P1a)).
      + exploit app_eq_inv_ge; eauto; intros (l' & ?); clarify;
          clear H2 l.
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega.
      + symmetry in H2; exploit app_eq_inv_ge; eauto; [omega |
          intros (l' & ?); clarify; clear H2 n].
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega.
    - symmetry in HP1'; exploit app_eq_inv_ge; eauto; [omega |
        intros (l1' & ?); clarify; clear HP1' n].
      destruct l1'; clarify.
      rewrite <- app_assoc in HP'.
      exploit NoDup_inj.
      { eauto. }
      { rewrite map_app; apply nth_error_split. }
      { rewrite HP', map_app; apply nth_error_split. }
      repeat rewrite map_length; intro; exploit app_eq_inv; eauto; clarify.
      rewrite (split_app P1'a), app_assoc, app_assoc in H2.
      destruct (le_dec (length P'a)
        (length (((P1'a ++ [(t, li)]) ++ opt_to_list o1) ++ l1'))).
      + exploit app_eq_inv_ge; eauto; intros (l' & ?); clarify.
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite app_assoc, map_app; apply nth_error_split. }
        omega.
      + symmetry in H2; exploit app_eq_inv_ge; eauto; [omega |
          intros (l' & ?); clarify; clear H2 n].
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app, nth_error_plus; instantiate (2 := S _); simpl.
          rewrite app_assoc, map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite app_assoc, map_app, nth_error_plus;
            instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega. }
  rewrite Heq, result_comm; auto; apply Hstep1.
  - destruct i; simpl in *; inversion Hresult; subst; auto.
    + intro Hin; contradiction H0.
      rewrite HP'; rewrite map_app, in_app.
      do 2 (rewrite map_app, in_app in Hin; clarify).
      destruct o0; clarify; destruct i'; clarify.
      contradiction H2222; rewrite H2, map_app, in_app; clarify.
    + rewrite HP', in_app in *; clarify.
      rewrite in_app; auto.
    + clarify.
  - destruct i'; simpl in *; inversion Hresult'; subst; auto.
    + intro Hin; contradiction H2222.
      rewrite H2; rewrite map_app, in_app in *; clarify.
      rewrite map_app, in_app; auto.
    + rewrite H2, in_app in H2222; rewrite in_app; clarify.
      rewrite in_app in H2222; destruct H2222; clarify.
      * specialize (Hwait i li'); rewrite in_app in Hwait; clarify.
      * destruct o1; clarify; destruct i; clarify.
        specialize (Hjoin t0 li li'); rewrite in_app in Hjoin; clarify.
    + clarify.
Qed.

Lemma exec_later_t : forall t P' G' lo lc P'' G''
  (Hrest : exec_star_minus t P' G' lo lc (Some P'') G'')
  P G o c (Htstep : exec P G t o c P' G') (Hdistinct : distinct P)
  (Hspawn : forall u li rest, ~In (t, Spawn u li :: rest) P)
  (Hlast : forall i, ~In (t, [i]) P),
  exists P1 G1, exec_star_minus t (Some P) G lo lc (Some P1) G1 /\
    exec P1 G1 t o c (Some P'') G''.
Proof.
  intros ????????.
  remember (Some P'') as S; generalize dependent P'';
    induction Hrest; clarify.
  { do 3 eexists; eauto; apply exec_refl_m. }
  specialize (IHHrest _ eq_refl).
  destruct P'; clarify; [|inversion Hrest; clarify].
  exploit exec_swap; eauto.
  { intros; exploit Hlast; eauto. }
  { intros; exploit Hspawn; eauto. }
  intros (P1 & G1 & Ht' & Ht).
  exploit distinct_step; eauto; intro Hdistinct1.
  specialize (IHHrest _ _ _ _ Ht Hdistinct1).
  assert (exists li, In (t, li) P0) as (li & ?).
  { generalize (exec_result Htstep); clarify.
    eexists; rewrite in_app; clarify. }
  exploit exec_other_thread; eauto; intro.
  use IHHrest.
  use IHHrest.
  clarify; repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - intro Hin1; generalize (NoDup_id_inj _ _ (t, li) Hdistinct1 Hin1); clarify.
    exploit Hlast; eauto.
  - intro Hin1; generalize (NoDup_id_inj _ _ (t, li) Hdistinct1 Hin1); clarify.
    exploit Hspawn; eauto.
Qed.

Lemma exec_sooner_t : forall t P G lo lc P' G'
  (Hrest : exec_star_minus t (Some P) G lo lc (Some P') G')
  P'' G'' o c (Htstep : exec P' G' t o c (Some P'') G'')
  (Hdistinct : distinct P)
  (Hwait : forall u rest, ~In (t, Wait u :: rest) P)
  li (Ht_start : In (t, li) P),
  exists P1 G1, exec P G t o c P1 G1 /\
    exec_star_minus t P1 G1 lo lc (Some P'') G''.
Proof.
  intros ????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hrest; clarify.
  { do 3 eexists; eauto; apply exec_refl_m. }
  destruct P'; clarify; [|inversion Hrest; clarify].
  specialize (IHHrest _ eq_refl _ eq_refl).
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit exec_other_thread; eauto; intro Ht_start'.
  specialize (IHHrest _ _ _ _ Htstep Hdistinct').
  use IHHrest.
  specialize (IHHrest _ Ht_start').
  destruct IHHrest as (P1 & G1 & Htstep' & Hrest').
  destruct P1; clarify; [|inversion Hrest'; clarify].
  assert (t <> t') by auto.
  exploit exec_swap; try (apply Hdistinct); eauto.
  { intros ?? Hspawn.
    generalize (exec_result Hexec); intros (P1 & i' & li' & Hresult); clarify.
    generalize (NoDup_id_inj _ _ (t', i' :: li') Hdistinct Hspawn);
      rewrite in_app; clarify.
    contradiction Hresult22222; rewrite in_map_iff; exists (t, li); auto. }
  clarify; repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - intro Hin'; generalize (NoDup_id_inj _ _ (t, li) Hdistinct' Hin'); clarify.
    exploit Hwait; eauto.
Qed.


Lemma exec_t_exec : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc P' G'),
  exec_star P G lo lc P' G'.
Proof.
  intros; induction Hsteps; clarify;
    [apply exec_refl | eapply exec_step; eauto].
Qed.

Lemma exec_step_inv_t : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc (Some P') G') o c P'' G''
  (Hstep : exec P' G' t o c P'' G''),
  exec_star_t t P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  intros ????????.
  remember (Some P') as S; generalize dependent P'; induction Hsteps; clarify.
  - generalize (exec_step_t Hstep (exec_refl_t _ _ _)); clarsimp.
  - specialize (IHHsteps _ eq_refl _ _ _ _ Hstep).
    repeat rewrite <- app_assoc; eapply exec_step_t; eauto.
Qed.

(* up *)
Lemma partition_filter : forall A f (l : list A),
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
  induction l; clarsimp.
Qed.

Lemma exec_minus_ops : forall t P G lo lc P' G'
  (Hsteps : exec_star_minus t P G lo lc P' G'),
  Forall (fun c => beq (thread_of c) t = false) lc.
Proof.
  intros; induction Hsteps; clarify.
  rewrite Forall_app; clarify.
  inversion Hexec; constructor; auto; unfold beq; clarify.
Qed.

Lemma t_steps_plus : forall t n1 n2 P G lo lc P' G'
  (Ht_steps : t_steps P G t (n1 + n2) lo lc (Some P') G'),
  exists lo1 lc1 P1 G1 lo2 lc2, t_steps P G t n1 lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t n2 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  induction n1; simpl; intros.
  - repeat eexists; auto.
  - destruct Ht_steps as (o & c & P1 & G1 & Hstep & lo1 & lc1 & P2 & G2 & lo2 & 
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    specialize (IHn1 _ _ _ _ _ _ _ Hrest1);
      destruct IHn1 as (lo1' & lc1' & P1' & G1' & lo2' & lc2' & Hsteps1 &
      Hsteps2 & ?); clarify.
    exists (opt_to_list o ++ lo1 ++ lo1'), (opt_to_list c ++ lc1 ++ lc1'),
      P1', G1', lo2', lc2'; clarsimp.
    repeat eexists; eauto; clarify.
Qed.

Lemma loc_split : forall t lc m1 m2 m3
  (Hcon : consistent (m1 ++ lc ++ m2 ++ m3))
  lct lcr (Hpart : partition (fun c => beq (thread_of c) t) lc = (lct, lcr))
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) m2 /\
     Forall (fun c' => loc_of c' <> loc_of c) lct) lcr)
  (Hlc : Forall prog_op lc) (Hm2 : Forall prog_op m2),
  consistent (m1 ++ lct ++ m2 ++ lcr ++ m3).
Proof.
  setoid_rewrite partition_filter.
  induction lc using rev_ind; clarify.
  repeat rewrite filter_app in *; clarify.
  rewrite Forall_app in *; clarify.
  inversion Hlc2; clear Hlc2; subst.
  destruct (beq (thread_of x) t) eqn: Ht; unfold beq in Ht; clarify.
  - specialize (IHlc m1 (x :: m2) m3); clarsimp.
    apply IHlc; auto.
    rewrite Forall_forall in *; intros ? Hin.
    specialize (Hindep1 _ Hin); rewrite Forall_app in *; clarify.
    inversion Hindep122; clarify.
  - inversion Hindep2; specialize (IHlc m1 m2 (x :: m3)); clarsimp.
    apply IHlc; auto.
    rewrite app_assoc, loc_comm_ops1_SC, <- app_assoc in H; auto.
Qed.

(* up *)
Lemma filter_negb_all : forall A f (l : list A)
  (Hall : Forall (fun x => f x = false) l),
  filter (fun x => negb (f x)) l = l.
Proof.
  intros; rewrite filter_all; auto.
  eapply Forall_impl; eauto 2; unfold negb; clarify.
Qed.

Lemma filter_negb_none : forall A f (l : list A)
  (Hall : Forall (fun x => f x = true) l),
  filter (fun x => negb (f x)) l = [].
Proof.
  intros; rewrite filter_none; auto.
  eapply Forall_impl; eauto 2; unfold negb; clarify.
Qed.

Lemma exec_ops : forall P G t o c P' G' (Hexec : exec P G t o c P' G'),
  Forall (fun x => beq (thread_of x) t = true) (opt_to_list c).
Proof.
  intros; inversion Hexec; constructor; auto; unfold beq; clarify.
Qed.

Fixpoint to_mem G t li vs :=
  match li with
  | [] => Some ([], G, vs)
  | i :: li =>
      match i with
      | Assign a e => to_mem (upd G a (eval G e)) t li vs
      | Load a x => match vs with [] => None | v :: vs =>
          match to_mem (upd G a v) t li vs with None => None
          | Some (lc, G, vs) => Some (Read t x v :: lc, G, vs) end end
      | Store x e => match to_mem G t li vs with None => None
          | Some (lc, G', vs) => Some (Write t x (eval G e) :: lc, G', vs) end
      | Lock m => match to_mem G t li vs with None => None
          | Some (lc, G, vs) => Some (Acq t m :: lc, G, vs) end
      | Unlock m => match to_mem G t li vs with None => None
          | Some (lc, G, vs) => Some (Rel t m :: lc, G, vs) end
      | _ => to_mem G t li vs
      end
  end.

Lemma app_nil_inv : forall A (l1 l2 : list A), l1 ++ l2 = l2 -> l1 = []. 
Proof.
  intros; assert (length (l1 ++ l2) = length l2) by (rewrite H; auto).
  rewrite app_length in *; destruct l1; clarify; omega.
Qed.

(* up!! *)
Lemma split_in : forall A (l1 l2 : list A) x, In x (l1 ++ x :: l2).
Proof. intros; rewrite in_app; clarify. Qed.

(* up? *)
Lemma eval_old1: forall G t a v e (Hfresh : expr_fresh a e),
  eval (upd_env G t a v t) e = eval (G t) e.
Proof.
  induction e; clarify.
  apply upd_old; auto.
Qed.

Lemma upd_other_comm : forall G t t' a a' v v' (Hdiff : t' <> t),
  upd_env (upd_env G t a v) t' a' v' = upd_env (upd_env G t' a' v') t a v.
Proof.
  intros; unfold upd_env.
  rewrite upd_comm; auto.
  do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

Lemma exec_mem : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li1 li2 (Hin : In (t, li1 ++ li2) P) (Hin' : In (t, li2) P'),
  exists vs lc' vs', to_mem (G t) t li1 vs = Some (lc', G' t, vs') /\
    filter (fun c => beq (thread_of c) t) lc = lc'.
Proof.
  intros until t; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; induction Hsteps; clarify.
  { exploit distinct_in; [eauto | apply Hin | apply Hin' | intro H].
    exploit app_nil_inv; eauto; clear H.
    exists [], [], []; clarify. }
  destruct P'0; [|inversion Hsteps].
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  destruct (instr_result t0 i (G t0) v) as [((((?, ?), ?), u), ?)|] eqn: Hi;
    clarify.
  destruct (eq_dec t0 t).
  - subst; exploit distinct_in; [eauto | apply split_in | eauto | clarify].
    exploit distinct_step; eauto; intro.
    destruct li1; clarify.
    { exploit exec_mono; eauto; [apply split_in|].
      clarify; exploit skip_cons_neq; eauto; contradiction. }
    exploit IHHsteps; try reflexivity; eauto.
    { apply split_in. }
    intros (vs & lc' & vs' & Hvs & Heq).
    destruct i0; clarify; try solve [do 3 eexists; setoid_rewrite Hvs; auto].
    + unfold upd_env in Hvs; rewrite upd_new in Hvs; eauto.
    + exists (v :: vs).
      unfold upd_env in Hvs; rewrite upd_new in Hvs; auto.
      do 2 eexists; setoid_rewrite Hvs; auto.
  - exploit exec_other_thread; try apply Hexec; eauto; intro.
    exploit distinct_step; eauto; intro.
    exploit IHHsteps; eauto; intros (? & ? & ? & Hvs & ?).
    exploit exec_ops; eauto; intro Hops.
    rewrite filter_app, filter_none.
    destruct u as [(?, ?)|]; eauto.
    unfold upd_env in Hvs; rewrite VectorClocks.upd_old in Hvs; eauto.
    { eapply Forall_impl; eauto 2; unfold beq; clarify. }
Qed.             

Lemma t_steps_None : forall t n P G lo lc G'
  (Hsteps : t_steps P G t n lo lc None G'),
  n > 0 /\ exists P1 G1 lo1 lc1 lo2 lc2,
    t_steps P G t (n - 1) lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t 1 lo2 lc2 None G' /\ lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  induction n; simpl; intros.
  { clarify. }
  destruct Hsteps as (? & ? & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus1 &
    ?); clarify.
  destruct P2; clarify.
  - exploit IHn; eauto; intros (? & ? & ? & ? & ? & ? & ? & ? & ?).
    do 7 eexists.
    + destruct n; [omega | simpl].
      do 5 eexists; eauto.
      do 7 eexists; eauto; simpl in *.
      rewrite <- minus_n_O in *; eauto.
    + clarify.
      split; [repeat eexists; eauto|].
      repeat rewrite <- app_assoc; auto.
  - clear IHn.
    do 8 eexists; eauto; simpl; eauto.
    do 5 eexists; eauto.
    do 4 eexists; exists [], []; split; [eauto | clarify].
Qed.

Lemma exec_keep : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P), exists n, In (t, skipn n li) P'.
Proof.
  intros ????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  { exists 0; auto. }
  destruct P'; [|inversion Hsteps; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHsteps _ Hdistinct' eq_refl _ eq_refl).
  destruct (eq_dec t0 t); subst.
  - exploit step_thread; eauto; intros (? & ? & ? & Hin').
    specialize (IHHsteps _ _ Hin'); destruct IHHsteps as (n & ?); clarify.
    exists (S n); auto.
  - exploit exec_other_thread; eauto.
Qed.

Lemma cons_app_neq : forall A (x : A) l1 l2, x :: l1 ++ l2 <> l2.
Proof.
  repeat intro.
  assert (length (x :: l1 ++ l2) = length l2) by (rewrite H; auto).
  simpl in *; rewrite app_length in *; omega.
Qed.

Lemma step_instr : forall t i li P (Hin : In (t, i :: li) P)
  (Hdistinct : distinct P) G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  n (Hin' : In (t, skipn n li) P'),
  exists P1 G1 lo1 lc1 o c P1' G1' lo2 lc2,
    exec_star_minus t (Some P) G lo1 lc1 (Some P1) G1 /\
    exec P1 G1 t o c (Some P1') G1' /\
    exec_star (Some P1') G1' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros; remember (Some P) as P0; remember (Some P') as Pf;
    generalize dependent P'; generalize dependent P; induction Hsteps;
    clarify.
  - generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    exploit skip_cons_neq; eauto; clarify.
  - destruct P'; [|inversion Hsteps; clarify].
    destruct (eq_dec t0 t).
    + subst.
      repeat eexists; eauto.
      * apply exec_refl_m.
      * auto.
      * auto.
    + exploit exec_other_thread; try apply Hin; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit IHHsteps; eauto; clarify.
      repeat eexists; eauto.
      * eapply exec_step_m; eauto.
      * clarsimp.
      * clarsimp.
Qed.

Lemma to_mem_app : forall t li1 li2 G vs lc G' vs',
  to_mem G t (li1 ++ li2) vs = Some (lc, G', vs') <->
  match to_mem G t li1 vs with None => False
  | Some (lc1, G1, vs1) => match to_mem G1 t li2 vs1 with None => False
  | Some (lc2, G2, vs2) => lc = lc1 ++ lc2 /\ G' = G2 /\ vs' = vs2 end end.
Proof.
  induction li1; clarify.
  - destruct (to_mem G t li2 vs) as [((?, ?), ?)|]; split; clarify.
  - assert (forall c G1 vs1, match to_mem G1 t (li1 ++ li2) vs1 with
      | Some (lc0, G0, vs0) => Some (c :: lc0, G0, vs0)
      | None => None end = Some (lc, G', vs') <->
      match match to_mem G1 t li1 vs1 with
            | Some (lc0, G0, vs0) => Some (c :: lc0, G0, vs0)
            | None => None end with
      | Some (lc1, G1, vs1) =>
          match to_mem G1 t li2 vs1 with
          | Some (lc2, G2, vs2) => lc = lc1 ++ lc2 /\ G' = G2 /\ vs' = vs2
          | None => False end
      | None => False end).
    { intros.
      specialize (IHli1 li2 G1 vs1).
      destruct (to_mem G1 t li1 vs1) as [((?, ?), ?)|]; clarify.
      destruct (to_mem n t li2 l0) as [((?, ?), ?)|]; clarify.
      destruct (to_mem G1 t (li1 ++ li2) vs1) as [((?, ?), ?)|];
        clarify.
      * specialize (IHli1 l0 n l3); destruct IHli1; split; clarify.
      * specialize (IHli1 (l ++ l1) n0 l2); destruct IHli1; clarify.
      * split; clarify.
        destruct x as ((?, ?), ?); clarify.
        rewrite IHli1 in *; auto.
      * split; clarify.
        destruct x as ((?, ?), ?); clarify.
        rewrite IHli1 in *; auto. }
    destruct a; clarify.
    destruct vs; [split|]; clarify.
Qed.

Lemma t_steps_mem : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : t_steps P G t n lo lc P' G') li (Hin : In (t, li) P),
  exists vs vs', to_mem (G t) t (firstn n li) vs =
    Some (filter (fun c => beq (thread_of c) t) lc, G' t, vs').
Proof.
  induction n; intros.
  { exists [], []; clarify. }
  simpl in Hsteps.
  destruct Hsteps as (? & c & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus & ?);
    clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & ?); clarify.
  assert (li = i :: rest).
  { exploit distinct_in; [eauto | eauto | apply split_in | clarify]. }
  assert (match li with [] => [] | a :: l => a :: firstn n l end =
    [i] ++ firstn n rest) as Heq by clarify; subst; rewrite Heq.
  setoid_rewrite to_mem_app.
  assert (exists lcr, lc = opt_to_list c ++ lcr) as (lcr & ?).
  { destruct P2; clarify; eauto. }
  subst.
  assert (exists vs vs', to_mem match instr_result t i (G t) v with
    Some (_, _, _, u, _) => upd_env' G t u t | None => G t end t (firstn n rest)
    vs = Some (filter (fun c => beq (thread_of c) t) lcr, G' t, vs'))
    as (vs & vs' & Hm2).
  { exploit exec_minus_ops; eauto; intro Hops'.
    destruct P1; [|inversion Hminus]; clarify.
    - exploit distinct_step; eauto; intro.
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
      destruct P2; clarify.
      + exploit exec_other_threads; try apply Hminus; try apply split_in; intro.
        exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
        exploit IHn; eauto.
        intros (vs & vs' & Heq); exists vs, vs'.
        erewrite exec_minus_env in Heq; eauto.
        exploit app_inv_head; eauto; clarify.
        rewrite filter_app, (filter_none _ Hops'); auto.
      + exploit app_inv_head; eauto; clarify.        
        rewrite (filter_none _ Hops').
        rewrite (exec_minus_env Hminus); exists [], []; auto.
    - exploit app_inv_head; eauto; clarify.
      exists [], [].
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  }
  exists (match i with Load _ _ => v :: vs | _ => vs end), vs'; destruct i;
    clarify.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - inversion H; clarify.
Qed.


Lemma prog_step : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  Forall prog_op (opt_to_list c).
Proof.
  intros; inversion Hstep; clarify; constructor; simpl; auto.
Qed.

Lemma prog_steps : forall P G lo lc P' G' (Hsteps : exec_star P G lo lc P' G'),
  Forall prog_op lc.
Proof.
  intros; induction Hsteps; clarify.
  rewrite Forall_app; clarify; eapply prog_step; eauto.
Qed.

Lemma t_steps_indep : forall t li P G li2 lo lc P' G' (Hdistinct : distinct P)
  (Ht : In (t, li ++ li2) P)
  (Ht_steps : t_steps P G t (length li) lo lc (Some P') G')
  (Hwait : forall i u, nth_error li i = Some (Wait u) -> i = 0)
  m (Hcon : consistent (m ++ lc))
  lct lcr (Hpart : partition (fun c => beq (thread_of c) t) lc = (lct, lcr))
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lct) lcr),
  exists lot P1 G1 lor,
    exec_star_t t (Some P) G lot lct (Some P1) G1 /\ In (t, li2) P1 /\
    exec_star_minus t (Some P1) G1 lor lcr (Some P') G' /\
    consistent (m ++ lct ++ lcr).
Proof.
  induction li using rev_ind; simpl; intros.
  { clarify; repeat eexists; eauto.
    - apply exec_refl_t.
    - apply exec_refl_m. }
  rewrite app_length in Ht_steps; exploit t_steps_plus; eauto; clear Ht_steps.
  intros (lo1 & lc1 & P1 & G1 & lo2 & lc2 & Hsteps1 & Hsteps2 & ? & ?); subst.
  rewrite <- app_assoc in Ht; simpl in Ht.
  specialize (IHli _ _ _ _ _ _ _ Hdistinct Ht Hsteps1); use IHli.
  rewrite app_assoc in Hcon; specialize (IHli _ (consistent_app_SC _ _ Hcon)).
  rewrite partition_filter in *; specialize (IHli _ _ eq_refl); use IHli.
  destruct IHli as (lot & Pt & Gt & lor & Htsteps & HPt & Hminus & Hcon').
  simpl in Hsteps2.
  destruct Hsteps2 as (o & c & P2 & G2 & Hstep & lo3 & lc3 & [P3|] & G3 & lo4 &
    lc4 & Hminus2 & Hresult); clarify.
  repeat rewrite filter_app in *.
  destruct P2; [|inversion Hminus2; clarify].
  exploit distinct_steps; eauto.
  { eapply exec_t_exec; eauto. }
  intro Hdistinctt.
  generalize (exec_minus_ops Hminus2); intro Hall2.
  rewrite (filter_none _ Hall2), (filter_negb_all _ Hall2) in *.
  generalize (exec_ops Hstep); intro Hallt.
  rewrite (filter_all _ Hallt), (filter_negb_none _ Hallt) in *.
  destruct (nil_dec li); clarify.
  { repeat eexists.
    - eapply exec_step_t; [eauto | apply exec_refl_t].
    - exploit step_thread; eauto; clarify.
    - rewrite app_nil_r; eauto.
    - repeat rewrite app_nil_r in *; auto. }
  generalize (exec_sooner_t Hminus Hstep Hdistinctt); intro Hswap; use Hswap.
  specialize (Hswap _ HPt); destruct Hswap as (Pt' & Gt' & Hstep' & Hminus').
  destruct Pt'; [|inversion Hminus'; clarify].
  repeat eexists.
  - rewrite app_nil_r; eapply exec_step_inv_t; eauto.
  - exploit step_thread; eauto; clarify.
  - rewrite app_nil_r; eapply exec_minus_trans; eauto.
  - rewrite <- app_assoc, app_nil_r in *.
    rewrite app_nil_r; eapply loc_split; eauto.
    { rewrite partition_filter; auto. }
    rewrite Forall_app in *; clarify.
    eapply Forall_impl; eauto 2; clarify.
    rewrite Forall_app in *; clarify.
    { eapply prog_steps, t_steps_exec; eauto. }
    { eapply prog_step; eauto. }
  - intro Hin; generalize (NoDup_id_inj _ _ _ Hdistinctt HPt Hin); clarify.
    specialize (Hwait (length li) u); clarify.
    rewrite nth_error_split in Hwait; destruct li; clarify.
  - repeat rewrite filter_app in Hindep; rewrite Forall_app in Hindep; clarify.
    eapply Forall_impl; eauto 2; clarify.
    rewrite Forall_app in *; clarify.
  - exploit nth_error_lt; eauto.
    specialize (Hwait i u); rewrite nth_error_app in Hwait; clarify.
Qed.

Hint Rewrite nth_error_single : util.

Lemma hb_check_no_wait : forall C1 C2 z tmp1 tmp2 j u,
  nth_error (hb_check C1 C2 z tmp1 tmp2) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 3 (destruct j; clarify).
Qed.

Lemma max_vc_no_wait : forall src tgt z tmp1 tmp2 j u,
  nth_error (max_vc src tgt z tmp1 tmp2) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 4 (destruct j; clarify).
Qed.

Lemma max_vc_no_wait' : forall src tgt tgt' z tmp1 tmp2 j u t,
  nth_error (max_vc src tgt z tmp1 tmp2 ++ inc_vc t tgt' tmp1 ) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 4 (destruct j; clarify).
  do 4 (destruct j; clarify).
Qed.

Transparent move.

Lemma set_vc_no_wait : forall src tgt z tmp j u,
  nth_error (set_vc src tgt z tmp) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 2 (destruct j; clarify).
Qed.

Lemma instrument_wait : forall i t j u
  (Hnth : nth_error (instrument_instr i t) j = Some (Wait u)), j = 0.
Proof.
  destruct i; clarsimp.
  - destruct x.
    destruct j; clarify.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (hb_check (W + v) (C + t) zt tmp1 tmp2)));
      [exploit hb_check_no_wait; eauto; clarify|].
    destruct (j - length (hb_check (W + v) (C + t) zt tmp1 tmp2)); clarify.
    do 4 (destruct n1; clarify).
  - destruct x.
    destruct j; clarify.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (hb_check (W + v) (C + t) zt tmp1 tmp2)));
      [exploit hb_check_no_wait; eauto; clarify|].
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec (j - length (hb_check (W + v) (C + t) zt tmp1 tmp2))
                       (length (hb_check (R + v) (C + t) zt tmp1 tmp2)));
      [exploit hb_check_no_wait; eauto; clarify|].
    destruct (j - length (hb_check (W + v) (C + t) zt tmp1 tmp2) -
              length (hb_check (R + v) (C + t) zt tmp1 tmp2)); clarify.
    do 4 (destruct n2; clarify).
  - destruct j; clarify.
    exploit max_vc_no_wait; eauto; clarify.
  - unfold unlock_handler in Hnth.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (set_vc (C + t) (L + m) zt tmp1)));
      [exploit set_vc_no_wait; eauto; clarify|].
    destruct (j - length (set_vc (C + t) (L + m) zt tmp1)); clarify.
    do 4 (destruct n0; clarify).
  - unfold spawn_handler in Hnth.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (max_vc (C + t0) (C + t) zt tmp1 tmp2)));
      [exploit max_vc_no_wait; eauto; clarify|].
    destruct (j - length (max_vc (C + t0) (C + t) zt tmp1 tmp2)); clarify.
    do 4 (destruct n0; clarify).
  -unfold wait_handler in Hnth.
    destruct j; clarify.
    exploit max_vc_no_wait'; eauto; clarify.
Qed.

Lemma component_decr : forall P G o c P' G'
  (Hsteps : exec_star (Some P) G o c (Some P') G') (Hdistinct : distinct P)
  t li (Hin : In (t, li) P) li' (Hin' : In (t, li') P')
  (Hlt : length li' < length li), size P' < size P.
Proof.
  intros.
  inversion Hsteps; clarify.
  - exploit (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify; omega.
  - destruct P'0; [|inversion Hexec'; clarify].
    exploit size_decr; eauto; intro.
    generalize (size_steps Hexec'); omega.
Qed.

Lemma step_segment : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hfinal : final_state (Some P')) (Hdistinct : distinct P)
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hli1 : li1 <> []),
  exists P'' G'' lo1 lc1 Pt Gt o c lo2 lc2,
    exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    exec P'' G'' t o c (Some Pt) Gt /\ In (t, li2) Pt /\
    exec_star (Some Pt) Gt lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros ???????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  { rewrite Forall_forall in Hfinal; specialize (Hfinal _ Ht); clarify.
    destruct li1; clarify. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl); clarify.
  exploit distinct_step; eauto; clarify.
  destruct (eq_dec t0 t); subst.
  - exploit step_thread; eauto; clarify.
    destruct li1; clarify.
    destruct (nil_dec li1); clarify.
    + repeat eexists; eauto.
      { apply exec_refl. }
      { auto. }
      { auto. }
    + specialize (IHHsteps t li1 li2); clarify.
      repeat eexists; eauto.
      { eapply exec_step; eauto. }
      { rewrite <- app_assoc; auto. }
      { rewrite <- app_assoc; auto. }
  - exploit exec_other_thread; eauto; intro.
    specialize (IHHsteps t0 li1 li2); clarify.
    repeat eexists; eauto.
    { eapply exec_step; eauto. }
    { rewrite <- app_assoc; auto. }
    { rewrite <- app_assoc; auto. }
Qed.

Lemma instrument_single : forall i t i', instrument_instr i t = [i'] ->
  match i with Assign _ _ => True | Assert_le _ _ => True | _ => False end.
Proof.
  destruct i; clarify; try destruct x; destruct zt; clarify.
Qed.

Lemma Forall2_nth : forall A (l1 l2 : list A) P (Hforall : Forall2 P l1 l2)
  i x (Hi : nth_error l1 i = Some x),
  exists x', nth_error l2 i = Some x' /\ P x x'.
Proof.
  induction l1; clarsimp.
  inversion Hforall; clarify.
  destruct i; clarify; eauto.
Qed.

Lemma state_sim_inv : forall P1a P1b P2a P2b t li li'
  (Hsim : state_sim (P1a ++ (t, li) :: P1b) (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  state_sim P1a P2a /\ state_sim P1b P2b /\ li' = instrument li t.
Proof.
  induction P1a; clarify.
  - destruct P2a; clarify.
    + inversion Hsim; clarify; apply Forall2_refl.
    + inversion Hsim; clarify.
      generalize (NoDup_inj(x := fst p) 0 (S (length (map fst P2a))) Hdistinct);
        clarify.
      rewrite map_app in *; simpl in *; rewrite nth_error_split in *; clarify.
  - destruct P2a; clarify.
    + inversion Hsim; clarify.
      assert (nth_error (a :: P1a ++ (fst a, li) :: P1b) (S (length P1a)) =
        Some (fst a, li)) by (simpl; apply nth_error_split).
      exploit Forall2_nth; eauto; intros (? & Hnth & ?).
      generalize (NoDup_inj(x := fst a) 0 (S (length P1a)) Hdistinct);
        clarify.
      erewrite map_nth_error in *; eauto; clarify.
    + inversion Hsim; clarify.
      inversion Hdistinct; clarify.
      exploit IHP1a; eauto; clarify.
      constructor; auto.
Qed.

Lemma removelast_length : forall A (l : list A) (Hnnil : l <> []),
  length (removelast l) = length l - 1.
Proof.
  induction l; auto.
  intro; simpl.
  destruct (nil_dec l); clarify.
Qed.

Lemma removelast_nth : forall A (l : list A) i x,
  nth_error (removelast l) i = Some x <->
  nth_error l i = Some x /\ i < length l - 1.
Proof.
  intros; destruct (nil_dec l); clarify.
  { split; clarsimp. }
  rewrite (app_removelast_last x n) at 2; rewrite nth_error_app.
  rewrite removelast_length; auto.
  destruct (lt_dec i (length l - 1)); split; clarify.
  exploit nth_error_lt; eauto; rewrite removelast_length; clarify.
Qed.

Lemma beq_negb : forall A (A_eq : EqDec_eq A) B (a : A) (b c : B),
  (if negb (beq a a) then b else c) = c.
Proof.
  unfold negb, beq; clarify.
Qed.

Lemma t_steps_length' : forall t P' G' li1 P G lo lc (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t (length li1) lo lc (Some P') G')
  li2 (Hin : In (t, li1 ++ li2) P), In (t, li2) P'.
Proof.
  induction li1; [clarify | simpl; intros].
  destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & [P2|] & G2 & lo2 
    & lc2 & Hminus & Hrest); clarify.
  destruct P1; [|inversion Hminus; clarify].
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  exploit step_thread; eauto; clarify.
  eapply IHli1; eauto.
  eapply exec_other_threads; eauto.
Qed.

Opaque minus.

Lemma to_mem_suffix : forall t li G vs lc G' vs'
  (Hmem : to_mem G t li vs = Some (lc, G', vs')), exists vs1, vs = vs1 ++ vs'.
Proof.
  induction li; clarify.
  - exists []; auto.
  - destruct a; clarify; eauto.
    + destruct vs; clarify.
      destruct x0 as ((?, ?), ?); clarify.
      exploit IHli; eauto; clarify.
      setoid_rewrite <- list_cons_plus_assoc; eauto.
    + destruct x0 as ((?, ?), ?); clarify; eauto.
    + destruct x as ((?, ?), ?); clarify; eauto.
    + destruct x as ((?, ?), ?); clarify; eauto.
Qed.

Corollary to_mem_le : forall G t li vs lc G' vs'
  (Hmem : to_mem G t li vs = Some (lc, G', vs')), length vs' <= length vs.
Proof.
  intros; exploit to_mem_suffix; eauto; clarify; rewrite app_length; omega.
Qed.
Typeclasses eauto := 2.

(* up *)
Lemma read_last : forall (m : list mem_op) p v (Hm : seq_con ML m)
  (Hlast : last_op m (Ptr p) (MWrite p v)) v',
  seq_con ML (m ++ [MRead p v']) <-> v' = v.
Proof.
  split; intro; subst.
  - destruct Hlast as (i & ? & ?).
    symmetry; eapply read_last_val; eauto.
    + rewrite inth_nth_error; apply nth_error_split.
    + rewrite itake_firstn, firstn_app, firstn_length, minus_diag, app_nil_r;
        eauto.
    + rewrite inth_nth_error in *; exploit nth_error_lt; eauto;
        rewrite nth_error_app; clarify.
  - induction m using rev_ind.
    + generalize (last_nil Hlast); clarify.
    + generalize (consistent_app _ _ Hm); clarify.
      rewrite <- app_assoc.
      rewrite last_op_app in Hlast; destruct Hlast as [Hlast | [Hlast Hx]].
      * destruct Hlast as (i & ?); destruct i; clarsimp.
        apply read_written; auto.
      * inversion Hx; clarify.
        destruct H2.
        { destruct x; clarify.
          rewrite read_noop_single; auto. }
        { apply loc_valid; auto. }
Qed.

Lemma last_single : forall (a : @mem_op var nat) l a',
  last_op (icons a inil) l a' <->
  a' = a /\ ~independent (block_model.loc_of a) l /\ not_read a = true.
Proof.
  split; clarify.
  - destruct H as (? & Hlast & ?).
    destruct x; clarsimp.
    inversion Hlast; clarify.
  - exists 0; clarify.
    econstructor; simpl; eauto 2; clarify.
    destruct j; clarsimp.
Qed.

Instance ptr_dec : EqDec_eq ptr.
Proof. eq_dec_inst. Qed.

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

Lemma last_write : forall (m : list conc_op) p v,
  last_op (@lower _ _ _ _ _ Base m) (Ptr p) (MWrite p v) <->
  exists c, find (fun c => writesb c p) (rev m) = Some c /\
  write_val c = Some v.
Proof.
  induction m using rev_ind; clarify.
  { split; clarify.
    apply last_nil in H; contradiction. }
  rewrite rev_app_distr, lower_app, lower_single, last_op_app; simpl.
  destruct (writesb x p) eqn: Hx.
  - split; clarify.
    + do 2 eexists; eauto.
      destruct H; clarify.
      * destruct x; clarify; try rewrite last_single in H; clarify.
        { inversion H1; clarify. }
        { destruct H as (i & ? & Hi); destruct i; clarify.
          destruct i; clarify; rewrite inth_nil in Hi; inversion Hi. }
      * destruct x; clarify; unfold beq in *; inversion H2; clarsimp.
        { inversion H4; clarify. }
        { destruct p; clarify. }
        { destruct p; clarify. }
    + left; destruct x0; clarify; unfold beq in *; clarify.
      * rewrite last_single; clarify.
      * exists 1; clarify.
        econstructor; simpl; eauto; intros.
        destruct j; clarify.
        destruct j; clarify.
        rewrite inth_nil in H; inversion H.
  - etransitivity; eauto.
    split; clarify.
    + destruct x; clarify; unfold beq in *; clarify;
        try (rewrite last_single in H; clarify).
      destruct H as (i & ? & Hi); destruct i; clarify.
      destruct i; clarify; rewrite inth_nil in Hi; inversion Hi.
    + right; clarify.
      destruct x; clarify; unfold beq in *; constructor; clarify.
Qed.

Lemma init_read : forall m p (Hinit : initialized m p) (Hcon : consistent m) v,
  can_read m p v <-> exists c,
    find (fun c => writesb c p) (rev m) = Some c /\ write_val c = Some v.
Proof.
  unfold can_read; intros.
  destruct Hinit as (v' & Hlast).
  unfold consistent, SC; rewrite lower_app, lower_single; simpl.
  rewrite read_last; eauto.
  rewrite last_write in Hlast; clarify.
  split; clarsimp; eauto.
Qed.

Lemma can_read_unique : forall m p v v' (Hcon : consistent m)
  (Hinit : initialized m p) (Hv : can_read m p v) (Hv' : can_read m p v'),
  v' = v.
Proof.
  unfold can_read; intros.
  unfold consistent, SC, lower in *.
  rewrite map_app, flatten_app in *; clarify.
  destruct Hinit.
  rewrite read_last in Hv, Hv'; eauto; clarify.
Qed.

Lemma init_step : forall m p a (Hinit : initialized m p) (Hprog : prog_op a),
  initialized (m ++ [a]) p.
Proof.
  unfold initialized; clarify.
  rewrite lower_app, lower_single; destruct a; clarify.
  - exists x; rewrite last_op_app; right; clarify.
  - destruct (eq_dec x0 p).
    + subst; exists v; rewrite last_op_app; left.
      setoid_rewrite last_single; clarify.
    + exists x; rewrite last_op_app; right; clarify.
  - destruct (eq_dec x0 p).
    + subst; exists v'; rewrite last_op_app; left.
      exists 1; clarify.
      econstructor; simpl; eauto.
      destruct j; clarify.
      destruct j; clarsimp.
    + exists x; rewrite last_op_app; right; clarify.
Qed.

Lemma init_steps : forall m p s (Hinit : initialized m p) (Hprog : Forall prog_op s),
  initialized (m ++ s) p.
Proof.
  intros. generalize dependent m. induction s. 
  -intros. rewrite app_nil_r. auto.
  -intros. rewrite split_app. apply IHs.
   +rewrite Forall_forall in *. intros. clarify.
   +apply init_step; auto.
    eapply Forall_inv. eauto.
Qed.

Lemma hb_check_len : forall C1 C2 z tmp1 tmp2,
  length (hb_check C1 C2 z tmp1 tmp2) = 3 * z.
Proof.
  induction z; clarify.
  rewrite IHz; omega.
Qed.

Lemma max_vc_len : forall src tgt z tmp1 tmp2,
  length (max_vc src tgt z tmp1 tmp2) = 4 * z.
Proof.
  induction z; clarify.
  rewrite IHz; omega.
Qed.

Transparent move.

Lemma load_handler_len : forall t x z,
  length (load_handler t x z) = 3 * z + 3.
Proof.
  unfold load_handler; clarify.
  rewrite app_length, hb_check_len; simpl; omega.
Qed.

Lemma store_handler_len : forall t x z,
  length (store_handler t x z) = 6 * z + 3.
Proof.
  unfold store_handler; clarify.
  repeat rewrite app_length, hb_check_len; simpl; omega.
Qed.

Lemma lock_handler_len : forall t l z,
  length (lock_handler t l z) = 4 * z.
Proof.
  intros; apply max_vc_len.
Qed.

Lemma spawn_handler_len : forall t l z,
  length (spawn_handler t l z) = 4 * z + 3.
Proof.
  unfold spawn_handler; clarify.
  rewrite app_length, max_vc_len; simpl; omega.
Qed.

Lemma unlock_handler_len : forall t u z tmp,
  length (unlock_handler t u z tmp) = 2 * z + 3.
Proof.
  unfold unlock_handler; clarify.
  rewrite app_length, set_vc_len; simpl; omega.
Qed.

Lemma wait_handler_len : forall t u z,
  length (wait_handler t u z) = 4 * z+3 .
Proof.
  unfold wait_handler; clarify.
  rewrite app_length,  max_vc_len; simpl. omega.
Qed.

Lemma hb_check_locs : forall C1 C2 z vs1 vs2 t l,
  In l (map loc_of (mops_hb_check C1 C2 vs1 vs2 z t)) ->
    exists n, n < z /\ (l = (C1, n) \/ l = (C2, n)).
Proof.
  induction z; clarify; destruct vs1; clarify.
  destruct vs2; clarify.
  destruct H as [? | [? | ?]]; eauto.
  destruct (leb n n0); clarify.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Definition accesses i := match i with
| Load _ p => Some p
| Store p _ => Some p
| Lock m => Some (m, 0)
| Unlock m => Some (m, 0)
| _ => None
end.

Lemma exec_accesses : forall P G t (Hdistinct : distinct P) o c P' G'
  (Hexec : exec P G t o c P' G') i rest (Hi : In (t, i :: rest) P) l,
  (match c with Some c => loc_of c = l | None => False end) <->
  accesses i = Some l.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  inversion Hexec; exploit distinct_thread; eauto; clarify; split; clarify.
Qed.

Lemma hb_check_instr : forall C1 C2 z tmp1 tmp2 i
  (Hi : In i (hb_check C1 C2 z tmp1 tmp2)) l (Haccess : accesses i = Some l),
  exists n, n < z /\ (l = (C1, n) \/ l = (C2, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma max_vc_instr : forall src tgt z tmp1 tmp2 i
  (Hi : In i (max_vc src tgt z tmp1 tmp2)) l (Haccess : accesses i = Some l),
  exists n, n < z /\ (l = (src, n) \/ l = (tgt, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | [? | [? | ?]]]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma set_vc_instr : forall src tgt z tmp i
  (Hi : In i (set_vc src tgt z tmp)) l (Haccess : accesses i = Some l),
  exists n, n < z /\ (l = (src, n) \/ l = (tgt, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.

Lemma instrument_own : forall li (Hsafe : Forall safe_instr li)
  t i (Hi : In i (instrument li t)) t' (Ht' : t' < zt) n
  (Haccess : accesses i = Some (C' + t', n)), t' = t \/
  (exists i', In i' li /\ In i (instrument_instr i' t) /\
   match i' with Spawn u _ | Wait u => t' = u
   | _ => False end).
Proof.
  induction li; clarify.
  inversion Hsafe as [|?? Hsafe' ?]; clarify.
  rewrite in_app in Hi; destruct Hi.
  destruct a; try destruct x; clarify.
  - left.
    repeat rewrite in_app in H; simpl in H.
    destruct H as [H | [[H | H] | [H | H]]]; clarify.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CW; try apply Ht'; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + destruct H as [H | H]; clarify.
      * eapply plus_reg_l; eauto.
      * exploit Hmetalocs_disjoint_CR; eauto; contradiction.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
  - left.
    repeat rewrite in_app in H; simpl in H.
    destruct H as [H | [[H | [H | [H | H]]] | [H | H]]]; clarify.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CW; try apply Ht'; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CR; try apply Ht'; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + eapply plus_reg_l; eauto.
    + exploit Hmetalocs_disjoint_CW; eauto; contradiction.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
  - left; unfold lock_handler in H.
    destruct H; clarify.
    + contradiction Hsafe'1; left; simpl; omega.
    + exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CL; try (apply H4); eauto; clarify.
      * eapply plus_reg_l; eauto.
  - left; unfold unlock_handler in H; repeat rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    + exploit set_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * eapply plus_reg_l; eauto.
      * exploit Hmetalocs_disjoint_CL; try (apply H4); eauto; clarify.
    + destruct H as [? | [? | ?]]; clarify; eapply plus_reg_l; eauto.
    + contradiction Hsafe'1; left; simpl; omega.
  - unfold spawn_handler in H; repeat rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    +exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * left. eapply plus_reg_l; eauto.
      * right; eexists; split; eauto; simpl.
        split; [|eapply plus_reg_l; eauto].
        unfold spawn_handler; repeat rewrite in_app; auto.
    + left; destruct H as [? | [? | ?]]; clarify; eapply plus_reg_l; eauto.
   
  - unfold wait_handler in H; repeat rewrite in_app in H.
    destruct H as [? | ?]; clarify.
    +exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
     *right; eexists; split; eauto; clarify.
      split; clarify. right. unfold wait_handler. rewrite in_app. clarify.
      eapply plus_reg_l; eauto.
     *left; eapply plus_reg_l; eauto.
    + destruct H as [? | [? | [?|?]]]; clarify.
      * right; eexists; split; eauto; clarify.
        split; clarify. right. unfold wait_handler. rewrite in_app. clarify.
        apply plus_reg_l in H1. clarify.
      * right; eexists; split; eauto; clarify.
        split; clarify. right. unfold wait_handler. rewrite in_app. clarify.
        apply plus_reg_l in H1. clarify.
  - exploit IHli; eauto; clarify.
    right; eauto.
Qed.

(* up *)
Lemma skipn_in : forall A n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
  intros; exploit in_nth_error; eauto; clarify.
  rewrite skipn_nth in *; eapply nth_error_in; eauto.
Qed.

Inductive exec_star_rev : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_rev P G : exec_star_rev P G [] [] P G
| exec_step_rev P G lo lc P' G' (Hexec : exec_star_rev P G lo lc (Some P') G')
    t o c P'' G'' (Hexec' : exec P' G' t o c P'' G'') :
    exec_star_rev P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.

Lemma exec_rev_trans : forall P G P' S G' G'' e1 m1 e2 m2,
  exec_star_rev P G e1 m1 P' G' ->
  exec_star_rev P' G' e2 m2 S G'' ->
  exec_star_rev P G (e1++e2) (m1++m2) S G''.
Proof.
  intros ?????????? Hexec Hexec'; revert Hexec; induction Hexec'; clarify.
  - clarsimp.
  - repeat rewrite app_assoc; eapply exec_step_rev; eauto.
Qed.

Lemma exec_rev_some : forall P G lo lc P' G'
  (Hrev : exec_star_rev P G lo lc (Some P') G'), exists P0, P = Some P0.
Proof.
  intros; remember (Some P') as P1; generalize dependent P';
    induction Hrev; clarify; eauto.
Qed.

Lemma exec_rev : forall P G lo lc P' G',
  exec_star P G lo lc P' G' <-> exec_star_rev P G lo lc P' G'.
Proof.
  split; intros; induction H.
  - apply exec_refl_rev.
  - eapply exec_rev_trans; eauto.
    apply (exec_step_rev (exec_refl_rev _ _) Hexec).
  - apply exec_refl.
  - exploit exec_rev_some; eauto; clarify.
    eapply exec_step_inv; eauto.
Qed.

Lemma hb_check_instrs : forall C1 C2 z tmp1 tmp2 i,
  In i (hb_check C1 C2 z tmp1 tmp2) -> (exists n, n < z /\
    (i = Load tmp1 (C1, n) \/ i = Load tmp2 (C2, n))) \/
    i = Assert_le (V tmp1) (V tmp2).
Proof.
  induction z; clarify.
  destruct H as [? | [? | ?]]; [left | left |]; clarify; eauto.
  exploit IHz; eauto; intros [(x & ? & [? | ?]) | ?]; clarify; left;
    exists x; clarify.
Qed.  

Lemma max_vc_instrs : forall src tgt z tmp1 tmp2 i,
  In i (max_vc src tgt z tmp1 tmp2) -> (exists n, n < z /\
    (i = Load tmp1 (src, n) \/ i = Load tmp2 (tgt, n) \/
     i = Store (tgt, n) (V tmp2))) \/ i = Assign tmp2 (Max (V tmp1) (V tmp2)).
Proof.
  induction z; clarify.
  destruct H as [? | [? | [? | [? | ?]]]]; clarify;
    try solve [left; repeat eexists; [|clarify]; auto].
  exploit IHz; eauto; intros [(x & ? & [? | ?]) | ?]; clarify; left;
    exists x; clarify.
Qed.  

Lemma set_vc_instrs : forall src tgt z tmp i,
  In i (set_vc src tgt z tmp) -> exists n, n < z /\
    (i = Load tmp (src, n) \/ i = Store (tgt, n) (V tmp)).
Proof.
  induction z; clarify.
  destruct H as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; clarify; eauto.
Qed.

Lemma spawn_in_handler : forall u li i t,
  In (Spawn u li) (instrument_instr i t) -> exists li', i = Spawn u li' /\
    li = instrument li' u.
Proof.
  destruct i; clarify.
  - destruct x; clarify.
    repeat rewrite in_app in H; destruct H as [[? | ?] | ?]; clarify.
    exploit hb_check_instrs; eauto; clarify.
  - destruct x; clarify.
    repeat rewrite in_app in H; destruct H as [[? | [? | ?]] | ?]; clarify;
      exploit hb_check_instrs; eauto; clarify.
  - exploit max_vc_instrs; eauto; clarify.
  - repeat setoid_rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    exploit set_vc_instrs; eauto; clarify.
  - repeat setoid_rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    + exploit max_vc_instrs; eauto; clarify.
    + inversion H.
      do 2 eexists; eauto.
  -repeat setoid_rewrite in_app in H.
   destruct H as [?|?]; clarify.
   exploit max_vc_instrs; eauto; clarify.
Qed.

Lemma spawn_in_instrument : forall u li t l, In (Spawn u li) (instrument l t) ->
  exists li', In (Spawn u li') l /\ li = instrument li' u.
Proof.
  induction l; clarify.
  rewrite in_app in *; destruct H; clarify; eauto.
  exploit spawn_in_handler; eauto; clarify; eauto.
Qed.

Typeclasses eauto := 5.

Lemma safe_instrs : forall l, (fix list_safe l := match l with [] => True |
  i :: rest => safe_instr i /\ list_safe rest end) l <->
  Forall safe_instr l.
Proof.
  induction l; split; clarify; rewrite IHl in *; clarify.
  inversion H; clarify.
Qed.

Lemma spawn_instrumented : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P)
  G lo lc P' G' (Hsteps : exec_star (Some P1) G lo lc (Some P') G')
  t li (Ht : In (t, li) P') u li' (Hspawn : In (Spawn u li') li),
  exists li0, li' = instrument li0 u /\ Forall safe_instr li0.
Proof.
  intros ??????????; remember (Some P1) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P1.
  rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - generalize (in_split _ _ Ht); clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hsim2 & ?).
    inversion Hsim2; clarify.
    exploit spawn_in_instrument; eauto; clarify.
    setoid_rewrite Forall_app in Hsafe; clarify.
    inversion Hsafe2 as [|?? Hl]; clarify.
    rewrite Forall_forall in Hl; exploit Hl; eauto; clarify.
    rewrite safe_instrs in *; eauto.
  - exploit exec_result; eauto.
    intros (P'a & i1 & li1 & P'b & v & ? & Hresult); subst.
    destruct (instr_result t i1 (G' t) v)
      as [((((t', ?), ?), ?), ?)|] eqn: Hi1; clarify.
    rewrite in_app in Ht; clarify; rewrite in_app in Ht.
    specialize (IHHsteps _ Hsim eq_refl _ eq_refl).
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Ht as [? | [? | [? | ?]]]; eauto.
    { inversion H; subst; exploit IHHsteps; eauto; clarify. }
    destruct t'; clarify.
    destruct i1; clarify.
    exploit IHHsteps; clarify.
    exploit spawn_in_instrument; eauto; clarify.
    rewrite Forall_forall in H2; exploit H2; eauto; clarify.
    rewrite safe_instrs in *; eauto.
Qed.

Lemma instrument_nonnil : forall i t, instrument_instr i t <> [].
Proof.
  destruct i; repeat intro; clarify.
  - destruct x, zt; clarify.
  - destruct x, zt; clarify.
  - destruct zt; clarify.
  - destruct zt; clarify.
Qed.

Lemma step_into_instrument : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P)
  G1 lo lc P1' G1' (Hsteps : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t i li (Ht : In (t, i :: li) P1') (Hdistinct : distinct P1),
  exists P2 lo2 lc2 G2 n' i' li' rest lo2' lc2', lc = lc2 ++ lc2' /\
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G2 /\
    In (t, instrument_instr i' t ++ instrument rest t) P2 /\
    skipn n' (instrument_instr i' t) = i :: li' /\
    li = li' ++ instrument rest t /\ safe_instr i' /\ Forall safe_instr rest /\
    exec_star (Some P2) G2 lo2' lc2' (Some P1') G1'.
Proof.
  intros ???????????; remember (Some P1) as Pa; remember (Some P1') as Pb;
    generalize dependent P1'; generalize dependent P1.
  rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - exploit in_split; eauto; clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hsim2 & ?).
    inversion Hsim2 as [|(t', li')]; clarify.
    destruct li'; clarify.
    destruct (instrument_instr i0 t) eqn: Hi0;
      [exploit instrument_nonnil; eauto|]; clarify.
    repeat eexists; try apply exec_refl; auto.
    + rewrite in_app; setoid_rewrite Hi0; simpl; eauto.
    + instantiate (1 := 0); eauto.
    + setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
    + setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
  - specialize (IHHsteps _ Hsim eq_refl _ eq_refl).
    exploit exec_result; eauto.
    intros (P'a & i1 & li1 & P'b & v & ? & Hresult); subst.
    destruct (instr_result t0 i1 (G' t0) v)
      as [((((t', ?), ?), ?), ?)|] eqn: Hi1; clarify.
    rewrite in_app in Ht; clarify; rewrite in_app in Ht.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Ht as [? | [? | [? | ?]]].
    + exploit IHHsteps; eauto; clarify; do 11 eexists.
      { rewrite <- app_assoc; eauto. }
      repeat split; eauto; eapply exec_step_inv; eauto.
    + clarify.
      exploit IHHsteps; eauto; intros (? & ? & ? & ? & n' & i' & li' & rest & ? 
        & ? & ? & ? & ? & Hli' & Hli & ? & Hrest & ?); clarify.
      destruct li'; clarify.
      * destruct rest; clarify.
        inversion Hrest; clarify.
        do 11 eexists.
        { instantiate (1 := []); rewrite app_nil_r; eauto. }
        repeat eexists.
        { eapply exec_step_inv; try apply Hexec'; eauto.
          eapply exec_star_trans; eauto. }
        { rewrite Hli, in_app; clarify. }
        { instantiate (2 := 0); simpl.
          instantiate (1 := tl (instrument_instr i0 t));
            destruct (instrument_instr i0 t) eqn: Hi0; clarify.
          exploit instrument_nonnil; eauto; clarify. }
        { destruct (instrument_instr i0 t) eqn: Hi0; clarify.
          exploit instrument_nonnil; eauto; clarify. }
        { auto. }
        { auto. }
        { apply exec_refl. }
      * do 11 eexists; [|split; eauto; repeat split; eauto].
        { rewrite <- app_assoc; eauto. }
        { instantiate (1 := n' + 1); rewrite <- skipn_skipn, Hli'; auto. }
        { eapply exec_step_inv; eauto. }
    + destruct t'; clarify.
      destruct i1; clarify.
      rewrite <- exec_rev in *.
      exploit spawn_instrumented; eauto.
      { rewrite in_app; clarify. }
      { clarify. }
      intros ([|?] & Hli & Hsafe'); clarify.
      inversion Hsafe'; clarify.
      repeat eexists.
      * eapply exec_step_inv; eauto.
        simpl; rewrite app_nil_r; auto.
      * rewrite in_app, Hli; simpl; eauto.
      * instantiate (2 := 0); simpl.
        instantiate (1 := tl (instrument_instr i0 t));
          destruct (instrument_instr i0 t) eqn: Hi0; clarify.
        exploit instrument_nonnil; eauto; clarify.
      * destruct (instrument_instr i0 t) eqn: Hi0; clarify.
        exploit instrument_nonnil; eauto; clarify.
      * auto.
      * auto.
      * apply exec_refl.
    + exploit IHHsteps; eauto; clarify; do 11 eexists.
      { rewrite <- app_assoc; eauto. }
      repeat split; eauto; eapply exec_step_inv; eauto.
Qed.

Lemma instrument_thread' : forall P (Hsafe : safe_locs P) P1
  (Hsim : state_sim P P1) (Hdistinct : distinct P1)
  P1' G1 lo lc G1' (Hroot : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t o c t' n P1'' G' (Hstep : exec P1' G1' t o (Some c) P1'' G')
  (Hloc : loc_of c = (C' + t', n)) (Ht' : t' < zt),
  t' = t \/ exists P2 lo2 lc2 G2 i' n' rest lo2' lc2',
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G2 /\
    In (t, instrument_instr i' t ++ instrument rest t) P2 /\
    In (t, skipn n' (instrument_instr i' t) ++ instrument rest t) P1' /\
    n' < length (instrument_instr i' t) /\
    exec_star (Some P2) G2 lo2' lc2' (Some P1') G1' /\
    match i' with Spawn u _ | Wait u => t' = u | _ => False end.
Proof.
  intros.
  exploit exec_result; eauto; intros (P1a & i & li & P1b & v & ? & Hresult);
    subst.
  exploit step_into_instrument; eauto.
  { rewrite in_app; clarify. }
  intros (? & ? & ? & ? & n' & i' & ? & ? & ? & ? & ? & ? & ? & Hi' & ?);
    clarify.
  assert (In i (instrument [i'] t)) as Hi.
  { simpl; rewrite app_nil_r; eapply skipn_in.
    eapply nth_error_in; setoid_rewrite Hi'.
    instantiate (1 := 0); simpl; eauto. }
  exploit distinct_steps; eauto; intro.
  exploit instrument_own; try apply Hi; eauto.
  { rewrite <- exec_accesses; try apply Hstep; clarify; eauto.
    rewrite in_app; clarify. }
  intros [? | (i1 & ?)]; clarify.
  right; exists x; repeat eexists; eauto.
  - setoid_rewrite Hi'; rewrite in_app; clarify.
  - destruct (le_lt_dec (length (instrument_instr i1 t)) n'); auto.
    rewrite skipn_all in *; clarify.
Qed.

Definition spawns t := instr_rect'' _ _ (fun _ => 0)
  (fun u _ r => if eq_dec u t then S r else r) 0 (fun _ _ r1 r2 => r1 + r2).

Fixpoint spawns_list t li :=
  match li with
  | [] => 0
  | i :: rest => spawns t i + spawns_list t rest
  end.

Notation instr_list_rect P Q f1 f2 g h := (list_rect Q g
  (fun u r => h u r (instr_rect'' P Q f1 f2 g h u))).

Lemma spawns_list_def : forall t li, instr_list_rect _ _ (fun _ => 0)
  (fun u _ r => if eq_dec u t then S r else r) 0 (fun _ _ r1 r2 => r1 + r2) li =
   spawns_list t li.
Proof. induction li; clarify. Qed.

Fixpoint spawn_count t (P : state) :=
  match P with
  | [] => 0
  | (_, li) :: rest => spawns_list t li + spawn_count t rest
  end.

Definition safe_spawns P := forall t, spawn_count t P <= 1 /\
  (forall li, In (t, li) P -> spawn_count t P = 0).

Lemma spawn_count_app : forall t P1 P2, spawn_count t (P1 ++ P2) =
  spawn_count t P1 + spawn_count t P2.
Proof.
  induction P1; clarify.
  destruct a; clarify.
  rewrite IHP1; omega.
Qed.

(* up *)
Lemma in_step_rev : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G') t' li (Hin : In (t', li) P'),
  In (t', li) P \/ (t' = t /\ exists i, In (t, i :: li) P) \/
  exists li', In (t, Spawn t' li :: li') P.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i' & ? & ? & v & ? & Hresult).
  destruct (instr_result t i' (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi';
    clarify.
  rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
  setoid_rewrite in_app; destruct Hin as [? | [? | [? | ?]]]; clarify;
    try solve [left; eauto].
  - right; left; clarify; eauto.
  - right; right; destruct o0; clarify.
    destruct i'; clarify; eauto.
Qed.

Lemma safe_spawns_step : forall P (Hspawns : safe_spawns P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), safe_spawns P'.
Proof.
  intros; exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  intro t'; specialize (Hspawns t'); rewrite spawn_count_app in *; clarify.
  destruct o0 as [(u, li)|]; clarify.
  destruct i; clarify.
  generalize (Hspawns2 li).
  unfold spawns in *; simpl in *; rewrite (spawns_list_def t') in *.
  destruct (eq_dec u t'); [split; intros; omega|].
  split; [omega | intros ? Hin].
  destruct (eq_dec t' t).
  - subst; exploit Hspawns2.
    { rewrite in_app; clarify. }
    omega.
  - rewrite <- (Hspawns2 li0); [omega|].
    rewrite in_app in *; simpl in *.
    destruct Hin as [? | [? | [? | ?]]]; clarify.
  - assert (spawns t' i = 0) as Hz by (destruct i; clarify); rewrite Hz in *;
      clarify.
    generalize (Hspawns2 li); rewrite in_app in *; clarify.
    eapply Hspawns2; rewrite in_app; clarify.
Qed.

Lemma skipn_app' : forall A n (l1 l2 : list A) (Hn : n <= length l1),
  skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros; rewrite skipn_app.
  rewrite <- Nat.sub_0_le in Hn; rewrite Hn; auto.
Qed.

Lemma spawns_list_app : forall t P1 P2, spawns_list t (P1 ++ P2) =
  spawns_list t P1 + spawns_list t P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; omega.
Qed.


Lemma own_thread : forall t P1 G lo lc P1' G' (Ht : t < zt)
  (Hsteps : exec_star_minus t (Some P1) G lo lc P1' G')
  P (Hsafe : safe_locs P) P0 (Hsim : state_sim P P0)
  (Hdistinct : distinct P0) G0 lo0 lc0
  (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G)
  li (Hlive : In (t, li) P1) (Hli : li <> []) (Hspawns : safe_spawns P1),
  Forall (fun c => fst (loc_of c) <> C' + t) lc.
Proof.
  intros ?????????; remember (Some P1) as Pa; generalize dependent P1;
    induction Hsteps; clarify.
  exploit exec_result; eauto.
  intros (Pa & i & li' & Pb & v & ?); clarify.
  rewrite Forall_app; split.
  - rewrite Forall_forall; intros c' ? ?.
    destruct c; clarify.
    destruct (loc_of c') eqn: Hloc; clarify.
    exploit instrument_thread'; eauto.
    intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Ht' & ?)];
      clarify.
    exploit distinct_steps; eauto; intro.
    exploit distinct_steps; eauto; intro.
    exploit in_split; eauto; clarify; exploit distinct_thread; eauto;
      intros (? & ? & Hli'); subst.
    destruct i'; clarify.
    + specialize (Hspawns t0); clarify.
      exploit Hspawns2; eauto.
      rewrite H4, spawn_count_app; simpl.
      rewrite skipn_app; repeat rewrite spawns_list_app.
      rewrite app_length in *; simpl in *.
      destruct (n' - length (spawn_handler t' t0 zt)) eqn: Hminus;
        [clarify | omega].
      unfold spawns in *; simpl in *; clarify; omega.
    + destruct n'; clarify.
      rewrite <- skipn_app' in Ht'; [|omega].
      exploit step_instr; try apply Ht'; eauto.
      intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hpre & Hwait & Hrest & ?);
        clarify.
      exploit exec_other_threads; try apply Hpre; eauto; intro.
      exploit in_split; eauto; clarify.
      exploit distinct_steps; try (eapply exec_minus_exec; eauto); auto; intro.
      inversion Hwait; subst; exploit distinct_thread; eauto 2;
        intros (? & ? & Hi); inversion Hi; subst; clear Hi.
      exploit distinct_step; eauto; intro.
      exploit exec_mono; try apply Hrest; eauto.
      { instantiate (1 := []); rewrite in_app in Hdone; rewrite in_app; clarify.
      }
      clarify; rewrite skipn_nil in *; clarify.
  - destruct P'; [|inversion Hsteps]; clarify.
    destruct (instr_result t' i (G t') v)
      as [((((th, ?), ?), ?), ?)|] eqn: Hresult; clarify.
    generalize (safe_spawns_step Hspawns Hexec); intro.
    destruct th; simpl in *.
    + destruct i; clarify.
      eapply IHHsteps; eauto.
      * eapply exec_step_inv; eauto.
      * eapply exec_other_thread; eauto.
    + eapply IHHsteps; eauto.
      * eapply exec_step_inv; eauto.
      * eapply exec_other_thread; eauto.
Qed.

Lemma step_thread' : forall P G t o c P' G'
   (Hstep : exec P G t o c (Some P') G'),
  exists i li', In (t, i :: li') P /\ In (t, li') P'.
Proof.
  intros; inversion Hstep; clarify; repeat eexists; eauto; rewrite in_app;
    clarify.
Qed.

Lemma safe_spawns_steps : forall P (Hspawns : safe_spawns P)
  G o c P' G' (Hsteps : exec_star (Some P) G o c (Some P') G'), safe_spawns P'.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P;
    induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  apply (IHHsteps s); auto.
  eapply safe_spawns_step; eauto.
Qed.

Lemma instrument_own_thread : forall t (Ht : t < zt) P G lo lc P1 G1
  (Hsteps : exec_star (Some P) G lo lc (Some P1) G1)
  P0 (Hsafe : safe_locs P0) P0' (Hdistinct : distinct P0')
  (Hspawns : safe_spawns P0') (Hsim : state_sim P0 P0') G0 lo0 lc0
  (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  li (Hin : In (t, li) P) li1 (Hin : In (t, li1) P1) (Hlive : li1 <> []),
  Forall (fun c => fst (loc_of c) <> C' + t)
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros until li; remember (Some P) as Pa; remember (Some P1) as Pb;
    generalize dependent P1; generalize dependent P;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  specialize (IHHsteps _ eq_refl _ eq_refl); clarify.
  rewrite <- exec_rev in Hsteps.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; eauto; clarify.
  specialize (IHHsteps (skipn x li)); use IHHsteps.
  exploit distinct_steps; eauto; intro.
  destruct (eq_dec t0 t).
  - subst; exploit exec_ops; eauto; intro.
    exploit step_thread; eauto; intros (? & ? & Heq & ?).
    rewrite Heq in IHHsteps; use IHHsteps.
    rewrite filter_app, Forall_app; clarify.
    rewrite filter_negb_none; auto.
  - exploit exec_step_m; eauto.
    { apply exec_refl_m. }
    repeat rewrite app_nil_r; intro.
    exploit exec_other_thread; eauto; intro.
    exploit distinct_step; eauto; intro.
    exploit distinct_in; [eauto | apply Hin0 | eauto | clarify].
    rewrite filter_app, Forall_app; clarify.
    exploit own_thread; eauto.
    { eapply exec_star_trans; eauto. }
    { eapply safe_spawns_steps; eauto.
      eapply exec_star_trans; eauto. }
    intro; apply Forall_filter; auto.
Qed.

(* up *)
Lemma C_meta : forall t (Ht : t < zt) o, meta_loc (C + t, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed. 

Definition good_lock x := state_forall (fun i =>
  match i with Load _ p | Store p _ => p <> x | _ => True end).

Definition lock_op x a := exists t, a = Acq t x \/ a = Rel t x.

Lemma good_lock_ops : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc P' G'),
  Forall (fun a => loc_of a = (x, 0) -> lock_op x a) lc.
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; induction Hsteps; clarify.
  rewrite Forall_app; split.
  - rewrite Forall_forall; intros.
    inversion Hexec; clarify; unfold lock_op; eauto;
      setoid_rewrite Forall_app in Hlock; clarify;
      inversion Hlock2 as [|?? Hi]; inversion Hi; unfold instr_forall in *;
      clarify.
  - clarify.
    destruct P'; [|inversion Hsteps; clarify].
    exploit forall_step; eauto.
Qed.

Lemma lock_hold : forall m l t ops (Hinit : initialized m (l, 0))
  (Hheld : can_read m (l, 0) (S t)) (Hcon : consistent (m ++ ops))
  (Hprog : Forall prog_op ops) (Hlock : Forall (fun a => loc_of a = (l, 0) ->
     lock_op l a) ops),
  can_read (m ++ ops) (l, 0) (S t) \/ In (Rel t l) ops.
Proof.
  induction ops using rev_ind; clarsimp.
  rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite Forall_app in *; clarify.
  inversion Hlock2 as [|?? Hx]; inversion Hprog2; rewrite in_app; clarify.
  unfold can_read in *.
  repeat rewrite <- app_assoc in *; simpl.
  destruct (eq_dec (loc_of x) (l, 0)).
  - unfold lock_op in Hx; clarify.
    destruct Hx as [? | ?]; clarify.
    + rewrite app_assoc, can_arw_SC_iff in Hcon.
      specialize (Hcon 0); exploit consistent_app_SC; eauto; intro.
      exploit can_read_thread'; eauto; intro.
      rewrite app_assoc in IHops.
      generalize (init_steps Hinit Hprog1); intro.
      generalize (can_read_unique(m := m ++ ops)(p := (l, 0)) (S t) 0); clarify.
    + rewrite app_assoc, can_arw_SC_iff in Hcon.
      specialize (Hcon 0); exploit consistent_app_SC; eauto; intro.
      exploit can_read_thread'; eauto; intro.
      rewrite app_assoc in IHops.
      generalize (init_steps Hinit Hprog1); intro.
      generalize (can_read_unique(m := m ++ ops)(p := (l, 0)) (S t) (S x0));
        intro Heq; clarify.
      inversion Heq; auto.
  - rewrite app_assoc, loc_valid_SC; clarify.
    repeat rewrite <- app_assoc in *; clarify.
Qed.

Lemma ARW_can_read : forall p m v v' t, consistent (m ++ [ARW t p v v']) ->
  can_read m p v.
Proof.
  intros; rewrite can_arw_SC_iff in H; specialize (H 0).
  exploit consistent_app_SC; eauto; intro.
  eapply can_read_thread'; eauto.
Qed.

Lemma can_read_arwritten : forall m p u v t, consistent (m ++ [ARW t p u v]) ->
  can_read (m ++ [ARW t p u v]) p v.
Proof.
  intros.
  apply (can_read_thread' _ _ _ t).
  rewrite read_arwritten_SC; auto.
Qed.

Lemma rel_inv : forall t x P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc P' G') li (Hin : In (t, li) P)
  (Hrel : In (Rel t x) lc), exists li1 li2, li = li1 ++ Unlock x :: li2 /\
  match P' with Some s' => exists n, In (t, skipn n li2) s' | None => True end.
Proof.
  intros; rewrite exec_rev in Hsteps; remember (Some P) as P0;
    generalize dependent P; induction Hsteps; clarify.
  rewrite <- exec_rev in Hsteps.
  rewrite in_app in Hrel; destruct Hrel.
  - clarify.
    specialize (IHHsteps P0); clarify.
    repeat eexists; eauto.
    destruct P''; clarify.
    exploit distinct_steps; eauto; intro.
    exploit exec_keep.
    + eauto.
    + eapply exec_step, exec_refl; eauto.
    + eauto.
    + clarify; rewrite skipn_skipn in *; eauto.
  - inversion Hexec'; clarify.
    inversion H; clarify.
    exploit exec_mono; eauto.
    { rewrite in_app; clarify. }
    intros (n & Hn).
    exists (firstn n li), rest.
    rewrite Hn, firstn_skipn; clarify.
    exists 0; rewrite in_app; clarify.
Qed.  

Lemma critical_section : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hdistinct : distinct P) m (Hinit : initialized m (x, 0))
  (Hcon : consistent (m ++ lc))
  t li (HP : In (t, Lock x :: li) P) n (HP' : In (t, skipn n li) P'),
  In (Unlock x) (firstn n li) \/ can_read (m ++ lc) (x, 0) (S t).
Proof.
  intros.
  exploit step_instr; eauto.
  intros (P1 & G1 & lo1 & lc1 & o & c & P1' & G1' & lo2 & lc2 & Hpre & Hacq &
    Hrest & ?); clarify.
  exploit exec_other_threads; try apply Hpre; eauto; intro.
  exploit distinct_steps; [|eapply exec_minus_exec|]; eauto; intro.
  exploit in_split; eauto; intros (Pa & Pb & ?).
  inversion Hacq; subst; exploit distinct_thread; eauto; clarify.
  rewrite split_app, app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite app_assoc; intro.
  exploit can_read_arwritten; eauto; intro Hlocked.
  exploit lock_hold; try apply Hcon; rewrite <- app_assoc in Hlocked; eauto.
  { rewrite app_assoc; apply init_step; clarify.
    apply init_steps; auto.
    eapply prog_steps, exec_minus_exec; eauto. }
  { eapply prog_steps; eauto. }
  { eapply good_lock_ops, Hrest.
    eapply forall_steps; eauto.
    eapply exec_step_inv; try eapply exec_minus_exec; eauto. }
  repeat rewrite <- app_assoc; clarify.
  exploit distinct_step; eauto; intro.
  left; exploit rel_inv; eauto.
  { rewrite in_app; clarify. }
  intros (li1 & li2 & ? & n' & HP'2); clarify.
  generalize (in_split _ _ HP'), (in_split _ _ HP'2); clarify.
  exploit distinct_steps; eauto; intro.
  exploit distinct_thread; eauto; intros (? & ? & Heq); subst.
  rewrite firstn_app.
  destruct (n - length li1) eqn: Hminus; [|rewrite in_app; clarify].
  assert (length (skipn n' li2) = length (skipn n (li1 ++ Unlock x :: li2)))
    by (rewrite Heq; auto).
  repeat rewrite skipn_length in *; rewrite app_length in *; clarify; omega.
Qed.  

Lemma exec_t_steps : forall P G lo lc P' G'
  (Hexec : exec_star P G lo lc (Some P') G') t,
  exists n lo1 lc1 P1 G1 lo2 lc2, exec_star_minus t P G lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t n lo2 lc2 (Some P') G'.
Proof.
  intros; remember (Some P') as P2; generalize dependent P'; induction Hexec;
    clarify.
  - exists 0; repeat eexists; apply exec_refl_m.
  - specialize (IHHexec _ eq_refl); destruct IHHexec as (n & ?); clarify.
    destruct (eq_dec t0 t).
    + subst; exists (S n); repeat eexists; eauto; [apply exec_refl_m|].
      simpl; eauto.
    + repeat eexists; eauto.
      eapply exec_step_m; eauto.
Qed.
      
(* up *)
Lemma X_meta : forall v (Ht : v < zv) o, meta_loc (X + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma instrument_hd : forall i t, let i' := hd (Lock 0) (instrument_instr i t)
  in match i' with
  | Assign _ _ | Wait _ | Assert_le _ _ => i' = i
  | Load _ (x, _) => x = C + t
  | Lock l => i' = i \/ exists v, accesses i = Some v /\ l = X + fst v /\
      (safe_instr i -> fst v < zv)
  | _ => False
  end.
Proof.
  destruct i; try (destruct x); clarify; eauto; destruct zt; clarify.
  - right; repeat eexists; clarify.
  - right; repeat eexists; clarify.
Qed.

Corollary instrument_access : forall i t i' li rest v
  (Hli : i :: li = instrument_instr i' t ++ rest)
  (Haccess : accesses i = Some v), (exists o, v = (C + t, o)) \/
    snd v = 0 /\ (i = Lock (fst v) /\ i' = i \/
    exists v', accesses i' = Some v' /\ fst v = X + fst v' /\
      (safe_instr i' -> fst v' < zv)).
Proof.
  intros.
  generalize (instrument_hd i' t); intro Hcases.
  generalize (instrument_nonnil i' t); destruct (instrument_instr i' t);
    clarify.
  destruct i0; try destruct v; clarify; eauto.
  right; clarify; eauto.
Qed.

Lemma R_meta : forall v (Ht : v < zv) o, meta_loc (R + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma W_meta : forall v (Ht : v < zv) o, meta_loc (W + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma v_not_C : forall t (Ht : t < zt) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (C + t, o1) = Some v \/
    (exists o, Some (C + t, o1) = Some (R + fst v, o)) \/
    (exists o, Some (C + t, o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply C_meta; auto.
  - eapply Hmetalocs_disjoint_CR; eauto.
  - eapply Hmetalocs_disjoint_CW; eauto.
Qed.

Lemma v_not_X : forall v' (Hv' : v' < zv) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (X + v', o1) = Some v \/
    (exists o, Some (X + v', o1) = Some (R + fst v, o)) \/
    (exists o, Some (X + v', o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply X_meta; auto.
  - eapply Hmetalocs_disjoint_RX; try (symmetry; apply H1); eauto.
  - eapply Hmetalocs_disjoint_WX; try (symmetry; apply H1); eauto.
Qed.

Lemma v_W : forall v' (Hv' : v' < zv) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (W + v', o1) = Some v \/
    (exists o, Some (W + v', o1) = Some (R + fst v, o)) \/
    (exists o, Some (W + v', o1) = Some (W + fst v, o))), v' = fst v.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply W_meta; auto.
  - exploit Hmetalocs_disjoint_WR; try apply H1; auto; contradiction.
  - eapply plus_reg_l; eauto.
Qed.

Lemma unlock_last : forall i t n l rest, skipn n (instrument_instr i t) =
  Unlock l :: rest -> rest = [].
Proof.
  intros.
  assert (nth_error (skipn n (instrument_instr i t)) 0 = Some (Unlock l))
    by clarsimp.
  rewrite skipn_nth in *; clarify.
  destruct i; try destruct x; clarsimp.
  - destruct n; clarify.
    rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))).
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n2; clarify.
      destruct n2; clarsimp.
      rewrite skipn_all in H; clarify; omega.
  - destruct n; clarify.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
             (length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)))].
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2) -
        length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)) eqn: Hminus; clarify.
      destruct n3; clarify.
      destruct n3; clarsimp.
      rewrite skipn_all in H; clarify; [|omega].
      rewrite skipn_all in H; clarify; omega.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
  - unfold unlock_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (set_vc (C' + t) (L' + m) zt tmp1 )));
      [|destruct (lt_dec (n - length (set_vc (C' + t) (L' + m) zt tmp1 ))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit set_vc_instrs; eauto; clarify.
    + destruct (n - length (set_vc (C' + t) (L' + m) zt tmp1)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
      rewrite skipn_all in H; clarify; [|omega].
      rewrite skipn_all in H; clarify; [|omega].
      destruct (n - (length (set_vc (C' + t) (L' + l) zt tmp1) + 3));
        clarsimp.
  - unfold spawn_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    unfold wait_handler in *; rewrite in_app in H1; destruct H1 as [?|[?|[?|?]]]; clarify.
    exploit max_vc_instrs; eauto; clarify.
Qed.      

Lemma lock_first : forall i t n l rest, skipn n (instrument_instr i t) =
  Lock l :: rest -> n = 0.
Proof.
  intros.
  assert (nth_error (skipn n (instrument_instr i t)) 0 = Some (Lock l))
    by clarsimp.
  rewrite skipn_nth in *; clarify.
  destruct i; try destruct x; clarsimp.
  - destruct n; clarify.
    rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))).
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n2; clarify.
      destruct n2; clarsimp.
  - destruct n; clarify.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
             (length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)))].
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2) -
        length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)) eqn: Hminus; clarify.
      destruct n3; clarify.
      destruct n3; clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
  - unfold unlock_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (set_vc (C' + t) (L' + m) zt tmp1 )));
      [|destruct (lt_dec (n - length (set_vc (C' + t) (L' + m) zt tmp1))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit set_vc_instrs; eauto; clarify.
    + destruct (n - length (set_vc (C' + t) (L' + m) zt tmp1)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - unfold spawn_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    unfold wait_handler in *; rewrite in_app in H1; destruct H1 as [?|[?|[?|?]]]; clarify.
    exploit max_vc_instrs; eauto; clarify.
Qed.  

Lemma L_meta : forall l (Ht : l < zl) o, meta_loc (L + l, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma v_not_L : forall l (Hl : l < zl) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (L + l, o1) = Some v \/
    (exists o, Some (L + l, o1) = Some (R + fst v, o)) \/
    (exists o, Some (L + l, o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply L_meta; auto.
  - eapply Hmetalocs_disjoint_LR; eauto.
  - eapply Hmetalocs_disjoint_LW; eauto.
Qed.

Definition bounded_instr := instr_rect'' _ _ (fun _ => True)
  (fun u li r => u < zt /\ r) True (fun _ _ r1 r2 => r1 /\ r2).

Definition bounded_threads (P : state) := Forall (fun e => fst e < zt /\
  Forall bounded_instr (snd e)) P.

Lemma bounded_spawn : forall u li, bounded_instr (Spawn u li) <->
  u < zt /\ Forall bounded_instr li.
Proof.
  unfold bounded_instr; induction li; split; clarify.
  - constructor; auto.
    apply IHli; auto.
  - inversion H2; clarify.
    apply IHli; auto.
Qed.

Lemma bounded_step : forall P (Hbounded : bounded_threads P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), bounded_threads P'.
Proof.
  intros; inversion Hstep; clarify; unfold bounded_threads in *;
    rewrite Forall_app in *; clarify; inversion Hbounded2 as [|?? [? Hbound]];
    inversion Hbound; clarify.
  rewrite bounded_spawn in *.
  inversion Hbound; repeat constructor; clarify.
Qed.

Corollary bounded_steps : forall P (Hbounded : bounded_threads P)
  G o c P' G' (Hsteps : exec_star (Some P) G o c (Some P') G'),
  bounded_threads P'.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit bounded_step; eauto.
Qed.

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

Lemma no_spawn_bounded : forall l (Hout : Forall (fun i =>
  match i with Spawn _ _ => False | _ => True end) l),
  Forall bounded_instr l.
Proof.
  intros; rewrite Forall_forall in *; clarify.
  specialize (Hout x); destruct x; unfold bounded_instr; clarify.
Qed.

Lemma bounded_instrument : forall i, safe_instr i ->
  forall t, Forall bounded_instr (instrument_instr i t).
Proof.
  intro; eapply instr_ind' with (Q := fun l => Forall safe_instr l ->
    forall t, Forall bounded_instr (instrument l t))(i := i); clarify.
  - destruct i0; auto; intros; apply no_spawn_bounded; rewrite Forall_forall;
      intros i' ?; destruct i'; auto; exploit spawn_in_handler; eauto; clarify.
  - rewrite Forall_app; split.
    + apply no_spawn_bounded; rewrite Forall_forall; intros ? Hin.
      destruct x; auto.
      setoid_rewrite in_app in Hin; destruct Hin; clarify.
      exploit max_vc_instrs; eauto; clarify.
    + constructor; clarify.
      rewrite bounded_spawn, safe_instrs in *; auto.
  - inversion H; rewrite Forall_app; clarify.
Qed.

Corollary bounded_instr_list : forall li, Forall safe_instr li ->
  forall t, Forall bounded_instr (instrument li t).
Proof.
  induction li; clarify.
  inversion H; rewrite Forall_app; clarify.
  apply bounded_instrument; auto.
Qed.

Corollary bounded_sim : forall P (Hsafe : safe_locs P)
  (Ht : Forall (fun e => fst e < zt) P) P' (Hsim : state_sim P P'),
  bounded_threads P'.
Proof.
  induction P; clarify.
  - inversion Hsim; clarify; constructor.
  - inversion Hsim; inversion Hsafe; inversion Ht; clarify.
    constructor; [|apply IHP; auto].
    clarsimp.
    apply bounded_instr_list; auto.
Qed.

Lemma skipn_cons : forall A l (x y : A) l' n, skipn n (x :: l) = y :: l' ->
  skipn n l = l'.
Proof.
  induction l; clarify.
  - destruct n; simpl in *; [|rewrite skipn_nil in *]; clarify.
  - destruct n; clarify; eauto.
Qed.

Definition v_access v a := loc_of a = v \/
  (exists o, loc_of a = (R + fst v, o)) \/
  (exists o, loc_of a = (W + fst v, o)).

Lemma instrument_length : forall i t, length (instrument_instr i t) <> 0.
Proof.
  repeat intro.
  destruct (instrument_instr i t) eqn: Hi; clarify.
  exploit instrument_nonnil; eauto.
Qed.

(* replace the previous version with this *)
Lemma t_steps_extend' : forall P' G' lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  P G t n lo0 lc0 (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo0 lc0 (Some P') G')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hn : n <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (lo0 ++ lo) (lc0 ++ lc) (Some P'') G''.
Proof.
  intros ???????.
  remember (Some P') as S; remember (Some P'') as S'; generalize dependent P'';
    generalize dependent P'; induction Hsteps; clarify.
  { clarsimp.
    erewrite <- t_steps_length; eauto. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl).
  destruct (eq_dec t0 t); clarify.
  - exploit t_steps_add_t; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
  - exploit t_steps_add_other; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
Qed.

Lemma exec_thread' : forall P G t o c P' G' (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G') lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (opt_to_list o ++ lo) (opt_to_list c ++ lc)
    (Some P'') G''.
Proof.
  intros; eapply t_steps_extend' with (n := 1); eauto.
  simpl; repeat eexists; eauto.
  - apply exec_refl_m.
  - clarsimp.
Qed.

Lemma app_neq : forall A (l l' : list A) a, a :: l ++ l' <> l'.
Proof.
  repeat intro.
  assert (length (a :: l ++ l') = length l') by (rewrite H; auto).
  simpl in *; rewrite app_length in *; omega.
Qed.

Lemma last_cons : forall A (x d : A) l (Hnonnil : l <> []), last (x :: l) d =
  last l d.
Proof. clarify. Qed.

Opaque last.
Lemma skipn_last : forall A (l l' : list A) x d n,
  skipn n (l ++ l') = x :: l' -> n = length l - 1 /\ x = last l d.
Proof.
  induction l; clarify.
  { exploit skip_cons_neq; eauto; clarify. }
  destruct (nil_dec l).
  - subst; destruct n; simpl in *.
    + clarify.
    + exploit skip_cons_neq; eauto; clarify.
  - rewrite last_cons; auto.
    destruct n; clarify.
    { destruct l; clarify.
      exploit app_neq; eauto; clarify. }
    exploit IHl; eauto; clarify.
    split; [|eauto].
    assert (length l <> 0) by (destruct l; clarify); omega.
Qed.    

Lemma step_thread0 : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  exists i li, In (t, i :: li) P.
Proof.
  intros; inversion Hstep; clarify; repeat eexists; rewrite in_app; clarify.
Qed.

Lemma lock_hold' : forall m l t ops (Hinit : initialized m (l, 0))
  (Hheld : can_read (m ++ ops) (l, 0) (S t)) (Hcon : consistent (m ++ ops))
  (Hprog : Forall prog_op ops) (Hlock : Forall (fun a => loc_of a = (l, 0) ->
     lock_op l a) ops),
  can_read m (l, 0) (S t) \/ In (Acq t l) ops.
Proof.
  induction ops using rev_ind; clarsimp.
  rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite Forall_app in *; clarify.
  inversion Hlock2 as [|?? Hx]; inversion Hprog2; rewrite in_app; clarify.
  unfold can_read in *.
  repeat rewrite <- app_assoc in *; simpl.
  destruct (eq_dec (loc_of x) (l, 0)).
  - unfold lock_op in Hx; clarify.
    destruct Hx as [? | ?]; clarify.
    + assert (S t = S x0) as Heq; [|inversion Heq; clarify].
      rewrite app_assoc in Hcon; rewrite <- read_arwritten_SC; eauto.
      apply can_read_thread.
      unfold can_read; repeat rewrite <- app_assoc; auto.
    + generalize (init_steps Hinit Hprog1); intro.
      inversion Hprog2; subst; exploit init_step; eauto; rewrite <- app_assoc;
        intro.
      generalize (can_read_unique(m := m ++ ops ++ [Rel x0 l])(p := (l, 0))
        (S t) 0); intro Heq; clarify.
      use Heq.
      * use Heq; clarify.
        eapply can_read_thread'.
        unfold can_read; rewrite app_assoc, read_arwritten_SC; auto.
        rewrite <- app_assoc; auto.
      * unfold can_read; repeat rewrite <- app_assoc; auto.
  - simpl in Hheld; rewrite app_assoc, loc_valid_SC in Hheld; clarify.
    repeat rewrite <- app_assoc in *; clarify.
Qed.

Definition good_var x := state_forall
  (fun i => match i with Lock l | Unlock l => l <> x | _ => True end).

Lemma protect_self : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  l (Hlock : good_lock (l, 0) P0')
  m (Hinit : initialized m (l, 0))
  t (Hheld : can_read (m ++ lc0) (l, 0) (S t))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  (Hno_lock : Forall (fun a => a <> Rel t l) lc)
  (Hcon : consistent (m ++ lc0 ++ lc)),
  Forall (fun a => loc_of a <> (l, 0))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; clarify.
  specialize (IHHsteps' _ eq_refl).
  rewrite filter_app, Forall_app; clarify.
  rewrite Forall_forall; repeat intro.
  rewrite <- exec_rev in Hsteps'.
  rewrite app_assoc in H; exploit lock_hold; try apply H; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { eapply prog_steps; eauto. }
  { exploit forall_steps; eauto; intro.
    eapply good_lock_ops; eauto. }
  intros [Hheld' | ?].
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  destruct c; clarify.
  exploit forall_steps; eauto; intro.
  exploit good_lock_ops; eauto.
  { eapply exec_step'; eauto; apply exec_refl. }
  rewrite Forall_app; simpl; intros [Hx _].
  inversion Hx as [|?? Hl]; clarify.
  destruct Hl as [? [? | ?]]; subst.
  - inversion Hexec'; clarify.
    rewrite can_arw_SC_iff in Hcon.
    specialize (Hcon 0); exploit consistent_app_SC; try apply Hcon; intro.
    exploit can_read_thread'; eauto; intro.
    exploit can_read_unique.
    { apply H. }
    { do 2 (eapply init_steps, prog_steps; eauto). }
    { apply Hheld'. }
    { eauto. }
    clarify.
  - inversion Hexec'; clarify.
    rewrite can_arw_SC_iff in Hcon.
    specialize (Hcon 0); exploit consistent_app_SC; try apply Hcon; intro.
    exploit can_read_thread'; eauto; intro.
    exploit can_read_unique.
    { apply H. }
    { do 2 (eapply init_steps, prog_steps; eauto). }
    { apply Hheld'. }
    { eauto. }
    intro Heq; inversion Heq; unfold beq, negb in cond; clarify.
  - rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto.
Qed.
 
(* up *)
Lemma Forall2_in1 : forall A P (l1 l2 : list A) x1 (Hall : Forall2 P l1 l2)
  (Hin : In x1 l1), exists x2, In x2 l2 /\ P x1 x2.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  exploit Forall2_app_inv_l; eauto; intros (? & ? & ? & Hall' & ?).
  inversion Hall'; clarify.
  setoid_rewrite in_app; simpl; eauto.
Qed.

Lemma Forall2_in2 : forall A P (l1 l2 : list A) x2 (Hall : Forall2 P l1 l2)
  (Hin : In x2 l2), exists x1, In x1 l1 /\ P x1 x2.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hall' & ?).
  inversion Hall'; clarify.
  setoid_rewrite in_app; simpl; eauto.
Qed.

Lemma access_v : forall i t n i' rest (Ht : t < zt)
  (Hn : skipn n (instrument_instr i t) = i' :: rest)
  v o (Hv : v < zv) (Hmeta : ~meta_loc (v, o))
  (Hi : i <> Lock v /\ i <> Unlock v) (Hsafe : safe_instr i)
  (Hwait : match i with Wait u => u < zt | _ => True end)
  (Haccess : accesses i' = Some (v, o) \/ accesses i' = Some (R + v, o) \/
             accesses i' = Some (W + v, o)),
  n > 0 /\ match i with Load _ p => fst p = v | Store p _ => fst p = v
                  | _ => False end.
Proof.
  intros.
  destruct (accesses i') as [(?, ?)|] eqn: Hi'; [|clarify].
  destruct n; clarify.
  - exfalso; exploit instrument_access; eauto.
    { setoid_rewrite <- app_nil_r in Hn at 1; eauto. }
    intros [[? ?] | [? [? | ?]]]; clarify.
    + eapply v_not_C with (v := (v, o)); eauto.
      destruct Haccess as [? | [? | ?]]; eauto.
    + contradiction Hsafe1; destruct Haccess; clarify;
        [apply R_meta | apply W_meta]; auto.
    + eapply v_not_X with (v := (v, o))(v' := fst x); eauto.
      destruct Haccess as [? | [? | ?]]; eauto.
  - destruct (instrument_instr i t) eqn: Hinstr; clarify.
    destruct i; try destruct x; clarify; try (rewrite skipn_nil in *; clarify).
    + repeat rewrite skipn_app in Hn; rewrite <- app_assoc in Hn.
      destruct (skipn n (hb_check (W' + v1) (C' + t) zt tmp1 tmp2)) eqn: Hskip;
        clarify.
      destruct (skipn (n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2))
        (move (C' + t, t) (R' + v1, t) tmp1)) eqn: Hskip'; clarify.
      destruct ((n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2 ++
        move (C' + t, t) (R' + v1, t) tmp1))); clarify.
      * contradiction Hsafe1; destruct Haccess; clarify;
          [apply R_meta | apply W_meta]; auto.
      * destruct n2; clarify; [|rewrite skipn_nil in *; clarify].
        exfalso; eapply v_not_X with (v := (v, o))(v' := v1); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * unfold move in Hskip';
          destruct (n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2));
          clarify.
        { exfalso; eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n2; clarify; [|rewrite skipn_nil in Hskip'; clarify].
        destruct Haccess as [? | [? | ?]]; clarify.
        { contradiction Hmeta; apply R_meta; auto. }
        eapply plus_reg_l; eauto.
        { exploit (Hmetalocs_disjoint_WR Hv Hsafe2); auto; contradiction. }
      * exploit hb_check_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { destruct Haccess as [? | [? | ?]]; clarify.
          { contradiction Hmeta; apply W_meta; auto. }
          { exploit (Hmetalocs_disjoint_WR Hsafe2 Hv); auto; contradiction. }
          eapply plus_reg_l; eauto. }
        { exfalso; eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + repeat rewrite skipn_app in Hn; repeat rewrite <- app_assoc in Hn.
      destruct (skipn n (hb_check (W' + v1) (C' + t) zt tmp1 tmp2)) eqn: Hskip;
        clarify.
      destruct (skipn (n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2))
        (hb_check (R' + v1) (C' + t) zt tmp1 tmp2)) eqn: Hskip'; clarify.
      destruct (skipn (n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2) -
        length (hb_check (R' + v1) (C' + t) zt tmp1 tmp2))
        (move (C' + t, t) (W' + v1, t) tmp1)) eqn: Hskip''; clarify.
      destruct ((n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2 ++
             hb_check (R' + v1) (C' + t) zt tmp1 tmp2 ++
             move (C' + t, t) (W' + v1, t) tmp1))); clarify.
      * contradiction Hsafe1; destruct Haccess; clarify;
          [apply R_meta | apply W_meta]; auto.
      * destruct n2; clarify; [|rewrite skipn_nil in *; clarify].
        exfalso; eapply v_not_X with (v := (v, o))(v' := v1); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * unfold move in Hskip'';
          destruct (n - length (hb_check (W' + v1) (C' + t) zt tmp1 tmp2) -
            length (hb_check (R' + v1) (C' + t) zt tmp1 tmp2)); clarify.
        { exfalso; eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n2; clarify; [|rewrite skipn_nil in Hskip''; clarify].
        destruct Haccess as [? | [? | ?]]; clarify.
        { contradiction Hmeta; apply W_meta; auto. }
        { exploit (Hmetalocs_disjoint_WR Hsafe2 Hv); auto; contradiction. }
        eapply plus_reg_l; eauto.
      * exploit hb_check_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip'; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { destruct Haccess as [? | [? | ?]]; clarify.
          { contradiction Hmeta; apply R_meta; auto. }
          eapply plus_reg_l; eauto.
          { exploit (Hmetalocs_disjoint_WR Hv Hsafe2); auto; contradiction. } }
        { exfalso; eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
      * exploit hb_check_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { destruct Haccess as [? | [? | ?]]; clarify.
          { contradiction Hmeta; apply W_meta; auto. }
          { exploit (Hmetalocs_disjoint_WR Hsafe2 Hv); auto; contradiction. }
          eapply plus_reg_l; eauto. }
        { exfalso; eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + exploit max_vc_instr; eauto.
      { eapply skipn_in; setoid_rewrite Hn; simpl; auto. }
      intros (? & ? & [? | ?]); clarify.
      * eapply v_not_L with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * eapply v_not_C with (v := (v, o))(t := t); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
    + unfold unlock_handler in Hinstr.
      destruct (set_vc (C' + t) (L' + m) zt tmp1) eqn: Hset; clarify.
      { destruct zt; clarify. }
      repeat rewrite skipn_app in Hn; rewrite <- app_assoc in Hn.
      destruct (skipn n l) eqn: Hskip.
      destruct (skipn (n - length l) (inc_vc t (C' + t) tmp1)) eqn: Hskip'.
      * destruct (n - length (l ++ inc_vc t (C' + t) tmp1)); clarify;
          [|rewrite skipn_nil in *; clarify].
        destruct Haccess; clarify; contradiction Hsafe1;
          [apply R_meta | apply W_meta]; auto.
      * unfold inc_vc in Hskip'; destruct (n - length l); clarify.
        { eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n1; clarify.
        destruct n1; clarify; [|rewrite skipn_nil in *; clarify].
        eapply v_not_C with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * clarify.
        exploit set_vc_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hset; instantiate (1 := 1); simpl.
          eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        { eapply v_not_L with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + unfold spawn_handler in Hinstr.
      destruct (max_vc (C' + t) (C' + t0) zt tmp1 tmp2) eqn: Hmax; clarify.
      { destruct zt; clarify. }
      repeat rewrite skipn_app in Hn; rewrite <- app_assoc in Hn.
      destruct (skipn n l) eqn: Hskip.
      destruct (skipn (n - length l) (inc_vc t (C' + t) tmp1)) eqn: Hskip'.
      * destruct (n - length (l ++ inc_vc t (C' + t) tmp1)); clarify.
        rewrite skipn_nil in *; clarify.
      * unfold inc_vc in Hskip'; destruct (n - length l); clarify.
        { eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n1; clarify.
        destruct n1; clarify; [|rewrite skipn_nil in *; clarify].
        eapply v_not_C with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * clarify.
        exploit max_vc_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hmax; instantiate (1 := 1); simpl.
          eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        { eapply v_not_C with (v := (v, o))(t := t0); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + unfold wait_handler in Hn; rewrite skipn_app in Hn.
      destruct (skipn n (max_vc (C' + t0) (C' + t) zt tmp1 tmp2)) eqn: Hskip.
      * unfold inc_vc in Hn;
          destruct (n - length (max_vc (C' + t0) (C' + t) zt tmp1 tmp2));
          clarify.
        { eapply v_not_C with (v := (v, o))(t := n0); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n1; clarify.
        destruct n1; clarify; [|rewrite skipn_nil in *; clarify].
        eapply v_not_C with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * clarify.
        exploit max_vc_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { eapply v_not_C with (v := (v, o))(t := t0); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        { eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
Qed.

Definition state_suffix := Forall2 (fun (t1 t2 : tid * list instr) =>
  let (t, li) := t1 in fst t2 = t /\ exists n,
    n < length (instrument_instr (hd (Assign 0 (I 0)) li) t) /\
    snd t2 = skipn n (instrument li t)).


Lemma step_into_instruments1 : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hdistinct : distinct P1)
  G1 lo lc P1' G1' (Hsteps : exec_star (Some P1) G1 lo lc (Some P1') G1')
  Pa n (HPa : Pa = skipn n P1'),
  exists P', safe_locs P' /\ state_suffix P' Pa.
Proof.
  induction Pa; clarify.
  - repeat eexists; constructor.
  - destruct P1'; [rewrite skipn_nil in HPa; clarify|].
    exploit skipn_cons; eauto; intro.
    specialize (IHPa (S n)); use IHPa; destruct IHPa as (P' & ?).
    assert (In a (p :: P1')).
    { eapply skipn_in; setoid_rewrite <- HPa; simpl; auto. }
    destruct a as (t, li); destruct li.
    + exists ((t, []) :: P'); repeat split; constructor; clarify; eauto.
    + exploit step_into_instrument; eauto.
      intros (? & ? & ? & ? & n' & i' & li' & rest & ?).
      exists ((t, i' :: rest) :: P'); repeat split; constructor; clarify.
      exists n'; rewrite skipn_app.
      destruct (le_gt_dec (length (instrument_instr i' t)) n').
      { rewrite skipn_all in *; clarify. }
      rewrite not_le_minus_0; [clarsimp | omega].
Qed.

Corollary step_into_instruments : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hdistinct : distinct P1)
  G1 lo lc P1' G1' (Hsteps : exec_star (Some P1) G1 lo lc (Some P1') G1'),
  exists P', safe_locs P' /\ state_suffix P' P1'.
Proof.
  intros; eapply step_into_instruments1 with (n := 0); eauto.
Qed.

Lemma rel_inv' : forall t x P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') li li'
  (Hin : In (t, li ++ li') P) (Hin' : In (t, li') P') (Hrel : In (Rel t x) lc),
  In (Unlock x) li.
Proof.
  intros.
  exploit rel_inv; eauto; intros (li1 & li2 & Heq & ? & Hin2).
  exploit distinct_steps; eauto; intro.
  exploit distinct_in.
  { eauto. }
  { apply Hin'. }
  { eauto. }
  clarify.
  symmetry in Heq.
  rewrite split_app in Heq; exploit app_eq_inv_ge.
  { eauto. }
  { assert (length ((li1 ++ [Unlock x]) ++ li2) = length (li ++ skipn x0 li2))
      by (rewrite Heq; auto).
    repeat rewrite app_length in *; rewrite skipn_length in *; omega. }
  intros (? & _ & ?); subst.
  repeat rewrite in_app; simpl; auto.
Qed.
    
Lemma firstn_in : forall A n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
  induction n; clarify.
  destruct l; clarify.
Qed.

Lemma access_held : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  v o (Hv : v < zv) (Hmeta : ~meta_loc (v, o))
  (Hlock : good_lock (X + v, 0) P0') (Hvar : good_var v P0')
  m (Hinit : initialized m (X + v, 0)) (Hcon : consistent (m ++ lc0))
  t i' rest (Hin : In (t, i' :: rest) P)
  (Haccess : accesses i' = Some (v, o) \/ accesses i' = Some (R + v, o) \/
             accesses i' = Some (W + v, o)),
  can_read (m ++ lc0) (X + v, 0) (S t).
Proof.
  intros.
  exploit step_into_instrument; eauto.
  intros (Pl & ? & ? & ? & n & i0 & ? & ? & ? & ? & ? & Hstepsl & Hinl & Heq &
    ?); clarify.
  exploit bounded_sim; eauto; intro.
  exploit bounded_steps; eauto; intro Hbound.
  setoid_rewrite Forall_forall in Hbound; exploit Hbound; eauto; clarify.
  exploit distinct_steps; try apply Hstepsl; auto; intro.
  exploit access_v; eauto.
  { exploit forall_steps; try apply Hstepsl; eauto.
    setoid_rewrite Forall_forall; intro X; exploit X; eauto; intro Hi0.
    split; intro; subst; simpl in *.
    * inversion Hi0; clarify.
    * repeat rewrite Forall_app in Hi0; destruct Hi0 as ((_ & Hi0) & ?).
      inversion Hi0; clarify. }
  { destruct i0; auto; clarify.
    destruct n; clarify.
    exploit step_instr; try apply Hinl; eauto.
    { rewrite skipn_app, not_le_minus_0.
      setoid_rewrite Heq; simpl; auto.
      { intro; rewrite skipn_all in Heq; clarify. } }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hwait & ?); clarify.
    exploit exec_other_threads; try apply Hinl; eauto; intro.
    exploit in_split; eauto; clarify.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit exec_next; eauto; clarify.
    exploit bounded_steps; try apply Hstepsl; auto; intro.
    exploit bounded_steps; try eapply exec_minus_exec; eauto; intro Hbound'.
    setoid_rewrite Forall_forall in Hbound'; exploit Hbound'; eauto; clarify. }
  intros (? & ?); destruct n; [omega|].
  destruct i0; try contradiction; try destruct x6; clarify.
  - exploit step_instr; try apply Hinl; eauto.
    { rewrite skipn_app, not_le_minus_0.
      setoid_rewrite Heq; simpl; auto.
      { intro; rewrite skipn_all in Heq; clarify. } }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HX & ?); clarify.
    exploit exec_other_threads; try apply Hinl; eauto; intro.
    exploit in_split; eauto; clarify.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit exec_next; eauto; clarify.
    rewrite split_app in Hcon; repeat rewrite app_assoc in Hcon.
    exploit lock_hold; try apply Hcon.
    { instantiate (1 := X' + v).
      repeat rewrite <- app_assoc.
      eapply init_steps; auto.
      repeat (rewrite Forall_app; split).
      * eapply prog_steps; eauto.
      * eapply prog_steps, exec_minus_exec; eauto.
      * constructor; simpl; auto. }
    { apply can_read_arwritten.
      eapply consistent_app_SC; eauto. }
    { eapply prog_steps; eauto. }
    { exploit forall_steps; try apply Hlock; try apply Hstepsl; intro.
      exploit forall_steps; try eapply exec_minus_exec; eauto; intro.
      exploit forall_step; eauto; intro.
      eapply good_lock_ops; eauto. }
    repeat rewrite <- app_assoc; clarify.
    exploit distinct_step; eauto; intro.
    exploit rel_inv'; eauto.
    { instantiate (1 := firstn n _).
      setoid_rewrite <- (firstn_skipn n ((hb_check _ _ _ _ _ ++ _) ++ _)).
      rewrite Heq, <- app_assoc; simpl; apply split_in. }
    repeat rewrite firstn_app, in_app; intros [[? | ?] | Hin'].
    + exploit firstn_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit firstn_in; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2 ++
        move (C' + t, t) (R' + v, t) tmp1)) eqn: Hn; setoid_rewrite Hn in Hin';
        clarify.
      destruct n1; clarify.
      rewrite skipn_all in Heq; [clarify|].
      rewrite app_length; simpl.
      clear - Hn.
      erewrite <- Nat.sub_add.
      setoid_rewrite Hn.
      rewrite plus_comm; apply plus_le_compat_r; omega.
      { omega. }
  - exploit step_instr; try apply Hinl; eauto.
    { rewrite skipn_app, not_le_minus_0.
      setoid_rewrite Heq; simpl; auto.
      { intro; rewrite skipn_all in Heq; clarify. } }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HX & ?); clarify.
    exploit exec_other_threads; try apply Hinl; eauto; intro.
    exploit in_split; eauto; clarify.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit exec_next; eauto; clarify.
    rewrite split_app in Hcon; repeat rewrite app_assoc in Hcon.
    exploit lock_hold; try apply Hcon.
    { instantiate (1 := X' + v).
      repeat rewrite <- app_assoc.
      eapply init_steps; auto.
      repeat (rewrite Forall_app; split).
      * eapply prog_steps; eauto.
      * eapply prog_steps, exec_minus_exec; eauto.
      * constructor; simpl; auto. }
    { apply can_read_arwritten.
      eapply consistent_app_SC; eauto. }
    { eapply prog_steps; eauto. }
    { exploit forall_steps; try apply Hlock; try apply Hstepsl; intro.
      exploit forall_steps; try eapply exec_minus_exec; eauto; intro.
      exploit forall_step; eauto; intro.
      eapply good_lock_ops; eauto. }
    repeat rewrite <- app_assoc; clarify.
    exploit distinct_step; eauto; intro.
    exploit rel_inv'; eauto.
    { instantiate (1 := firstn n _).
      setoid_rewrite <- (firstn_skipn n ((hb_check _ _ _ _ _ ++ _) ++ _)).
      rewrite Heq, <- app_assoc; simpl; apply split_in. }
    repeat rewrite firstn_app, in_app; intros [[? | [? | ?]] | Hin'].
    + exploit firstn_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit firstn_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit firstn_in; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2 ++
        hb_check (R' + v) (C' + t) zt tmp1 tmp2 ++
        move (C' + t, t) (W' + v, t) tmp1)) eqn: Hn; setoid_rewrite Hn in Hin';
        clarify.
      destruct n1; clarify.
      rewrite skipn_all in Heq; [clarify|].
      rewrite app_length; simpl.
      clear - Hn.
      erewrite <- Nat.sub_add.
      setoid_rewrite Hn.
      rewrite plus_comm; apply plus_le_compat_r; omega.
      { omega. }
Qed.

Lemma protect_held : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  v (Hv : fst v < zv) (Hmeta : ~meta_loc v)
  (Hlock : good_lock (X + fst v, 0) P0') (Hvar : good_var (fst v) P0')
  m (Hinit : initialized m (X + fst v, 0))
  t (Hheld : can_read (m ++ lc0) (X + fst v, 0) (S t))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  (Hno_lock : Forall (fun a => a <> Rel t (X + fst v)) lc)
  (Hcon : consistent (m ++ lc0 ++ lc)),
  Forall (fun a => ~v_access v a /\ loc_of a <> (X + fst v, 0))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; clarify.
  specialize (IHHsteps' _ eq_refl).
  rewrite filter_app, Forall_app; clarify.
  rewrite Forall_forall; repeat intro.
  rewrite <- exec_rev in Hsteps'.
  rewrite app_assoc in H; exploit lock_hold; try apply H; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { eapply prog_steps; eauto. }
  { exploit forall_steps; try apply Hlock; eauto; intro.
    eapply good_lock_ops; eauto. }
  intros [Hheld' | ?].
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  exploit protect_self; eauto.
  { rewrite <- app_assoc in Hheld'; auto. }
  { eapply exec_step'; eauto.
    * apply exec_refl.
    * rewrite app_nil_r; auto. }
  { repeat rewrite <- app_assoc in *; auto. }
  intro Hlocked; destruct c; clarify.
  inversion Hlocked; clarify.
  assert (Forall (fun a => a <> Acq t0 (X + fst v)) [x]).
  { constructor; auto; intro; clarify. }
  exploit exec_ops; eauto.
  simpl; unfold beq; intro Hthread; inversion Hthread; clarify.
  destruct P''; [|inversion Hexec'; clarify].
  intro Haccess.
  exploit step_thread'; eauto; intros (i & ? & Hin' & ?); clarify.
  assert (exists o, ~meta_loc (fst v, o) /\ (accesses i = Some (fst v, o) \/
    accesses i = Some (R + fst v, o) \/ accesses i = Some (W + fst v, o)))
    as (o' & Hmeta' & Haccess').
  { exploit distinct_steps; eauto; intro Hdistinct'.
    generalize (exec_accesses Hdistinct' Hexec' _ _ Hin'); intro Hloc.
    destruct Haccess as [? | [? | ?]].
    * rewrite Hloc in *; destruct v; eauto.
    * clarify; rewrite Hloc in *; eauto.
    * clarify; rewrite Hloc in *; eauto. }
  rewrite <- app_assoc in *.
  exploit access_held; eauto; intro.
  exploit can_read_unique.
  { apply H. }
  { do 2 (eapply init_steps, prog_steps; eauto). }
  { apply Hheld'. }
  { eauto. }
  intro Heq; inversion Heq; unfold beq, negb in cond; clarify.
  { rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto. }
Qed.

Lemma L_access : forall i1 i t (Ht : t < zt)
  (Hsafe : safe_instr i) (Hi : match i with Wait u => u < zt | _ => True end)
  (His : In i1 (instrument_instr i t))
  l (Hv : l < zl) (Hv2 : ~meta_loc (l, 0))
  o (Haccess : accesses i1 = Some (L + l, o)),
  match i with Lock p => p = l | Unlock p => p = l | _ => False end.
Proof.
  destruct i; try destruct x; clarify; repeat rewrite in_app in *.
  - destruct His as [? | [[? | ?] | ?]]; clarify.
    + exploit Hmetalocs_disjoint_LX; eauto.
    + exploit hb_check_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * exploit Hmetalocs_disjoint_LW; eauto.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + destruct H; clarify.
      * eapply Hmetalocs_disjoint_CL; eauto.
      * eapply Hmetalocs_disjoint_LR; eauto.
    + destruct H; clarify.
      * contradiction Hsafe1; apply L_meta; auto.
      * eapply Hmetalocs_disjoint_LX; eauto.
  - destruct His as [? | [[? | [? | ?]] | ?]]; clarify.
    + exploit Hmetalocs_disjoint_LX; eauto.
    + exploit hb_check_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * exploit Hmetalocs_disjoint_LW; eauto.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + exploit hb_check_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * exploit Hmetalocs_disjoint_LR; eauto.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + destruct H; clarify.
      * eapply Hmetalocs_disjoint_CL; eauto.
      * eapply Hmetalocs_disjoint_LW; eauto.
    + destruct H; clarify.
      * contradiction Hsafe1; apply L_meta; auto.
      * eapply Hmetalocs_disjoint_LX; eauto.
  - destruct His; clarify.
    + contradiction Hsafe1; apply L_meta; auto.
    + exploit max_vc_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * eapply plus_reg_l; eauto.
      * destruct H1; clarify; exploit Hmetalocs_disjoint_CL; try apply H2;
          eauto; contradiction.
  - setoid_rewrite in_app in His; destruct His as [[? | ?] | ?]; clarify.
    + exploit set_vc_instrs; eauto; intros [? [? [? | ?]]]; clarify.
      * exploit Hmetalocs_disjoint_CL; try apply H2; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + destruct H as [? | [? | ?]]; clarify; exploit Hmetalocs_disjoint_CL;
        eauto; contradiction.
    + contradiction Hsafe1; apply L_meta; auto.
  - setoid_rewrite in_app in His; destruct His as [[? | ?] | ?]; clarify.
    + exploit max_vc_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * eapply Hmetalocs_disjoint_CL with (t := t0); eauto.
      * destruct H1; clarify; eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + destruct H as [? | [? | ?]]; clarify; eapply Hmetalocs_disjoint_CL; eauto.
  - setoid_rewrite in_app in His; destruct His; clarify.
    + exploit max_vc_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
      * destruct H1; clarify; eapply Hmetalocs_disjoint_CL with (t := t0);
          eauto.
    + destruct H; clarify; eapply Hmetalocs_disjoint_CL; eauto.
Qed.

Definition good_unlock l li := forall i, nth_error li i = Some (Unlock l) ->
  exists j, j < i /\ nth_error li j = Some (Lock l) /\
  forall k, j < k < i -> nth_error li k <> Some (Unlock l).

Definition good_unlocks l := instr_rect'' (fun _ => Prop) _ (fun _ => True)
  (fun _ li r => good_unlock l li /\ r) True (fun _ _ r1 r2 => r1 /\ r2).

Lemma good_unlocks_list_iff : forall x li, instr_list_rect _ _ (fun _ => True)
  (fun _ li r => good_unlock x li /\ r) True (fun _ _ r1 r2 => r1 /\ r2) li <->
  Forall (good_unlocks x) li.
Proof.
  unfold good_unlocks; induction li; split; clarify.
  - constructor; auto.
    apply IHli; auto.
  - inversion H; clarify; apply IHli; auto.
Qed.

Definition well_locked l (P : state) :=
  Forall (fun e => good_unlock l (snd e) /\ Forall (good_unlocks l) (snd e)) P.

Lemma well_locked_spawn : forall l P G lo lc P' G'
  (Hwell_locked : well_locked l P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') t li (Hin : In (t, li) P')
  u li' (Hspawn : In (Spawn u li') li),
  good_unlock l li' /\ Forall (good_unlocks l) li'.
Proof.
  intros ?????????; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - setoid_rewrite Forall_forall in Hwell_locked; exploit Hwell_locked; eauto;
      intros (? & Hgood).
    rewrite Forall_forall in Hgood; exploit Hgood; eauto; clarify.
    unfold good_unlocks in *; clarify.
    rewrite (good_unlocks_list_iff l) in *; auto.
  - specialize (IHHsteps P0); clarify.
    specialize (IHHsteps _ eq_refl).
    rewrite <- exec_rev in Hsteps.
    exploit exec_result; eauto.
    intros (Pa & i & li2 & Pb & v & ? & Hresult).
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi; 
      clarify.
    rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Hin as [? | [? | [? | ?]]]; eauto; clarify.
    + exploit IHHsteps; eauto.
      simpl; eauto.
    + destruct o0; clarify.
      destruct i; clarify.
      exploit IHHsteps.
      { eauto. }
      { simpl; eauto. }
      intros (? & Hgood).
      rewrite Forall_forall in Hgood; exploit Hgood; eauto; clarify.
      unfold good_unlocks in *; clarify.
      rewrite (good_unlocks_list_iff l) in *; auto.
Qed.        

Lemma well_locked_steps : forall l P G lo lc P' G'
  (Hwell_locked : well_locked l P) (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') t li (Hin : In (t, li) P'),
  exists P1 G1 lo1 lc1 lo2 lc2 li1, exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t, li1) P1 /\ good_unlock l li1 /\ Forall (good_unlocks l) li1 /\
    exec_star (Some P1) G1 lo2 lc2 (Some P') G' /\ lo = lo1 ++ lo2 /\
    lc = lc1 ++ lc2.
Proof.
  intros until t; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - do 8 eexists; try apply exec_refl.
    split; eauto.
    setoid_rewrite Forall_forall in Hwell_locked; exploit Hwell_locked; eauto;
      clarify.
    apply exec_refl.
  - specialize (IHHsteps P0); clarify.
    specialize (IHHsteps _ eq_refl).
    rewrite <- exec_rev in Hsteps.
    exploit exec_result; eauto.
    intros (Pa & i & li' & Pb & v & ? & Hresult).
    destruct (instr_result t0 i (G' t0) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi; 
      clarify.
    rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Hin as [? | [? | [? | ?]]].
    + exploit IHHsteps; eauto; intros (P1 & ?); clarify.
      exists P1; do 7 eexists; eauto.
      split; eauto; clarify.
      split; [eapply exec_step_inv; eauto|].
      repeat rewrite <- app_assoc; auto.
    + clarify.
      exploit IHHsteps; eauto; intros (P1 & ?); clarify.
      exists P1; do 7 eexists; eauto.
      split; eauto; clarify.
      split; [eapply exec_step_inv; eauto|].
      repeat rewrite <- app_assoc; auto.
    + destruct o0; clarify.
      exists (Pa ++ (t0, li') :: (t, li) :: Pb); do 7 eexists.
      { eapply exec_step_inv; eauto. }
      split; [rewrite in_app; clarify|].
      destruct i; clarify.
      exploit well_locked_spawn; eauto.
      { rewrite in_app; clarify. }
      { simpl; eauto. }
      clarify.
      split; [apply exec_refl|].
      repeat rewrite app_nil_r; auto.
    + exploit IHHsteps; eauto; intros (P1 & ?); clarify.
      exists P1; do 7 eexists; eauto.
      split; eauto; clarify.
      split; [eapply exec_step_inv; eauto|].
      repeat rewrite <- app_assoc; auto.
Qed.

(* Replace the unprimed with this. *)
Lemma step_invariant' : forall P G lo lc P' G' (I : state -> Prop)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (HI : I P')
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hdistinct : distinct P)
  (HnotI : forall P (Hdistinct : distinct P) n (Hn : n < length li1)
                  (Ht : In (t, skipn n li1 ++ li2) P), ~I P),
  exists P'' G'' lo1 lc1 lo2 lc2, exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    In (t, li2) P'' /\ exec_star (Some P'') G'' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros; destruct li1.
  { exists P, G, [], [], lo, lc; repeat split; clarify; apply exec_refl. }
  remember (Some P) as S; remember (Some P') as S';
    generalize dependent li2; generalize dependent li1; revert i;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  { specialize (HnotI _ Hdistinct 0); clarify. }
  destruct P'; [|inversion Hsteps; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHsteps _ eq_refl Hdistinct' _ eq_refl); clarify.
  destruct (eq_dec t t0); subst.
  - exploit step_thread; eauto; intros (? & ? & ? & Ht'); clarify.
    destruct li1; clarify.
    + exists s, G', (opt_to_list o), (opt_to_list c), lo, lc; clarify.
      eapply exec_step'; [eauto | apply exec_refl | clarsimp | clarsimp].
    + specialize (IHHsteps _ _ _ Ht'); use IHHsteps.
      destruct IHHsteps as (Pa & Ga & lo1 & lc1 & lo2 & lc2 & ?).
      exists Pa, Ga, (opt_to_list o ++ lo1), (opt_to_list c ++ lc1), lo2, lc2;
        clarsimp.
      eapply exec_step; eauto.
      { apply (HnotI _ Hdistinct0 (S n)); auto. }
  - exploit exec_other_thread; eauto; intro Hin.
    specialize (IHHsteps _ _ _ Hin HnotI);
      destruct IHHsteps as (Pa & Ga & lo1 & lc1 & lo2 & lc2 & ?).
    exists Pa, Ga, (opt_to_list o ++ lo1), (opt_to_list c ++ lc1), lo2, lc2;
      clarsimp.
    eapply exec_step; eauto.
Qed.

Lemma critical_section' : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hdistinct : distinct P) m (Hinit : initialized m (x, 0))
  (Hcon : consistent (m ++ lc))
  t li0 li1 li2 (HP : In (t, li0 ++ Lock x :: li1 ++ li2) P)
  (HP' : In (t, li2) P'),
  In (Unlock x) li1 \/ can_read (m ++ lc) (x, 0) (S t).
Proof.
  intros.
  exploit step_invariant'; eauto.
  { repeat intro.
    exploit distinct_in.
    { eauto. }
    { apply Ht. }
    { eauto. }
    intro Heq; exploit app_nil_inv.
    { rewrite split_app, app_assoc in Heq; eauto. }
    rewrite <- app_assoc; intro.
    destruct (skipn n li0); clarify. }
  intros (? & ? & ? & ? & ? & ? & Hsteps0 & Hlock' & ?); clarify.
  exploit forall_steps; try apply Hsteps0; eauto; intro.
  exploit distinct_steps; try apply Hsteps0; eauto; intro.
  rewrite app_assoc in Hcon.
  exploit critical_section; try apply Hlock'; try apply Hcon; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { instantiate (1 := length li1); rewrite skipn_app, skipn_all, minus_diag;
      auto. }
  rewrite firstn_app, firstn_length, minus_diag, app_nil_r, <- app_assoc;
    auto.
Qed.

Lemma exec_keep' : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P) li' (Hin' : In (t, li') P'),
  exists n, li' = skipn n li.
Proof.
  intros; exploit exec_keep; eauto; clarify.
  exploit distinct_steps; eauto; intro.
  exploit distinct_in; [eauto | apply Hin' | eauto | clarify; eauto].
Qed.

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

(* With well-locked programs, if we're up to an unlock we should know we hold
   the lock. *)
Lemma unlock_locked : forall P0 l (Hdistinct : distinct P0)
  (Hlock : good_lock (l, 0) P0) (Hlock' : well_locked l P0)
  G0 lo lc P G (Hsteps : exec_star (Some P0) G0 lo lc (Some P) G)
  t li1 li2 (Hin : In (t, li1 ++ Unlock l :: li2) P)
  (Hlocked : Forall (fun i => i <> Lock l) li1)
  m (Hinit : initialized m (l, 0)) (Hcon : consistent (m ++ lc)),
  can_read (m ++ lc) (l, 0) (S t).
Proof.
  intros until G; intro; rewrite exec_rev in Hsteps.
  remember (Some P0) as P1; remember (Some P) as P2; generalize dependent P;
    generalize dependent P0; induction Hsteps; clarify.
  - setoid_rewrite Forall_forall in Hlock'.
    exploit Hlock'; eauto; intros (Hgood & _).
    specialize (Hgood _ (nth_error_split _ _ _)).
    destruct Hgood as (j & ?); clarify.
    rewrite nth_error_app in *; clarify.
    exploit nth_error_in; eauto; intro.
    rewrite Forall_forall in Hlocked; exploit Hlocked; eauto; contradiction.
  - specialize (IHHsteps P0); clarify.
    specialize (IHHsteps _ eq_refl).
    exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto; intro.
    rewrite <- exec_rev in Hsteps.
    assert (can_read (m ++ lc) (l, 0) (S t0) ->
      can_read (m ++ lc ++ opt_to_list c) (l, 0) (S t0)).
    { intro; exploit lock_hold; try apply Hcon; eauto.
      { eapply init_steps, prog_steps; eauto. }
      { eapply prog_step; eauto. }
      { exploit forall_steps; eauto; intro.
        eapply good_lock_ops; eauto.
        eapply exec_step'; eauto.
        * apply exec_refl.
        * rewrite app_nil_r; auto. }
      rewrite <- app_assoc; intro Hrel; clarify.
      destruct c; clarify.
      destruct i; clarify.
      exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin |
        clarify].
      exploit well_locked_steps; eauto.
      { rewrite in_app; clarify. }
      intros (? & ? & ? & ? & ? & ? & ? & ? & ? & Hgood & ? & Hsteps0 & ?);
        clarify.
      exploit exec_keep'; try apply Hsteps0; eauto.
      { eapply distinct_steps; [apply Hdistinct | eauto]. }
      { rewrite in_app; clarify. }
      intros (n & Hskip).
      specialize (Hgood (S (length li1) + n)).
      rewrite <- skipn_nth, <- Hskip in Hgood; simpl in Hgood.
      use Hgood; [|apply nth_error_split].
      destruct Hgood as (j & ? & Hj & Hk); clarify.
      destruct (le_dec n j).
      { rewrite <- (Nat.sub_add n j) in Hj; auto.
        rewrite <- skipn_nth, <- Hskip in Hj.
        destruct (j - n) eqn: Hminus; clarify.
        rewrite nth_error_app in Hj; destruct (lt_dec n0 (length li1));
          [|omega].
        exploit nth_error_in; eauto; intro.
        rewrite Forall_forall in Hlocked; exploit Hlocked; eauto;
          contradiction. }
      specialize (Hk n); use Hk; [|omega].
      rewrite <- (plus_O_n n), <- skipn_nth, <- Hskip in Hk; clarify. }
    rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Hin as [? | [? | [? | ?]]]; clarify; eauto.
    + specialize (IHHsteps t0 (i :: li1) li2); clarify.
      destruct (instr_eq_dec i (Lock l)); clarify.
      rewrite app_assoc; apply can_read_arwritten; auto.
    + destruct o0; clarify.
      destruct i; clarify.
      exploit well_locked_spawn; eauto.
      { rewrite in_app; clarify. }
      { simpl; eauto. }
      intros (Hgood & _).
      specialize (Hgood (length li1)); use Hgood; [|apply nth_error_split].
      destruct Hgood as (j & ? & Hj & Hk).
      rewrite nth_error_app in Hj; clarify.
      exploit nth_error_in; eauto; intro.
      rewrite Forall_forall in Hlocked; exploit Hlocked; eauto;
        contradiction.
Qed.

Transparent minus.
      
Lemma protect_l : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo lc P G
  (Hsteps : exec_star (Some P0') G0 lo lc (Some P) G)
  l (Hv : l < zl) (Hmeta : ~meta_loc (l, 0))
  (Hlock : good_lock (l, 0) P0') (Hlock' : well_locked l P0')
  m (Hinit : initialized m (l, 0)) (Hcon : consistent (m ++ lc))
  t i li (Hin : In (t, i :: li) P)
  (Haccess : exists o, accesses i = Some (L + l, o)),
  can_read (m ++ lc) (l, 0) (S t).
Proof.
  intros until m; intros ??; rewrite exec_rev in Hsteps.
  remember (Some P0') as P1; remember (Some P) as P2; generalize dependent P;
    generalize dependent P0'; induction Hsteps; clarify.
  - exploit in_split; eauto; clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hrest & ?).
    inversion Hrest as [|(?, li') Hi]; inversion Hi; clarify.
    destruct li'; clarify.
    setoid_rewrite Forall_app in Hsafe; clarify.
    inversion Hsafe2 as [|?? Hsafe_i]; inversion Hsafe_i as [|?? Hsafei ?];
      clarify.
    exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
    + rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      exploit Hmetalocs_disjoint_CL; eauto; clarify.
    + contradiction Hsafei1; apply L_meta; auto.
    + exploit Hmetalocs_disjoint_LX; eauto; clarify.
  - rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto; clarify.
    specialize (IHHsteps P0'); clarify.
    specialize (IHHsteps _ eq_refl).
    exploit exec_result; eauto; intros (Pa & i' & li' & Pb & v' & ? & Hresult).
    rewrite <- exec_rev in Hsteps.
    destruct (eq_dec t0 t).
    + subst.
      exploit step_into_instrument; eauto.
      { rewrite in_app; clarify. }
      intros (? & ? & ? & ? & n' & i2 & li2 & rest & ? & ? & ? & ? & Hi2 & ? &
        ? & ? & Hsafe_i & ?); clarify.
      exploit bounded_sim; eauto; intro.
      exploit bounded_steps; eauto; setoid_rewrite Forall_app.
      intros [? Ht']; inversion Ht'; clarify.
      exploit step_thread; eauto.
      { eapply distinct_steps; eauto. }
      { rewrite in_app; clarify. }
      clarify.
      exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit distinct_in.
      { eauto. }
      { apply Hin. }
      { eauto. }
      intro Heq.
      destruct li2; clarify.
      { destruct rest; clarify.
        inversion Hsafe_i as [|?? Hsafei]; subst.
        exploit L_access; eauto.
        { destruct i0; auto; clarify. }
        { generalize (instrument_nonnil i0 t);
            destruct (instrument_instr i0 t); clarify. }
        destruct i0; try contradiction; clarify.
        * contradiction Hmeta; rewrite H11; apply L_meta; auto.
        * destruct zt; clarify.
          exploit Hmetalocs_disjoint_CL; eauto; contradiction. }
      assert (distinct x0).
      { eapply distinct_steps; [|eauto]; auto. }
      assert (S n' - length (instrument_instr i2 t) = 0) as Hn'.
      { destruct (lt_dec n' (length (instrument_instr i2 t))); [omega|].
        rewrite skipn_all in H2; [inversion H2 | simpl; omega]. }
      exploit L_access; eauto.
      { destruct i2; auto.
        exploit step_instr; try apply Hi2.
        { auto. }
        { eapply exec_step_inv; eauto. }
        { instantiate (1 := n'); rewrite skipn_app.
          simpl in Hn'; rewrite Hn'.
          simpl; erewrite skipn_cons; [|apply H2]; auto. }
        intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hwait & ?).
        exploit exec_other_threads; try apply Hi2; eauto; intro.
        exploit distinct_steps; [|eapply exec_minus_exec; eauto|]; auto.
        exploit in_split; eauto; clarify.
        inversion Hwait; subst; exploit distinct_thread; eauto; clarify.
        exploit bounded_steps; try apply H1; auto; intro.
        exploit bounded_steps; [|eapply exec_minus_exec; eauto|]; auto.
        setoid_rewrite Forall_forall; intro Hbound; exploit Hbound; eauto;
          clarify. }
      { eapply skipn_in.
        setoid_rewrite H2; simpl; auto. }
      destruct i2; try contradiction; intro; subst; simpl in *.
      * exploit forall_steps; try apply H1; eauto; intro.
        rewrite <- app_assoc, <- app_assoc, app_assoc in Hcon.
        exploit critical_section; try apply Hcon; eauto.
        { eapply exec_step_inv; eauto. }
        { eapply init_steps, prog_steps; eauto. }
        { instantiate (1 := n').
          exploit skipn_cons; eauto; intro Heq.
          rewrite skipn_app, Heq, Hn'; simpl; auto. }
        repeat rewrite <- app_assoc; intro Hunlock; clarify.
        rewrite firstn_app, Hn' in Hunlock.
        rewrite in_app in Hunlock; clarify.
        exploit firstn_in; eauto; intro.
        exploit max_vc_instrs; eauto; clarify.
      * rewrite app_length, Nat.add_1_r in Hn'; simpl in Hn'.
        rewrite <- app_assoc; eapply unlock_locked; try apply Hlock.
        { auto. }
        { auto. }
        { rewrite app_assoc; eapply exec_step_inv; eauto. }
        { rewrite skipn_app, Hn' in H2; simpl in H2.
          instantiate (2 := skipn 1 (skipn n' (unlock_handler t l zt tmp1)));
            simpl.
          destruct (skipn n' (unlock_handler t l zt tmp1)) eqn: Hskip;
            clarify.
          assert (In (t, (i0 :: li2) ++ instrument rest t) P1) as Hin by auto.
          rewrite <- H11, <- app_assoc in Hin; eauto. }
        { rewrite Forall_forall; intros.
          exploit skipn_in; eauto; intro.
          exploit skipn_in; eauto; intro Hin'.
          setoid_rewrite in_app in Hin'; intro; destruct Hin'; clarify.
          exploit set_vc_instrs; eauto; clarify. }
        { auto. }
        { repeat rewrite <- app_assoc in Hcon; auto. }
    + destruct (instr_result t i' (G' t) v') as [((((?, ?), ?), ?), ?)|]
        eqn: Hi'; clarify.
      assert (In (t0, i :: li) (Pa ++ (t, i' :: li') :: Pb) ->
        can_read (m ++ lc ++ opt_to_list c) (l, 0) (S t0)).
      { intro; exploit IHHsteps; eauto; intro Hhold.
        exploit lock_hold; try apply Hcon; try apply Hhold.
        { eapply init_steps, prog_steps; eauto. }
        { eapply prog_step; eauto. }
        { eapply good_lock_ops.
          * eapply forall_steps; eauto.
          * eapply exec_step'; try apply exec_refl; eauto; clarsimp. }
        rewrite <- app_assoc; clarify.
        destruct c; clarify.
        inversion Hexec'; clarify.
        contradiction n; auto. }
      rewrite in_app in *; clarify.
      destruct Hin; clarify.
      rewrite in_app in *; clarify.
      destruct o0; clarify.
      destruct i'; clarify.
      exploit spawn_instrumented; eauto.
      { rewrite in_app; clarify. }
      { clarify. }
      intros (? & ? & Hsafe_i).
      destruct x0; clarify.
      inversion Hsafe_i as [|?? Hsafei]; subst.
      exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
      * exploit bounded_sim; eauto; intro.
        exploit bounded_steps; eauto.
        setoid_rewrite Forall_app; intros [_ Ht'].
        inversion Ht' as [|?? [? Hi1]]; subst.
        inversion Hi1; unfold bounded_instr in *; clarify.
        exploit Hmetalocs_disjoint_CL; eauto; contradiction.
      * contradiction Hsafei1; apply L_meta; auto.
      * exploit Hmetalocs_disjoint_LX; eauto; contradiction.
Qed.

Lemma protect_l' : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  l (Hv : l < zl) (Hmeta : ~meta_loc (l, 0))
  (Hlock : good_lock (l, 0) P0') (Hlock' : well_locked l P0')
  m (Hinit : initialized m (l, 0))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  t (Hno_lock : Forall (fun a => a <> Acq t l) lc)
  (Hcon : consistent (m ++ lc0 ++ lc))
  a (Ha : In a lc) (Ht : thread_of a = t) (Haccess : fst (loc_of a) = L' + l),
  can_read (m ++ lc0) (l, 0) (S t).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock; clarify.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; intro.
  rewrite in_app in Ha; destruct Ha; [clarify; eauto|].
  exploit step_thread0; eauto; intros (? & ? & Hin).
  exploit distinct_steps; eauto; intro.
  rewrite <- exec_rev in Hsteps'; exploit distinct_steps; eauto;
    intro Hdistinct'.
  generalize (exec_accesses Hdistinct' Hexec' _ _ Hin); intro Hloc.
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  destruct c; clarify; inversion Hno_lock2; clarify.
  exploit forall_steps; eauto; intro.
  exploit protect_l; eauto.
  { setoid_rewrite <- Hloc.
    destruct (loc_of a); eauto. }
  rewrite app_assoc; intro Hheld.
  exploit lock_hold'; try apply Hheld.
  - eapply init_steps, prog_steps; eauto.
  - rewrite <- app_assoc; auto.
  - eapply prog_steps; eauto.
  - eapply good_lock_ops; [|eauto].
    eapply forall_steps; [apply Hlock | eauto].
  - exploit exec_ops; eauto; simpl; intro Hthread.
    inversion Hthread; unfold beq in *; clarify.
    rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto; clarify.
Qed.

Lemma protect_lock : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  l (Hl : l < zl) (Hmeta : ~meta_loc (l, 0))
  (Hlock : good_lock (l, 0) P0') (Hlock2 : well_locked l P0')
  m (Hinit : initialized m (l, 0))
  t (Hheld : can_read (m ++ lc0) (l, 0) (S t))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  (Hno_lock : Forall (fun a => a <> Rel t l) lc)
  (Hcon : consistent (m ++ lc0 ++ lc)),
  Forall (fun a => forall o, loc_of a <> (L + l, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; clarify.
  specialize (IHHsteps' _ eq_refl).
  rewrite filter_app, Forall_app; clarify.
  rewrite Forall_forall; repeat intro.
  rewrite <- exec_rev in Hsteps'.
  rewrite app_assoc in H; exploit lock_hold; try apply H; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { eapply prog_steps; eauto. }
  { exploit forall_steps; eauto; intro.
    eapply good_lock_ops; eauto. }
  intros [Hheld' | ?].
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  exploit protect_self; eauto.
  { rewrite <- app_assoc in Hheld'; auto. }
  { eapply exec_step'; eauto.
    * apply exec_refl.
    * rewrite app_nil_r; auto. }
  { repeat rewrite <- app_assoc in *; auto. }
  intro Hlocked; destruct c; clarify.
  inversion Hlocked; clarify.
  assert (Forall (fun a => a <> Acq t0 l) [x]).
  { constructor; auto; intro; clarify. }
  exploit exec_ops; eauto.
  simpl; unfold beq; intro Hthread; inversion Hthread; clarify.
  exploit protect_l'; eauto.
  { eapply exec_step'; eauto.
    { apply exec_refl. }
    { rewrite app_nil_r; auto. } }
  { repeat rewrite <- app_assoc in *; auto. }
  { simpl; auto. }
  { rewrite H1; auto. }
  intro; exploit can_read_unique.
  { apply H. }
  { do 2 (eapply init_steps, prog_steps; eauto). }
  { apply Hheld'. }
  { rewrite <- app_assoc; eauto. }
  intro Heq; inversion Heq; unfold beq, negb in cond; clarify.
  { rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto. }
Qed.

Lemma instrument_incom : forall i i' l l' t,
  instrument_instr i t ++ l = instrument_instr i' t ++ l' -> i' = i /\ l' = l.
Proof.
  intro.
  eapply instr_ind' with (Q := fun l => forall l' t, instrument l t =
    instrument l' t -> l' = l)(i := i); clarify.
  - destruct i0; clarify; destruct i'; clarify; try (destruct x; clarify);
    try (destruct zt; clarify); try (destruct x0; clarify);
    try (repeat rewrite <- app_assoc in *; exploit app_eq_inv; eauto; clarify).
    repeat rewrite <- app_assoc in *; exploit app_eq_inv; eauto; clarify.
  - destruct i'; clarify; destruct zt; clarify; try (destruct x; clarify).
    repeat rewrite <- app_assoc in *; exploit app_eq_inv; eauto; clarify.
    exploit IHli; eauto; clarify.
  - destruct l'; clarify.
    exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
      clarify.
  - destruct l'; clarify.
    + exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
        clarify.
    + exploit IHi; eauto; clarify.
      exploit IHli; symmetry; eauto; clarify.
Qed.


Lemma removelast_in : forall A (l : list A) x, In x (removelast l) -> In x l.
Proof. induction l; clarify. Qed.

Lemma tl_in : forall A (l : list A) x, In x (tl l) -> In x l.
Proof. destruct l; clarify. Qed.

(* This should probably replace all other versions. *)
Lemma in_mops_set_vc'': forall n c vc1 vc2 vs t
  (Hin: In c (mops_set_vc vc1 vc2 n t vs)),
match c with
  | Read _ (x, o) _ => x = vc1 /\ o < n
  | Write _ (x, o) _ => x = vc2 /\ o < n
  | _ => False
end.
Proof.
  induction n; clarify.
  destruct vs; clarify.
  exploit IHn; eauto; destruct c; try destruct x; clarify.
Qed.

Lemma instrument_thread'' : forall P (Hsafe : safe_locs P) P1
  (Hsim : state_sim P P1) (Hdistinct : distinct P1)
  P1' G1 lo lc G1' (Hroot : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t o c t' n P1'' G' (Hstep : exec P1' G1' t o (Some c) P1'' G')
  (Hloc : loc_of c = (C' + t', n)) (Ht' : t' < zt),
  t' = t \/ exists P2 lo2 lc2 G2 i' n' rest lo2' lc2',
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G2 /\
    In (t, instrument_instr i' t ++ instrument rest t) P2 /\
    In (t, skipn n' (instrument_instr i' t) ++ instrument rest t) P1' /\
    n' < length (instrument_instr i' t) /\
    exec_star (Some P2) G2 lo2' lc2' (Some P1') G1' /\
    match i' with Spawn u _ => t' = u | Wait u => t' = u /\ In (u, []) P1'
      | _ => False end.
Proof.
  intros.
  exploit exec_result; eauto; intros (P1a & i & li & P1b & v & ? & Hresult);
    subst.
  exploit step_into_instrument; eauto.
  { rewrite in_app; clarify. }
  intros (? & ? & ? & ? & n' & i' & ? & ? & ? & ? & ? & ? & ? & Hi' & ?);
    clarify.
  assert (In i (instrument [i'] t)) as Hi.
  { simpl; rewrite app_nil_r; eapply skipn_in.
    eapply nth_error_in; setoid_rewrite Hi'.
    instantiate (1 := 0); simpl; eauto. }
  exploit distinct_steps; eauto; intro.
  exploit instrument_own; try apply Hi; eauto.
  { rewrite <- exec_accesses; try apply Hstep; clarify; eauto.
    rewrite in_app; clarify. }
  intros [? | (i1 & ?)]; clarify.
  right; exists x; repeat eexists; eauto.
  - setoid_rewrite Hi'; rewrite in_app; clarify.
  - destruct (le_lt_dec (length (instrument_instr i1 t)) n'); auto.
    rewrite skipn_all in *; clarify.
  - destruct i1; clarify.
    destruct n'; clarify.
    exploit distinct_steps; try apply H0; auto; intro.
    exploit step_instr; eauto.
    { instantiate (1 := n'); rewrite skipn_app, Hi'.
      destruct (le_dec (length (wait_handler t t0 zt)) n').
      { rewrite skipn_all in Hi'; clarify. }
      destruct (n' - length (wait_handler t t0 zt)) eqn: Hminus; [|omega].
      rewrite in_app; simpl; auto. }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hminus' & Hwait & ?);
      clarify.
    exploit exec_other_threads; try apply Hminus'; eauto; intro.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit in_split; eauto; clarify.
    inversion Hwait; subst; exploit distinct_thread; eauto; clarify.
    exploit exec_keep; eauto.
    { eapply exec_step; eauto. }
    intros (? & ?); rewrite skipn_nil in *; auto.
Qed.

Lemma protect_spawn : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hl : u < zt)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc (Some P') G')
  (Hout : Forall (fun e => fst e <> u /\
    forall li, ~In (Spawn u li) (snd e)) P'),
  Forall (fun a => forall o, loc_of a <> (C + u, o)) lc.
Proof.
  intros until G'; intro.
  remember (Some P) as P1; remember (Some P') as P2; generalize dependent P';
    generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  exploit exec_result; eauto; intros (? & i & li & ? & v & ? & Hresult).
  destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  specialize (IHHsteps' _ eq_refl _ eq_refl).
  rewrite Forall_app in *; clarify.
  inversion Hout2 as [|?? [Hu1 Hu2] Hu']; rewrite Forall_app in *; clarify.
  assert (forall li', ~In (Spawn u li') (i :: li)) as Hout_i.
  { simpl; intro; intros [? | ?]; [clarify | exploit Hu2; eauto].
    inversion Hu'1; clarify. }
  use IHHsteps'; clarify.
  rewrite Forall_forall; intros.
  intro; destruct c; clarify.
  rewrite <- exec_rev in Hsteps'.
  exploit instrument_thread''; try apply Hexec'; eauto.
  { eapply exec_star_trans; eauto. }
  intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Hin & ? & Hsteps2 &
    Hop)]; clarify.
  exploit distinct_steps; try apply Hsteps; eauto; intro.
  exploit distinct_steps; try apply Hsteps'; eauto; intro.
  exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin |
    intro Heq].
  destruct i'; auto; clarify.
  - rewrite skipn_app in Heq.
    rewrite app_length in *; simpl in *.
    destruct (n' - length (spawn_handler t t0 zt)) eqn: Hminus; [|omega].
    assert (In (Spawn t0 ((fix f p t1 := match p with [] => []
      | ins :: inss => instrument_instr ins t1 ++ f inss t1 end) li0 t0))
      (i :: li)).
    { rewrite Heq, in_app, in_app; simpl; auto. }
    simpl in *; eapply Hout_i; eauto.
  - rewrite Forall_forall in *.
    rewrite in_app in Hop2; destruct Hop2; clarify.
    + exploit Hout1; eauto; clarify.
    + exploit Hu'2; eauto; clarify.
Qed.    

Lemma has_spawn : forall u li li', In (Spawn u li') li ->
  spawns_list u li > 0.
Proof.
  induction li; clarify.
  destruct H; clarify.
  - unfold spawns; simpl; rewrite (spawns_list_def u); clarify.
  - exploit IHli; eauto; omega.
Qed.

Lemma has_spawn_thread : forall u P e, In e P ->
  spawn_count u P >= spawns_list u (snd e).
Proof.
  induction P; clarify.
  destruct a, H; clarify; [omega|].
  exploit IHP; eauto; omega.
Qed.

Lemma protect_spawn' : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hl : u < zt)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P') li' (Hspawn : In (Spawn u li') li),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros until G'; intro.
  remember (Some P) as P1; remember (Some P') as P2; generalize dependent P';
    generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  specialize (IHHsteps' _ eq_refl _ eq_refl).
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite <- exec_rev in Hsteps'.
  rewrite filter_app, Forall_app; split.
  - rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps'.
    destruct Hin as [? | [? | [? | ?]]]; clarify; eauto.
    + eapply IHHsteps'; eauto.
      simpl; eauto.
    + destruct o0; clarify.
      destruct i; clarify.
      exploit protect_spawn; eauto.
      { generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
        generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
        specialize (Hspawns' u); rewrite spawn_count_app in Hspawns';
          simpl in Hspawns'.
        unfold spawns in Hspawns'; simpl in Hspawns';
          rewrite (spawns_list_def u) in Hspawns'.
        exploit has_spawn; eauto; intro.
        destruct (eq_dec t0 u); clarify; [omega|].
        rewrite Forall_forall; intros ? Hin; split.
        * intro; specialize (Hspawns'2 (snd x2)); destruct x2; clarify; omega.
        * intros ? Hin'.
          destruct (spawns_list u li); [omega|].
          simpl in *; rewrite <- plus_n_Sm in *.
          generalize (le_S_n _ _ Hspawns'1); intro.
          exploit has_spawn; eauto; intro.
          destruct (spawns_list u (snd x2)) eqn: Hn1; [omega|].
          rewrite in_app in Hin; simpl in Hin; destruct Hin as [? | [? | ?]].
          { exploit (has_spawn_thread u); eauto; setoid_rewrite Hn1; omega. }
          { clarify.
            destruct Hin' as [Hin' | ?]; [inversion Hin'; clarify|].
            exploit has_spawn; eauto; omega. }
          { exploit (has_spawn_thread u); eauto; setoid_rewrite Hn1; omega. } }
      apply Forall_filter.
  - rewrite Forall_forall; intros.
    destruct c; clarify; intro.
    generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
    generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
    generalize (safe_spawns_step Hspawns' Hexec'); intro Hspawns''.
    specialize (Hspawns'' u); clarify.
    exploit instrument_thread''; try apply Hexec'; eauto.
    { eapply exec_star_trans; eauto. }
    intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & Hsteps0 & ? & Hin2 & ?)].
    { subst; exploit Hspawns''2.
      { rewrite in_app; clarify. }
      exploit has_spawn; eauto; intros.
      exploit (has_spawn_thread t); eauto; simpl; omega. }
    destruct i'; clarify.
    + rewrite skipn_app in Hin2.
      rewrite app_length in *; simpl in *.
      assert (n' - length (spawn_handler t t1 zt) = 0) as Hzero by omega.
      rewrite Hzero in Hin2; simpl in Hin2.
      exploit distinct_steps; try apply Hsteps; auto; intro.
      exploit distinct_steps; try apply Hsteps'; auto; intro.
      exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin2
        | intro Heq].
      destruct (skipn n' (spawn_handler t t1 zt)) eqn: Hskip; clarify.
      rewrite spawn_count_app in Hspawns''1; simpl in Hspawns''1.
      repeat rewrite spawns_list_app in Hspawns''1; clarify.
      unfold spawns in Hspawns''1; simpl in Hspawns''1;
        rewrite (spawns_list_def t1) in Hspawns''1; clarify.
      do 2 ( rewrite <- plus_n_Sm in *; simpl in * ).
      generalize (le_S_n _ _ Hspawns''1); intro.
      assert (t0 <> t).
      { exploit exec_ops; eauto; simpl; intro Hx; inversion Hx; clarify.
        unfold negb, beq in *; clarify. }
      exploit has_spawn; eauto; intro.
      rewrite in_app in Hin; destruct Hin as [Hin | Hin]; clarify;
        generalize (has_spawn_thread t1 _ _ Hin); simpl; omega.
    + specialize (Hspawns''2 []); use Hspawns''2.
      exploit has_spawn; eauto; intro.
      generalize (has_spawn_thread t1 _ _ Hin); simpl; omega.
      { clear Hin Hin2; rewrite in_app in *; clarify; rewrite in_app; clarify. }
Qed.

Definition waits t := instr_rect'' (fun _ => nat) _
  (fun i => match i with Wait u => if eq_dec u t then 1 else 0 | _ => 0 end)
  (fun _ _ r => r) 0 (fun _ _ r1 r2 => r1 + r2).

Fixpoint waits_list t li :=
  match li with
  | [] => 0
  | i :: rest => waits t i + waits_list t rest
  end.

Lemma waits_list_def : forall t li, instr_list_rect (fun _ => nat) _
  (fun i => match i with Wait u => if eq_dec u t then 1 else 0 | _ => 0 end)
  (fun _ _ r => r) 0 (fun _ _ r1 r2 => r1 + r2) li =
   waits_list t li.
Proof. induction li; clarify. Qed.

Fixpoint wait_count t (P : state) :=
  match P with
  | [] => 0
  | (_, li) :: rest => waits_list t li + wait_count t rest
  end.

Definition safe_waits P := forall t, wait_count t P <= 1.

Lemma wait_count_app : forall t P1 P2, wait_count t (P1 ++ P2) =
  wait_count t P1 + wait_count t P2.
Proof.
  induction P1; clarify.
  destruct a; clarify.
  rewrite IHP1; omega.
Qed.

Lemma safe_waits_step : forall P (Hwaits : safe_waits P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), safe_waits P'.
Proof.
  intros; intro t'; specialize (Hwaits t'); inversion Hstep; clarify;
    rewrite wait_count_app in *; clarify;
    try solve [generalize (Hwaits2 li); rewrite in_app in *; clarify;
    eapply Hwaits2; rewrite in_app; clarify]; try omega.
  unfold waits in Hwaits; simpl in Hwaits;
    rewrite (waits_list_def t') in *; omega.
Qed.

Definition waiter t u := instr_rect'' _ (fun _ => tid -> Prop)
  (fun i => match i with Wait u' => fun t' => u' = u /\ t' = t
   | _ => fun _ => False end)
  (fun u _ r _ => r u) (fun _ => False) (fun _ _ r1 r2 t' => r1 t' \/ r2 t').

Lemma waiter_list_def : forall t u u' li t', waiter t u (Spawn u' li) t' <->
  Exists (fun i => waiter t u i u') li.
Proof.
  unfold waiter; induction li; split; clarify.
  - inversion H.
  - rewrite IHli in H; auto.
  - inversion H; clarify.
    rewrite IHli; auto.
Qed.

Definition t_waits t u P := exists e, In e P /\
  Exists (fun i => waiter t u i (fst e)) (snd e).

Lemma no_waiters : forall u i, waits u i = 0 -> forall t t', ~waiter t u i t'.
Proof.
  intros ??; eapply instr_ind' with (Q := fun l => waits_list u l = 0 ->
    forall t t', ~Exists (fun i => waiter t u i t') l)(i := i); clarify.
  - destruct i0; clarify.
    unfold waiter; unfold waits in *; intro; clarify.
  - unfold waits in *; clarify.
    rewrite (waits_list_def u) in *; rewrite (waiter_list_def t u); auto.
  - intro H; inversion H.
  - use IHi; [|omega].
    use IHli; [|omega].
    intro H1; inversion H1; [eapply IHi | eapply IHli]; eauto.
Qed.  

Corollary no_waiters_list : forall u li, waits_list u li = 0 ->
  forall t t', ~Exists (fun i => waiter t u i t') li.
Proof.
  induction li; clarify.
  { intro H; inversion H. }
  use IHli; [|omega].
  intro H1; inversion H1.
  - exploit no_waiters; eauto; omega.
  - eapply IHli; eauto.
Qed.

Lemma one_waiter : forall u i (Hsafe : waits u i <= 1) t', exists t,
  forall t1, waiter t1 u i t' -> t1 = t.
Proof.
  intros ??; eapply instr_ind' with (Q := fun l => waits_list u l <= 1 ->
    forall t', exists t, forall t1, Exists (fun i => waiter t1 u i t') l ->
    t1 = t) (i := i); clarify.
  - destruct i0; clarify; try solve [exists 0; clarify].
    exists t'; unfold waiter; clarify.
  - unfold waits in *; simpl in *; rewrite (waits_list_def u) in *; clarify.
    specialize (IHli u0); clarify.
    exists x; intros.
    rewrite (waiter_list_def t1 u) in *; auto.
  - exists 0; intros ? H1; inversion H1.
  - destruct (waits u i0) eqn: Hi; clarify.
    + specialize (IHli t'); clarify.
      exists x; intros ? H1; inversion H1; clarify.
      exploit no_waiters; eauto; contradiction.
    + use IHi; [|omega].
      specialize (IHi t'); clarify.
      exists x; intros ? H1; inversion H1; clarify.
      exploit no_waiters_list; eauto; omega.
Qed.      
    
Corollary one_waiter_list : forall u li (Hsafe : waits_list u li <= 1) t',
  exists t, forall t1, Exists (fun i => waiter t1 u i t') li -> t1 = t.
Proof.
  induction li; clarify.
  { exists 0; intros; inversion H. }
  destruct (waits u a) eqn: Ha; clarify.
  - specialize (IHli t'); clarify.
    exists x; intros ? H; inversion H; clarify.
    exploit no_waiters; eauto; contradiction.
  - generalize (one_waiter u a); intro H; clarify.
    use H; [|omega].
    specialize (H t'); clarify.
    exists x; intros ? H1; inversion H1; clarify.
    exploit no_waiters_list; eauto; omega.
Qed.  

Lemma safe_waits_cons : forall e P, safe_waits (e :: P) -> safe_waits P.
Proof.
  repeat intro.
  specialize (H t); clarify.
  destruct e; omega.
Qed.

Lemma no_waiters' : forall u P (Hnone : wait_count u P = 0) t, ~t_waits t u P.
Proof.
  induction P; unfold t_waits; repeat intro; clarify.
  destruct a; use IHP; [|omega].
  destruct H1; clarify.
  - exploit no_waiters_list; eauto; omega.
  - eapply IHP.
    unfold t_waits; eauto.
Qed.

Lemma one_waiter' : forall P (Hsafe : safe_waits P) u, exists t,
  forall t', t_waits t' u P -> t' = t.
Proof.
  induction P; unfold t_waits; clarify.
  { exists 0; clarify. }
  generalize (safe_waits_cons Hsafe); clarify.
  specialize (Hsafe u); simpl in Hsafe.
  destruct a.
  destruct (waits_list u l) eqn: Hl; clarify.
  - specialize (IHP u); clarify.
    exists x; clarify.
    destruct H01; clarify.
    + exploit no_waiters_list; eauto; contradiction.
    + apply IHP; unfold t_waits; eauto.
  - exploit (one_waiter_list u l); [omega|].
    instantiate (1 := t).
    intros (x & Hx); exists x; clarify.
    assert (wait_count u P = 0) by omega.
    exploit no_waiters'; eauto; [|contradiction].
    unfold t_waits; eauto.
Qed.

Lemma t_waits_step : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G')
  t' u (Hwait : t_waits t' u P'), t_waits t' u P.
Proof.
  unfold t_waits; clarify.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite in_app in Hwait1; simpl in Hwait1; rewrite in_app in Hwait1.
  setoid_rewrite in_app.
  destruct Hwait1 as [? | [? | [? | ?]]]; clarify; eauto.
  - do 2 eexists; eauto; clarify.
  - destruct o0; clarify.
    destruct i; clarify.
    do 2 eexists; eauto; clarify.
    constructor; rewrite (waiter_list_def t' u); auto.
Qed.    

Corollary t_waits_steps : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t u (Hwait : t_waits t u P'), t_waits t u P.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  exploit IHHsteps; eauto.
  eapply t_waits_step; eauto.
Qed.

Corollary unique_wait : forall P (Hsafe : safe_waits P) u, exists t,
  forall G lo lc P' G' (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t' li (Hwait : In (t', Wait u :: li) P'), t' = t.
Proof.
  intros.
  exploit one_waiter'; eauto; intros (t & Ht); exists t; clarify.
  exploit t_waits_steps; eauto.
  do 2 eexists; eauto; clarify.
  constructor; unfold waiter; clarify.
Qed.    
    
Lemma protect_wait : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0')
  (Hwaits : safe_waits P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hdone : In (u, []) P)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, Wait u :: li) P),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros until t.
  remember (Some P) as P1; remember (Some P') as P2; generalize dependent P';
    generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  specialize (IHHsteps' _ eq_refl Hdone _ eq_refl _ Hin).
  rewrite filter_app, Forall_app; clarify.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t0 i (G' t0) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite <- exec_rev in Hsteps'.
  rewrite Forall_forall; intros.
  destruct c; clarify; intro.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; try apply Hdone; eauto; intros (? & Hdone').
  rewrite skipn_nil in Hdone'; clarify.
  exploit instrument_thread''; try apply Hexec'; eauto.
  { eapply exec_star_trans; eauto. }
  { exploit bounded_sim; eauto; intro.
    exploit bounded_steps; eauto; intro Hu.
    setoid_rewrite Forall_forall in Hu; specialize (Hu _ Hdone); clarify. }
  intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Hin' & ?)].
  { exploit distinct_steps; eauto; intro; subst.
    exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify]. }
  destruct i'; clarify.
  - generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
    generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
    specialize (Hspawns' t1); clarify.
    specialize (Hspawns'2 []); clarify.
    rewrite skipn_app in Hin'.
    rewrite app_length in *; simpl in *.
    assert (n' - length (spawn_handler t0 t1 zt) = 0) as Hzero by omega.
    rewrite Hzero in Hin'; simpl in Hin'.
    generalize (has_spawn_thread t1 _ _ Hin'); simpl.
    repeat rewrite spawns_list_app; clarify.
    unfold spawns in *; clarify; rewrite (spawns_list_def t1) in *; omega.
  - assert (t0 <> t).
    { exploit exec_ops; eauto; simpl; intro Hx; inversion Hx; clarify.
      unfold negb, beq in *; clarify. }
    exploit unique_wait; eauto; intros (t' & Ht').
    exploit Ht'; try apply Hin; eauto; clarify.
    exploit Ht'; try apply H2; eauto.
Qed.

Definition lock_instr l := instr_rect'' (fun _ => Prop) _
  (fun i => match i with Lock m | Unlock m => m = l | _ => False end)
  (fun _ _ r => r) False (fun _ _ r1 r2 => r1 \/ r2).

Lemma lock_list_iff : forall x u li, lock_instr x (Spawn u li) <->
  Exists (lock_instr x) li.
Proof.
  unfold lock_instr; induction li; split; clarify.
  - inversion H.
  - apply Exists_cons_tl, IHli; auto.
  - inversion H; clarify.
    right; apply IHli; auto.
Qed.  

Definition locks x (P : state) := exists e, In e P /\
  Exists (lock_instr x) (snd e).

Corollary instr_in_step_rev : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G')
  t' li i (Hin : In (t', li) P') (Hi : In i li),
  (exists li', In (t', li') P /\ In i li') \/
  exists li', In (t, Spawn t' li :: li') P.
Proof.
  intros.
  exploit in_step_rev; eauto; intros [? | [? | ?]]; clarify; eauto.
  left; do 2 eexists; eauto; clarify.
Qed.
  
Lemma locks_steps : forall l P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (Hlocks : locks l P'),
  locks l P.
Proof.
  intros until G'; intro; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P; rewrite exec_rev in Hsteps;
    induction Hsteps; clarify.
  eapply IHHsteps; eauto.
  unfold locks; destruct Hlocks as ((?, ?) & ? & He).
  exploit in_step_rev; eauto; intros [? | [? | ?]]; clarify; eauto.
  - do 2 eexists; eauto.
    apply Exists_cons_tl; auto.
  - do 2 eexists; eauto.
    constructor; rewrite (lock_list_iff l); auto.
Qed.

Corollary locks_spec : forall l P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') t li (Hin : In (t, li) P')
  (Hlock : In (Lock l) li \/ In (Unlock l) li), locks l P.
Proof.
  intros; eapply locks_steps; eauto.
  do 2 eexists; eauto.
  rewrite Exists_exists; destruct Hlock; do 2 eexists; eauto;
    unfold lock_instr; clarify.
Qed.

(* remove? 
Lemma instrument_indep : forall P0 G0 t o c P G lo lc P1 G1 o' c' P2 G2 i rest
  (Hdistinct : distinct P0) P0' (Hsim : state_sim P0' P0)
  (Hsafe : safe_locs P0') (Hfresh : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
(*  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)*)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
(*!!  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0) !!*)
  (Hsafe_i : safe_instr i) (Hfresh_i : fresh tmp1 i /\ fresh tmp2 i)
  lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  (Ht1 : t < zt) (Hin : In (t, instrument_instr i t ++ rest) P1)
  (Hstep1 : exec P1 G1 t o c (Some P) G)
  (Hsteps : exec_star (Some P) G lo lc (Some P2) G2)
  P3 G3 (Hstep2 : exec P2 G2 t o' c' (Some P3) G3) (Hin' : In (t, rest) P3)
  m (Hcon : consistent (m ++ lc0 ++ opt_to_list c ++ lc ++ opt_to_list c'))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t)
            (opt_to_list c ++ lc ++ opt_to_list c')))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  exploit step_thread'; eauto; intros (i' & ? & Hin1 & ?).
  exploit distinct_steps; eauto; intro Hdistinct1.
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_steps; eauto; intro Hdistinct2.
  exploit distinct_step; eauto; intro Hdistinct3.
  exploit distinct_in.
  { eauto. }
  { eauto. }
  { apply Hin'. }
  intro; subst.
  assert (i' = last (instrument_instr i t) (Lock 0)); subst.
  { exploit exec_mono; try apply Hdistinct1.
    { eapply exec_step; eauto. }
    { eauto. }
    { eauto. }
    intros (n & Heq).
    exploit skipn_last; eauto; clarify; eauto. }
  exploit exec_thread'.
  { apply Hdistinct1. }
  { eauto. }
  { eauto. }
  { rewrite (app_removelast_last (Lock 0) (instrument_nonnil i t)) in Hin.
    rewrite <- app_assoc in Hin; eauto. }
  { auto. }
  intro Ht_steps.
  destruct i; try destruct x.
  - exploit step_thread; try apply Hstep1; eauto; clarify.
    exploit exec_keep; try apply Hsteps; eauto; clarify.
    exploit distinct_in.
    { apply Hdistinct1. }
    { apply Hin. }
    { eauto. }
    clarify; exploit skip_cons_neq; eauto; clarify.
  - rewrite removelast_length in Ht_steps; [|apply instrument_nonnil].
    exploit t_steps_load; try apply Ht_steps; eauto.
    intros (vs1 & vs2 & vt & v0 & Heq); rewrite app_assoc, Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    inversion Hstep1; subst; exploit distinct_thread; try apply Hdistinct1;
      eauto; clarify.
    rewrite split_app in Hin1; setoid_rewrite (split_app [] _ (Lock (X' + v)))
      in Hin1.
    repeat rewrite app_assoc in Hin1; rewrite last_snoc in Hin1.
    exploit protect_held; try apply Hsafe_i1; try apply Hsim; try apply Hsteps;
      auto.
    { eapply exec_step_inv; eauto. }
    { rewrite app_assoc; apply can_read_arwritten.
      eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
    { rewrite Forall_forall; repeat intro; subst.
      exploit rel_inv'; eauto.
      { rewrite in_app; clarify.
        right; rewrite <- app_assoc; simpl.
        rewrite split_app; eauto. }
      repeat rewrite in_app; intros [[? | ?] | ?]; clarify.
      exploit hb_check_instrs; eauto; clarify. }
    { eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
    repeat rewrite Forall_forall; intros Haccess ? Ha;
      specialize (Haccess _ Ha).
    constructor; clarify.
    exploit instrument_own_thread; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite in_app; clarify. }
    { clarify. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x1); eauto.
    + repeat constructor; simpl; intro Heq; rewrite <- Heq in *; clarify.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
  - rewrite removelast_length in Ht_steps; [|apply instrument_nonnil].
    simpl in Hfresh_i; destruct Hfresh_i.
    exploit t_steps_store; try apply Ht_steps; eauto.
    intros (vs1 & vs2 & vs3 & v0 & Heq); rewrite app_assoc, Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    inversion Hstep1; subst; exploit distinct_thread; try apply Hdistinct1;
      eauto; clarify.
    rewrite split_app in Hin1; setoid_rewrite (split_app [] _ (Lock (X' + v)))
      in Hin1.
    repeat rewrite app_assoc in Hin1; rewrite last_snoc in Hin1.
    exploit protect_held; try apply Hsafe_i1; try apply Hsim; try apply Hsteps;
      auto.
    { eapply exec_step_inv; eauto. }
    { rewrite app_assoc; apply can_read_arwritten.
      eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
    { rewrite Forall_forall; repeat intro; subst.
      exploit rel_inv'; eauto.
      { rewrite in_app; clarify.
        right; rewrite <- app_assoc; simpl.
        rewrite split_app; eauto. }
      repeat rewrite in_app; intros [[? | [? | ?]] | ?]; clarify;
        exploit hb_check_instrs; eauto; clarify. }
    { eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
    repeat rewrite Forall_forall; intros Haccess ? Ha;
      specialize (Haccess _ Ha).
    constructor; clarify.
    exploit instrument_own_thread; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite in_app; clarify. }
    { clarify. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    repeat rewrite Forall_app; repeat split.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x1); eauto.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x1); eauto.
    + repeat constructor; simpl; intro Heq; rewrite <- Heq in *; clarify.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
  - rewrite removelast_length in Ht_steps; [|apply instrument_nonnil].
    exploit t_steps_lock; try apply Ht_steps; eauto.
    intros (vs1 & vs2 & Heq); rewrite app_assoc, Heq; clear Heq.
    simpl in Hin.
    generalize (in_split _ _ Hin); clarify.
    inversion Hstep1; subst; exploit distinct_thread; try apply Hdistinct1;
      eauto; clarify.
    specialize (Hlocks m0); use Hlocks.
    exploit protect_self; try apply Hsim; try apply Hsteps; eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite app_assoc; apply can_read_arwritten.
      eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
    { rewrite Forall_forall; repeat intro; subst.
      exploit rel_inv'; eauto.
      { rewrite in_app; clarify.
        right; left; rewrite split_app.
        assert (lock_handler t m0 zt <> []) by (destruct zt; clarify).
        rewrite last_cons, <- app_removelast_last; auto. }
      intro; exploit removelast_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
    exploit protect_lock; try apply Hsim; try apply Hsteps; eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite app_assoc; apply can_read_arwritten.
      eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
    { rewrite Forall_forall; repeat intro; subst.
      exploit rel_inv'; eauto.
      { rewrite in_app; clarify.
        right; left; rewrite split_app.
        assert (lock_handler t m0 zt <> []) by (destruct zt; clarify).
        rewrite last_cons, <- app_removelast_last; auto. }
      intro; exploit removelast_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
    repeat rewrite Forall_forall; intros HL Haccess ? Ha;
      specialize (Haccess _ Ha); specialize (HL _ Ha).
    constructor; clarify.
    exploit instrument_own_thread; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite in_app; clarify. }
    { clarify. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_forall; intros.
    exploit in_mops_max_vc'; eauto.
    repeat intro; destruct x2; clarify.
    destruct (loc_of x1); exploit HL; eauto.
    { eapply locks_spec; eauto; clarify. }
  - rewrite removelast_length in Ht_steps; [|apply instrument_nonnil].
    exploit t_steps_unlock; try apply Ht_steps; eauto.
    intros (vs & v & Heq); rewrite app_assoc, Heq; clear Heq.
    exploit step_thread; try apply Hstep1; eauto; intros (i & li & Heq & Hin2).
    specialize (Hlocks m0); use Hlocks.
    assert (li = tl (unlock_handler t m0 zt tmp1) ++ Unlock m0 :: rest).
    { simpl in Heq; destruct zt; clarify.
      rewrite <- app_assoc; auto. }
    clarify; exploit unlock_locked; try apply Hlocks; try apply Hsim;
      try apply Hsteps; try apply Hin2; auto.
    { eapply exec_step_inv; eauto. }
    { rewrite Forall_forall; intros.
      exploit tl_in; eauto; intro Hi.
      setoid_rewrite in_app in Hi; destruct Hi; clarify.
      exploit set_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC.
      do 2 rewrite <- app_assoc; eauto. }
    intro Hheld.
    rewrite last_snoc in Hin1.
    exploit protect_self; try apply Hlocks; try apply Hsim; try apply Hsteps;
      eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite Forall_forall; repeat intro; subst.
      exploit rel_inv'; try apply Hsteps; eauto.
      intro; exploit tl_in; eauto; intro Hi.
      setoid_rewrite in_app in Hi; destruct Hi; clarify.
      exploit set_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC; do 3 rewrite <- app_assoc; eauto. }
    exploit protect_lock; try apply Hlocks; try apply Hsim; try apply Hsteps;
      eauto.
    { eapply exec_step_inv; eauto. }
    { rewrite Forall_forall; repeat intro; subst.
      exploit rel_inv'; try apply Hsteps; eauto.
      intro; exploit tl_in; eauto; intro Hi.
      setoid_rewrite in_app in Hi; destruct Hi; clarify.
      exploit set_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC; do 3 rewrite <- app_assoc; eauto. }
    repeat rewrite Forall_forall; intros HL Haccess ? Ha;
      specialize (Haccess _ Ha); specialize (HL _ Ha).
    exploit instrument_own_thread; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { clarify. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_forall; intros ? Hx.
    intro Heq'; rewrite <- Heq' in *; rewrite in_app in Hx;
      destruct Hx as [? | [? | ?]]; clarify.
    exploit in_mops_set_vc''; eauto.
    destruct x0; destruct (loc_of x); clarify.
    exploit HL; eauto.
    { eapply locks_spec; eauto; repeat rewrite in_app; clarify. }
  - rewrite removelast_length in Ht_steps; [|apply instrument_nonnil].
    exploit t_steps_spawn; try apply Ht_steps; eauto.
    intros (vs1 & vs2 & v & Heq); rewrite app_assoc, Heq; clear Heq.
    clarify; rewrite last_snoc in Hin1.
    clarify; exploit protect_spawn'; try apply Hsafe_i1; try apply Hsim;
      try apply Hsteps; eauto.
    { eapply exec_step_inv; eauto. }
    { simpl; eauto. }
    intro Ht0.
    exploit step_thread; try apply Hstep1; eauto; clarify.
    exploit instrument_own_thread; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { clarify. }
    repeat rewrite Forall_forall in *; intros Hthread ? Ha;
      specialize (Hthread _ Ha); specialize (Ht0 _ Ha).
    rewrite Forall_forall; intros ? Hx.
    intro Heq'; rewrite <- Heq' in *; rewrite in_app in Hx; destruct Hx;
      clarify.
    exploit in_mops_max_vc'; eauto.
    destruct x2; destruct (loc_of x1); clarify; eapply Ht0; eauto.
  - rewrite removelast_length in Ht_steps; [|apply instrument_nonnil].
    exploit t_steps_wait; try apply Ht_steps; eauto.
    intros (vs1 & vs2 & v & Heq); rewrite app_assoc, Heq; clear Heq.
    simpl in Hin.
    exploit protect_wait; try apply Hsim; try apply Hin; eauto.
    { generalize (in_split _ _ Hin); clarify.
      inversion Hstep1; subst; exploit distinct_thread; try apply Hdistinct1;
        eauto; clarify. }
    { eapply exec_step; eauto; apply exec_refl. }
    rewrite filter_app, Forall_app; intros (_ & Ht0).
    exploit step_thread; try apply Hstep1; eauto; clarify.
    exploit instrument_own_thread; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { clarify. }
    repeat rewrite Forall_forall in *; intros Hthread ? Ha;
      specialize (Hthread _ Ha); specialize (Ht0 _ Ha).
    rewrite Forall_forall; intros ? Hx.
    intro Heq'; rewrite <- Heq' in *; rewrite in_app in Hx; destruct Hx;
      clarify.
    + exploit in_mops_max_vc'; eauto.
      destruct x0; destruct (loc_of x); clarify; eapply Ht0; eauto.
    + destruct H; clarify; eapply Ht0; eauto.
  - exploit step_thread; try apply Hstep1; eauto; clarify.
    exploit exec_keep; try apply Hsteps; eauto; clarify.
    exploit distinct_in.
    { apply Hdistinct1. }
    { apply Hin. }
    { eauto. }
    clarify; exploit skip_cons_neq; eauto; clarify.
Qed.*)

Lemma list_fresh_iff : forall v li, (fix list_fresh l :=
  match l with [] => True | i :: rest => fresh v i /\ list_fresh rest end) li
  <-> Forall (fresh v) li.
Proof.
  induction li; split; clarify; rewrite IHli in *; clarify.
  inversion H; clarify.
Qed.

Lemma Forall_and : forall A P1 P2 (l : list A),
  Forall (fun x => P1 x /\ P2 x) l <-> Forall P1 l /\ Forall P2 l.
Proof.
  induction l; split; clarify.
  - inversion H; rewrite IHl in *; split; constructor; clarify.
  - inversion H1; inversion H2; constructor; auto; rewrite IHl; auto.
Qed.  

Lemma fresh_result : forall Pa t i li Pb
  (Hfresh : fresh_tmps (Pa ++ (t, i :: li) :: Pb)) G v th o c G' f
  (Hresult : instr_result t i (G t) v = Some (th, o, c, G', f)),
  fresh_tmps (Pa ++ (t, li) :: opt_to_list th ++ Pb).
Proof.
  unfold fresh_tmps; intros.
  rewrite Forall_app in *; clarify.
  inversion Hfresh2 as [|?? Hi]; inversion Hi; constructor; auto.
  rewrite Forall_app; clarify.
  destruct th; clarify.
  destruct i; clarify.
  constructor; auto.
  simpl; rewrite Forall_and.
  do 2 rewrite <- (list_fresh_iff); auto.
Qed.  

Lemma safe_result : forall Pa t i li Pb
  (Hsafe : safe_locs (Pa ++ (t, i :: li) :: Pb)) G v th o c G' f
  (Hresult : instr_result t i (G t) v = Some (th, o, c, G', f)),
  safe_locs (Pa ++ (t, li) :: opt_to_list th ++ Pb).
Proof.
  unfold safe_locs; intros.
  rewrite Forall_app in *; clarify.
  inversion Hsafe2 as [|?? Hi]; inversion Hi; constructor; auto.
  rewrite Forall_app; clarify.
  destruct th; clarify.
  destruct i; clarify.
  constructor; auto.
  rewrite safe_instrs in *; auto.
Qed.

Fixpoint instrument_prog P :=
  match P with
  | [] => []
  | (t, li) :: rest => (t, instrument li t) :: instrument_prog rest
  end.

Lemma instrumented : forall P, state_sim P (instrument_prog P).
Proof.
  induction P.
  - constructor.
  - destruct a; simpl; constructor; clarify.
Qed.

Lemma instrumented_iff : forall P1 P2, state_sim P1 P2 <->
  P2 = instrument_prog P1.
Proof.
  split; clarify; [|apply instrumented; auto].
  induction H; clarify.
  destruct x, y; clarify.
Qed.

(* We should be able to prove that most of these well-formedness conditions
   transfer over from the uninstrumented program, though I doubt we can prove
   they hold automatically. *)

Lemma sim_suffix : forall P P', state_sim P P' -> state_suffix P P'.
Proof.
  intros; induction H; constructor; auto.
  destruct x, y; clarify.
  exists 0; clarify.
  generalize (instrument_length (hd (Assign 0 (I 0)) p) t0); omega.
Qed.

Lemma skipn_all_iff : forall A n (l : list A), skipn n l = [] <-> length l <= n.
Proof.
  split; try apply skipn_all.
  revert l; induction n; clarify.
  destruct l; clarify.
  apply le_n_S; auto.
Qed.

Lemma exec_length : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G'),
  length P <= length P'.
Proof.
  intros; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; induction Hsteps; clarify.
  destruct P'0; [|inversion Hsteps].
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  specialize (IHHsteps _ eq_refl); rewrite app_length in *; simpl in *.
  rewrite app_length in *; omega.
Qed.

Lemma in_steps_rev : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P'),
  (exists li1, In (t, li1 ++ li) P) \/ (forall li, ~In (t, li) P) /\
  exists P1 G1 lo1 lc1 t' li1 rest lo2 lc2 P1',
    exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t', Spawn t (li1 ++ li) :: rest) P1 /\
    exec P1 G1 t' (Some (fork t' t)) None (Some P1') G1 /\
    exec_star (Some P1') G1 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ fork t' t :: lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb; generalize dependent P;
    induction Hsteps; clarify.
  - left; exists []; auto.
  - destruct P'0; [|inversion Hsteps].
    exploit distinct_step; eauto; intro.
    exploit IHHsteps; eauto; intros [IH | IH].
    + destruct IH as (li1 & ?).
      exploit in_step_rev; eauto; intros [? | [(? & i & ?) | (rest & ?)]];
        eauto.
      * left; exists (i :: li1); clarify.
      * right.
        exploit in_split; eauto; clarify.
        exploit exec_next; eauto; clarify.
        split; [|repeat eexists; eauto; try apply exec_refl; auto].
        repeat intro; contradiction H22222.
        rewrite in_map_iff; do 2 eexists; eauto; clarify.
    + right; clarify.
      split.
      * repeat intro.
        destruct (eq_dec t0 t); [subst; exploit step_thread |
          exploit exec_other_thread]; eauto; clarify; eapply IH1; eauto.
      * do 11 eexists; [|split; eauto].
        { eapply exec_step; eauto. }
        repeat (split; eauto); rewrite <- app_assoc; auto.
Qed.

Lemma in_steps_rev2 : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P'),
  (exists li1, In (t, li1 ++ li) P) \/ (forall li, ~In (t, li) P) /\
  exists P1 G1 lo1 lc1 t0 t' li' rest li1 lo2 lc2 P1',
    exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t0, Spawn t' li' :: rest) P1 /\
    In (t0, li1 ++ Spawn t' li' :: rest) P /\
    exec P1 G1 t0 (Some (fork t0 t')) None (Some P1') G1 /\
    exec_star (Some P1') G1 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ fork t0 t' :: lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb; generalize dependent P;
    induction Hsteps; clarify.
  - left; exists []; auto.
  - destruct P'0; [|inversion Hsteps].
    exploit distinct_step; eauto; intro.
    exploit IHHsteps; eauto; intros [IH | IH].
    + destruct IH as (li1 & ?).
      exploit in_step_rev; eauto; intros [? | [(? & i & ?) | (rest & ?)]];
        eauto.
      * left; exists (i :: li1); clarify.
      * right.
        exploit in_split; eauto; clarify.
        exploit exec_next; eauto; clarify.
        split.
        { repeat intro; contradiction H22222.
          rewrite in_map_iff; do 2 eexists; eauto; clarify. }
        { repeat eexists; try apply exec_refl; eauto.
          instantiate (1 := []); rewrite in_app; clarify. }
    + right; destruct IH as (IH1 & ? & ? & ? & ? & t' & ? & ? & ? & rest & ?);
        clarify.
      split.
      * repeat intro.
        destruct (eq_dec t0 t); [subst; exploit step_thread |
          exploit exec_other_thread]; eauto; clarify; eapply IH1; eauto.
      * exploit in_step_rev; try apply Hexec; eauto;
          intros [? | [(? & i & ?) | ?]].
        { do 13 eexists; [|split; eauto].
          { eapply exec_step; eauto. }
          repeat (split; eauto); rewrite <- app_assoc; auto. }
        { clarify; do 13 eexists; [|split; eauto].
          { eapply exec_step; eauto. }
          repeat (split; eauto); try solve [rewrite <- app_assoc; auto].
          instantiate (1 := i :: rest); auto. }
        { clarify; do 13 eexists; [apply exec_refl|].
          split; eauto.
          split; [instantiate (1 := []); auto|].
          assert (G' = G /\ o = Some (fork t0 t') /\ c = None).
          { exploit in_split; eauto; clarify.
            inversion Hexec; subst; exploit distinct_thread;
              try apply Hdistinct; eauto; clarify. }
          clarify; eauto. }
Qed.

Lemma length_firstn : forall A n (l : list A), n <= length l ->
  length (firstn n l) = n.
Proof.
  intros.
  rewrite List.firstn_length, Min.min_l; auto.
Qed.

Lemma app_eq_skip : forall A (l1 l2 l3 : list A), l1 ++ l2 = l3 ->
  l2 = skipn (length l1) l3.
Proof.
  intros.
  assert (length l1 <= length l3).
  { rewrite <- H, app_length; omega. }
  rewrite <- (firstn_skipn (length l1) l3) in H.
  exploit app_eq_inv; try apply H; clarify.
  rewrite length_firstn; auto.
Qed.  

Lemma spawn_in_handler' : forall u li i t n
  (Hnth : nth_error (instrument_instr i t) n = Some (Spawn u li)),
  exists li', i = Spawn u li' /\ li = instrument li' u /\
  n = length (instrument_instr i t) - 1.
Proof.
  intros.
  exploit nth_error_in; eauto; intro.
  exploit spawn_in_handler; eauto; clarify.
  repeat eexists; eauto.
  rewrite nth_error_app in Hnth.
  destruct (lt_dec n (length (spawn_handler t u zt))).
  - unfold spawn_handler in Hnth; rewrite nth_error_app in Hnth.
    destruct (lt_dec n (length (max_vc (C' + t) (C' + u) zt tmp1 tmp2)));
      exploit nth_error_in; eauto; clarify.
    exploit max_vc_instrs; eauto; clarify.
  - rewrite nth_error_single in *; clarify.
    rewrite app_length; simpl; omega.
Qed.

Lemma distinct_threads : forall P P' (Hsuffix : state_suffix P P') t,
  In t (map fst P) <-> In t (map fst P').
Proof.
  intros; induction Hsuffix; [reflexivity|].
  destruct x, y; clarify.
  rewrite IHHsuffix; reflexivity.
Qed.

Lemma distinct_suffix : forall P P' (Hsuffix : state_suffix P P'),
  distinct P <-> distinct P'.
Proof.
  intros; induction Hsuffix; [reflexivity|].
  unfold distinct; destruct x, y; clarify.
  exploit distinct_threads; eauto.
  instantiate (1 := t); intro Hin.
  split; intro H; inversion H; subst; constructor.
  - rewrite <- Hin; auto.
  - rewrite <- IHHsuffix; auto.
  - rewrite Hin; auto.
  - rewrite IHHsuffix; auto.
Qed.

Lemma sim_thread : forall P P1 P2 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1) G1 lo lc G2
  (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2) t li
  (Hin : In (t, li) P2),
  (exists li0, In (t, li0) P /\
   In (t, instrument li0 t) P1 /\
   exists n', n' < length (instrument_instr (hd (Assign 0 (I 0)) li0) t) /\
     li = skipn n' (instrument li0 t)) \/
  (exists t0 i rest n', In (t0, instrument_instr i t0 ++ rest) P1 /\
     In (t0, skipn n' rest) P2).
Proof.
  intros.
  exploit in_steps_rev2; eauto; intros [(li1 & ?) | Hspawn].
  - exploit Forall2_in2; eauto; intros ((? & li0) & ? & ? & Heq);
      clarify.
    exploit app_eq_skip; eauto; clarify.
    destruct (le_gt_dec (length (instrument_instr (hd (Assign 0 (I 0)) li0) t))
      (length li1)).
    + right; destruct li0; clarify.
      { rewrite skipn_nil in *.
        destruct li1; clarify; omega. }
      rewrite Heq in H; repeat eexists; eauto.
      rewrite skipn_app, skipn_all in Hin; [eauto | omega].
    + left; rewrite Heq in *; exists li0; clarify.
      repeat eexists; eauto.
  - right; destruct Hspawn as (Hout & ? & ? & ? & ? & t1 & t' & li' & rest &
      li2 & ? & ? & ? & ? & ? & ? & Hspawn & Hsteps' & ?); clarify.
    exploit Forall2_in2; eauto; intros ((?, li1) & ? & ? & Heq).
    destruct li1; clarify.
    { destruct li2; clarify. }
    simpl in *; rewrite Heq in *.
    assert (exists n, rest = skipn n (instrument li1 t1)) as (n' & ?).
    { rewrite split_app in Heq.
      destruct (le_gt_dec (length (li2 ++ [Spawn t' li']))
        (length (instrument_instr i t1))).
      * exploit app_eq_inv_ge; eauto; intros (? & ? & Heq1).
        exploit spawn_in_handler'.
        { setoid_rewrite Heq1.
          rewrite <- app_assoc; simpl; apply nth_error_split. }
        intros (? & ? & ? & Hlen); subst.
        symmetry in Heq1; generalize (app_eq_skip _ _ Heq1).
        rewrite app_length, skipn_all; [exists 0; clarify|].
        rewrite Hlen; simpl; omega.
      * symmetry in Heq; exploit app_eq_inv_ge; try apply Heq; [omega|].
        intros (? & Hrest & ?).
        symmetry in Hrest; generalize (app_eq_skip _ _ Hrest); eauto. }
    subst.
    inversion Hspawn; clarify.
    exploit distinct_steps; eauto; intro.
    exploit distinct_in.
    { eauto. }
    { rewrite in_app; clarify. }
    { eauto. }
    clarify.
    exploit exec_keep; try apply Hsteps'.
    { eapply distinct_step; eauto. }
    { rewrite in_app; right; simpl; left; eauto. }
    clarify; rewrite skipn_skipn in *; repeat eexists; eauto.
Qed.    

Corollary sim_thread1 : forall P P1 P2 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1) G1 lo lc G2
  (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2),
  Forall (fun (e : tid * list instr) => let (t, li) := e in
    exists li0, In (t, li0) P /\ exists n,
    n < length (instrument_instr (hd (Assign 0 (I 0)) li0) t) /\
    li = skipn n (instrument li0 t)) P2 \/ exists t i rest n',
    In (t, instrument_instr i t ++ rest) P1 /\ In (t, skipn n' rest) P2.
Proof.
  intros.
  remember P2 as P'.
  assert (Forall (fun (e : tid * list instr) => let (t, li) := e in
    (exists li0, In (t, li0) P /\ In (t, instrument li0 t) P1 /\
     exists n', n' < length (instrument_instr (hd (Assign 0 (I 0)) li0) t)
      /\ li = skipn n' (instrument li0 t)) \/
    (exists t0 i rest n', In (t0, instrument_instr i t0 ++ rest) P1 
      /\ In (t0, skipn n' rest) P2)) P').
  { rewrite Forall_forall; intros (t, li); subst; eapply sim_thread; eauto. }
  setoid_rewrite HeqP' at 2.
  assert (incl P' P2) as Hincl by (subst; apply incl_refl).
  clear Hsteps HeqP'; induction P'; auto.
  inversion H as [|?? Ha]; clear H; clarify.
  generalize (incl_cons_inv Hincl); clarify.
  destruct a as (t, li); destruct Ha as [(li0 & n & Hli0) | ?];
    [|clarify; right; repeat eexists; eauto].
  clarify; left; constructor; eauto.
Qed.

Lemma sim_next_thread : forall P P1 P2 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1) G1 lo lc G2
  (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2),
  state_suffix P P2 \/ exists t i rest n',
    In (t, instrument_instr i t ++ rest) P1 /\ In (t, skipn n' rest) P2.
Proof.
  intros.
  exploit sim_thread1; eauto; clarify; left.
  remember (Some P1) as Pa; remember (Some P2) as Pb; generalize dependent P2;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  { apply sim_suffix; auto. }
  rewrite <- exec_rev in Hsteps; specialize (IHHsteps _ eq_refl).
  exploit exec_result; eauto.
  intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  destruct o0; clarify.
  { destruct i; clarify.
    rewrite Forall_app in H; clarify.
    inversion H2 as [|??? Ht0]; clarify.
    inversion Ht0 as [|(?, ?) ? (? & Hin0 & ?)]; clarify.
    contradiction Hresult2222.
    exploit Forall2_in1; try apply Hin0; eauto; intros ((?, ?) & Hin1 & ?);
      clarify.
    exploit exec_keep; eauto; clarify.
    rewrite in_map_iff; repeat eexists; eauto; clarify. }
  rewrite Forall_app in *; clarify.
  inversion H2 as [|?? Ht]; subst.
  destruct Ht as (li0 & ? & n' & ?); clarify.
  use IHHsteps.
  - exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hrest & ?); subst.
    inversion Hrest as [|(?, ?)]; clarify.
    apply Forall2_app; auto; constructor; clarify.
    rewrite <- (distinct_suffix (sim_suffix Hsim)) in Hdistinct.
    exploit distinct_in.
    { eauto. }
    { eauto. }
    { rewrite in_app; clarify. }
    clarify; eauto.
  - constructor; auto.
    do 2 eexists; eauto.
    exploit Forall2_in1; eauto; intros ((?, ?) & Hin1 & ?); clarify.
    exploit exec_mono; eauto.
    { rewrite in_app; clarify. }
    intros (n2 & Hskip).
    destruct n'; [exploit skip_cons_neq; eauto; contradiction|].
    exists n'; split; [omega|].
    erewrite (skipn_n n'); eauto.
    assert (n2 = n').
    { assert (length (i :: skipn (S n') (instrument li0 t0)) =
        length (skipn n2 (instrument li0 t0))) by (rewrite Hskip; auto).
      remember (S n') as n0; simpl in *; repeat rewrite skipn_length in *.
      destruct li0; clarify.
      rewrite app_length in *; omega. }
    rewrite <- (plus_O_n n'), <- skipn_nth; subst.
    rewrite <- Hskip; clarify.
Qed.

Definition mem_ext m1 m2 := (forall ops, consistent (m1 ++ ops) <->
  consistent (m2 ++ ops)) /\ forall p, initialized m1 p <-> initialized m2 p.

Lemma mem_ext_app : forall m1 m2 ops, mem_ext m1 m2 ->
  mem_ext (m1 ++ ops) (m2 ++ ops).
Proof.
  repeat intro; split; intro.
  - repeat rewrite <- app_assoc.
    destruct H as [H _]; rewrite H; reflexivity.
  - unfold initialized.
    repeat rewrite lower_app; split; intros (v & Hlast);
      rewrite last_op_app in Hlast; destruct Hlast;
      try solve [exists v; rewrite last_op_app; clarify].
    + destruct H as [_ H]; specialize (H p); destruct H as [H _].
      clarify; exploit H; unfold initialized; eauto.
      intros (v' & ?); exists v'; rewrite last_op_app; clarify.
    + destruct H as [_ H]; specialize (H p); destruct H as [_ H].
      clarify; exploit H; unfold initialized; eauto.
      intros (v' & ?); exists v'; rewrite last_op_app; clarify.
Qed.

Lemma state_sim_inv' : forall P2a P1 P2b t li'
  (Hsim : state_sim P1 (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  exists P1a li P1b, P1 = (P1a ++ (t, li) :: P1b) /\
  state_sim P1a P2a /\ state_sim P1b P2b /\ li' = instrument li t.
Proof.
  induction P2a; clarify.
  - inversion Hsim as [|(?, ?)]; clarify.
    exists []; repeat eexists; auto; constructor.
  - inversion Hsim as [|(?, ?) ???? Hrest]; clarify.
    specialize (IHP2a _ _ _ _ Hrest).
    inversion Hdistinct; clarify.
    repeat eexists; eauto; try constructor; eauto; clarify.
Qed.

Lemma state_suffix_inv' : forall P2a P1 P2b t li'
  (Hsuffix : state_suffix P1 (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  exists P1a li P1b n, P1 = (P1a ++ (t, li) :: P1b) /\
  state_suffix P1a P2a /\ state_suffix P1b P2b /\
  li' = skipn n (instrument li t) /\
  n < length (instrument_instr (hd (Assign 0 (I 0)) li) t).
Proof.
  induction P2a; clarify.
  - inversion Hsuffix as [|(?, ?)]; clarify.
    exists []; repeat eexists; auto; constructor.
  - inversion Hsuffix as [|(?, ?) ???? Hrest]; clarify.
    specialize (IHP2a _ _ _ _ Hrest).
    inversion Hdistinct; clarify.
    repeat eexists; eauto; try constructor; clarify; eauto.
Qed.

Instance mem_ext_refl : RelationClasses.Reflexive mem_ext.
Proof. repeat intro; split; reflexivity. Qed.

Lemma state_suffix_alt : forall P P1, state_suffix P P1 <->
  (forall n t li (Hn : nth_error P n = Some (t, li)),
    exists li1, nth_error P1 n = Some (t, li1) /\ exists n',
    n' < length (instrument_instr (hd (Assign 0 (I 0)) li) t) /\
    li1 = skipn n' (instrument li t)) /\
  (forall n t li1 (Hn : nth_error P1 n = Some (t, li1)), exists li,
    nth_error P n = Some (t, li)).
Proof.
  induction P; intros.
  - split; intro H; [inversion H|]; clarify.
    + split; clarsimp.
    + destruct P1; [constructor | clarify].
      destruct p as (t, li).
      specialize (H2 0 t li); clarify.
  - split; intro H; clarify.
    + inversion H as [|(?, ?) (?, ?) ??? Hsuffix]; clarify.
      rewrite IHP in Hsuffix; clarify.
      split; intros.
      * destruct n; clarify; eauto.
      * destruct n; clarify; eauto.
    + destruct a as (t, li).
      generalize (H1 0 t li); clarify.
      destruct P1; clarify.
      constructor; eauto.
      rewrite IHP; split; clarify.
      * specialize (H1 (S n) t0 li0); clarify; eauto.
      * specialize (H2 (S n) t0 li1); clarify; eauto.
Qed.

(* Next time, consider using a map. *)
Lemma state_suffix_inter : forall P P1 (Hsim : state_suffix P P1)
  (Hdistinct : distinct P1)
  G1 lo1 lc1 P2 G2 (Hsteps1 : exec_star (Some P1) G1 lo1 lc1 (Some P2) G2)
  lo2 lc2 P3 G3 (Hsteps2 : exec_star (Some P2) G2 lo2 lc2 (Some P3) G3)
  (Hsuffix : state_suffix P P3), state_suffix P P2.
Proof.
  intros until G2; intro; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P1; induction Hsteps1; clarify.
  destruct P'; [|inversion Hsteps1].
  assert (state_suffix P s -> state_suffix P P2) as IH.
  { intro; eapply IHHsteps1; eauto.
    eapply distinct_step; eauto. }
  clear IHHsteps1.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  exploit state_suffix_inv'; eauto; intros (? & li0 & ? & n & ?); clarify.
  destruct li0; [rewrite skipn_nil in *|]; clarify.
  rewrite skipn_app' in *; [|omega].
  destruct (skipn n (instrument_instr i0 t)) eqn: Hskip; clarify.
  { rewrite skipn_all_iff in Hskip; omega. }
  destruct l; clarify.
  - exploit distinct_step; eauto; intro.
    exploit exec_keep; eauto; [apply split_in | clarify].
    exploit distinct_steps; eauto; intro.
    exploit exec_keep; eauto; intros (? & Hin').
    rewrite skipn_skipn in *.
    exploit Forall2_in1; try apply Hsuffix; [apply split_in|].
    intros ((?, ?) & ?); clarify.
    exploit distinct_steps; eauto; intro.
    exploit distinct_in; [eauto | apply Hin' | eauto|].
    rewrite skipn_app'; [|omega].
    intro Hskips.
    pose proof (eq_refl (length (skipn (x0 + x4) (instrument li0 t)))) as Hlen.
    rewrite Hskips in Hlen at 1; rewrite app_length in Hlen;
      repeat rewrite skipn_length in Hlen; omega.
  - apply IH; clear IH.
    destruct o0; clarify.
    { destruct i1; clarify.
      exploit spawn_in_handler'.
      { rewrite <- skipn_nth; setoid_rewrite Hskip.
        instantiate (3 := 0); simpl; eauto. }
      clarify.
      rewrite app_length in Hskip; simpl in Hskip.
      rewrite Nat.add_sub, skipn_app', skipn_length' in Hskip; clarify. }
    apply Forall2_app; [|constructor]; clarify.
    exists (S n); rewrite skipn_app'; [|omega].
    split.
    + eapply nth_error_lt.
      rewrite <- Nat.add_1_l, <- skipn_nth, Hskip; simpl; eauto.
    + erewrite skipn_n in Hskip;
        [|rewrite <- (plus_O_n n), <- skipn_nth, Hskip; simpl; eauto].
      inversion Hskip as [Heq]; simpl; rewrite Heq; auto.
Qed.  

Corollary state_suffix_inv : forall P P1 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1)
  G1 lo1 lc1 P2 G2 (Hsteps1 : exec_star (Some P1) G1 lo1 lc1 (Some P2) G2)
  lo2 lc2 P3 G3 (Hsteps2 : exec_star (Some P2) G2 lo2 lc2 (Some P3) G3)
  (Hsuffix : state_suffix P P3), state_suffix P P2.
Proof.
  
  intros; eapply state_suffix_inter with (P3 := P3); try apply sim_suffix, Hsim;
    eauto.
Qed.

Lemma exec_t_maintain : forall P G lo lc P' G' t li (Hdistinct : distinct P)
  (Hin : In (t, li) P) (Hsteps : exec_star_t t (Some P) G lo lc (Some P') G')
  (Hin' : In (t, li) P'), P' = P /\ G' = G /\ lo = [] /\ lc = [].
Proof.
  intros; inversion Hsteps; clarify.
  destruct P'0; [|inversion Hexec'; clarify].
  exploit step_thread; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit exec_mono; eauto.
  { eapply exec_t_exec; eauto. }
  clarify.
  exploit skip_cons_neq; eauto; clarify.
Qed.

Lemma upd_overwrite1 : forall A B (A_eq : EqDec_eq A) (f : A -> B) t v1 v2,
  upd (upd f t v1) t v2 = upd f t v2.
Proof.
  intros; extensionality x; unfold upd; clarify.
Qed.

Lemma upd_assoc1 : forall A B (A_eq : EqDec_eq A) (f : A -> B) t1 t2 v1 v2
  (Hdiff : t1 <> t2), upd (upd f t1 v1) t2 v2 = upd (upd f t2 v2) t1 v1.
Proof.
  intros; extensionality x; unfold upd; clarify.
Qed.

Transparent last.

Lemma last_cons' : forall A (l : list A) x d, last (x :: l) d = last l x.
Proof.
  intros; destruct (nil_dec l).
  - subst; simpl; auto.
  - simpl; destruct l; auto.
    rewrite (app_removelast_last d), last_snoc, last_snoc; auto.
Qed.

Lemma upd_three : forall G t a1 a2 v1 v2 v1' (Hdiff : a1 <> a2),
  upd_env (upd_env (upd_env G t a1 v1) t a2 v2) t a1 v1' =
  upd_env (upd_env G t a1 v1') t a2 v2.
Proof.
  intros; rewrite upd_assoc, upd_overwrite; auto.
Qed.

Lemma hb_check_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt
  Pa Pb (HP : P = Pa ++ (t, hb_check src tgt z tmp1 tmp2 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists vs1 vs2, lo = events_hb_check src tgt vs1 vs2 t /\
    lc = mops_hb_check src tgt vs1 vs2 z t /\ first_gt vs1 vs2 = None /\
    length vs1 = z /\ length vs2 = z /\ P' = (Pa ++ (t, li) :: Pb) /\
    G' = upd_env (upd_env G t tmp1 (last vs1 (G t tmp1)))
                 t tmp2 (last vs2 (G t tmp2)).
Proof.
  induction z; clarify.
  - exists [], []; clarify.
    do 2 rewrite upd_triv.
    exploit exec_t_maintain; eauto; clarify.
    rewrite in_app; clarify.
  - inversion Ht; clarify.
    { exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin' |
                            clarify].
      repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
    exploit exec_next; eauto; intros (v1 & ?); clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'; clarify.
    { exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin' |
                            clarify].
      repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
    exploit exec_next; eauto; intros (v2 & ?); clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clarify.
    { exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin' |
                            clarify].
      repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
    exploit exec_next; eauto; simpl; intros (? & ?).
    rewrite upd_same, upd_assoc, upd_same in *; auto.
    destruct (le_dec v1 v2); clarify; [|inversion Hexec'1].
    exploit distinct_step; eauto; intro.
    exploit IHz; eauto.
    rewrite <- leb_le in *.
    Opaque last.
    intros (vs1 & vs2 & ?); exists (v1 :: vs1), (v2 :: vs2); clarify.
    rewrite upd_overwrite, upd_same.
    rewrite upd_three, upd_old, upd_same, upd_assoc; auto.
    do 2 rewrite last_cons'; auto.
Qed.

Lemma exec_t_segment : forall t P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star_t t (Some P) G lo lc (Some P') G')
  li1 li2 li3 (Hin : In (t, li1 ++ li2 ++ li3) P) (Hin' : In (t, li3) P'),
  exists P1 G1 lo1 lc1 lo2 lc2, exec_star_t t (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t, li2 ++ li3) P1 /\ exec_star_t t (Some P1) G1 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros ?????????; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; induction Hsteps; clarify.
  - exploit distinct_in; [eauto | apply Hin | apply Hin' | clarify].
    rewrite app_assoc in H; exploit app_nil_inv; eauto; clear H; intro.
    exploit app_eq_nil; eauto; clarify.
    repeat eexists; try apply exec_refl_t; auto.
  - destruct P'0; [|inversion Hsteps].
    exploit distinct_step; eauto; intro.
    destruct li1.
    { do 7 eexists; [apply exec_refl_t | clarify].
      eapply exec_step_t; eauto. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (v & ?).
    destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
    exploit IHHsteps; eauto.
    { rewrite in_app; clarify. }
    intros (? & ? & ? & ? & ? & ? & Hsteps' & ?).
    clarify; do 7 eexists; [eapply exec_step_t; try apply Hsteps'; eauto |
      clarify].
    split; eauto.
    repeat rewrite <- app_assoc; auto.
Qed.

Lemma move_exec : forall t P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt Pa Pb (HP : P = Pa ++ (t, move src tgt tmp1 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists v, lo = events_move (fst src) (fst tgt) t /\
            lc = mops_move src tgt t v /\ P' = Pa ++ (t, li) :: Pb /\
            G' = upd_env G t tmp1 v.
Proof.
  intros; inversion Ht; clear Ht; clarify.
  { exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify].
    exfalso; eapply (cons_app_neq [_]); simpl; eauto. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clear Hexec'; clarify.
  { exploit distinct_in.
    { eauto. }
    { rewrite in_app; clarify. }
    { eauto. }
    intro; exploit cons_neq; eauto; contradiction. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit exec_t_maintain; eauto.
  { rewrite in_app; clarify. }
  clarify.
  repeat eexists; eauto.
  rewrite upd_same; auto.
Qed.
    
Opaque move.
Opaque mops_move.
Opaque events_move.

Lemma last_def : forall A (l : list A) d d', l <> [] -> last l d = last l d'.
Proof.
  intros; rewrite (app_removelast_last d H); repeat rewrite last_snoc; auto.
Qed.

Lemma hb_check_match : forall C1 C2 t z vs1 vs2 (Hlen1 : length vs1 = z)
  (Hlen2 : length vs2 = z) (Hle : first_gt vs1 vs2 = None)
  m (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t)) n (Hlt : n < z), 
  exists v, nth_error vs2 n = Some v /\ can_read m (C2, z - n - 1) v.
Proof.
  induction z; clarify; [omega|].
  destruct vs1, vs2; clarify.
  destruct n.
  - do 2 eexists; simpl; eauto.
    rewrite <- minus_n_O.
    rewrite read_noop_SC in Hcon.
    eapply can_read_thread'.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
    { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  - exploit (IHz vs1 vs2); eauto.
    { rewrite read_noop_SC, read_noop_SC in Hcon; auto.
      { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
      { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. } }
    { omega. }
Qed.

Lemma mops_hb_check_read : forall C1 C2 t z vs1 vs2,
  Forall (fun c => match c with Read _ _ _ => True | _ => False end)
         (mops_hb_check C1 C2 t z vs1 vs2).
Proof.
  intros.
  rewrite Forall_forall; intros.
  exploit in_mops_hb_check; eauto; destruct x; auto.
Qed.

(* up *)
Lemma list_ext : forall A (l1 l2 : list A)
  (Hnth : forall n, nth_error l1 n = nth_error l2 n), l1 = l2.
Proof.
  induction l1; destruct l2; clarify.
  - specialize (Hnth 0); clarify.
  - specialize (Hnth 0); clarify.
  - exploit IHl1.
    { intro n; specialize (Hnth (S n)); simpl in Hnth; apply Hnth. }
    specialize (Hnth 0); clarify.
Qed.

Corollary hb_check_twice : forall C1 C1' C2 t z vs1 vs1' vs2 vs2'
  (Hlen1 : length vs1 = z) (Hlen1' : length vs1' = z) (Hlen2 : length vs2 = z)
  (Hlen2' : length vs2' = z) (Hle : first_gt vs1 vs2 = None)
  (Hle' : first_gt vs1' vs2' = None)
  m (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t ++
                             mops_hb_check C1' C2 vs1' vs2' z t))
  (Hinit : forall o, o < z -> initialized m (C2, o)),
  vs2' = vs2.
Proof.
  intros.
  rewrite app_assoc in Hcon.
  generalize (hb_check_match _ _ _ _ _ Hlen1' Hlen2' Hle' _ Hcon); intro Hvs2'.
  exploit consistent_app_SC; eauto; intro Hcon'.
  generalize (hb_check_match _ _ _ _ _ Hlen1 Hlen2 Hle _ Hcon'); intro Hvs2.
  apply list_ext; intro n; specialize (Hvs2 n); specialize (Hvs2' n).
  destruct (lt_dec n z); clarify.
  - unfold can_read in *; rewrite <- app_assoc in *.
    rewrite reads_noops_SC in Hvs2'2; auto; [|apply mops_hb_check_read].
    exploit consistent_app_SC; eauto; intro.
    exploit can_read_unique.
    { eauto. }
    { specialize (Hinit (length vs1 - n - 1)).
      use Hinit; [eauto | omega]. }
    { apply Hvs22. }
    { apply Hvs2'2. }
    clarsimp.
  - destruct (nth_error vs2 n) eqn: Hnth.
    { exploit nth_error_lt; eauto; omega. }
    destruct (nth_error vs2' n) eqn: Hnth'; auto.
    { exploit nth_error_lt; eauto; omega. }
Qed.

Lemma last_nil : forall A (d : A), last [] d = d.
Proof. auto. Qed.

Lemma max_vc_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt (Hz : z <> 0)
  Pa Pb (HP : P = Pa ++ (t, max_vc src tgt z tmp1 tmp2 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists vs1 vs2, lo = events_max_vc src tgt t z /\
    lc = mops_max_vc src tgt vs1 vs2 t z /\
    length vs1 = z /\ length vs2 = z /\ P' = (Pa ++ (t, li) :: Pb) /\
    G' = upd_env (upd_env G t tmp1 (last vs1 0))
                 t tmp2 (Peano.max (last vs1 0) (last vs2 0)).
Proof.
  induction z; clarify.
  inversion Ht; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; intros (v1 & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; intros (v2 & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'0; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'1; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; clarify.
  repeat rewrite upd_same.
  rewrite upd_old, upd_same; auto.
  exploit distinct_step; eauto; intro.
  destruct (eq_dec z 0).
  { clarify.
    exploit exec_t_maintain; try apply Hexec'2; try apply split_in; eauto;
      clarify.
    exists [v1], [v2]; clarify.
    repeat rewrite upd_same.
    rewrite upd_overwrite.
    rewrite upd_old, upd_same; auto. }
  exploit IHz; eauto.
  intros (vs1 & vs2 & ?); exists (v1 :: vs1), (v2 :: vs2); clarify.
  repeat rewrite upd_same.
  rewrite upd_overwrite.
  repeat rewrite upd_three; auto.
  rewrite last_cons, last_cons; auto; intro; clarify.
Qed.

Transparent move mops_move.

Lemma set_vc_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt
  Pa Pb (HP : P = Pa ++ (t, set_vc src tgt z tmp1 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists vs, lo = events_set_vc src tgt z t /\
    lc = mops_set_vc src tgt z t vs /\ length vs = z /\
    P' = (Pa ++ (t, li) :: Pb) /\ G' = upd_env G t tmp1 (last vs (G t tmp1)).
Proof.
  induction z; clarify.
  { exists []; clarify.
    exploit exec_t_maintain; eauto; try apply split_in; clarify.
    rewrite last_nil, upd_triv; auto. }
  inversion Ht; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; intros (v & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit IHz; eauto; intros (vs & ?); exists (v :: vs); clarify.
  repeat rewrite upd_same; clarify.
  rewrite upd_overwrite.
  rewrite last_cons'; auto.
Qed.

Opaque move mops_move.

Lemma exec_t_iexec : forall t P G lo lc P' G' i li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr i t ++ li) P) (Hlt : t < zt)
  (Hfresh : fresh tmp1 i /\ fresh tmp2 i)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P')
  m (Hcon : consistent (m ++ lc))
  (Hinit : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  iexec P G t lo lc P' G'.
Proof.
  destruct i; try destruct x; clarify.
  - inversion Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
      exploit cons_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); intros (P1 & P2 & ?); clarify.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto.
    { rewrite in_app; clarify. }
    clarify; apply iexec_assign; auto.
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (i & ?); clarify.
    exploit distinct_step; eauto; intro.
    repeat rewrite <- app_assoc in *.
    exploit exec_t_segment; eauto.
    { rewrite in_app; right.
      unfold In; fold In; left.
      rewrite (app_assoc (move _ _ _)); eauto. }
    intros (Pm & Gm & loc & lcc & lom & lcm & Hcheck & Hinm & Hrest & ?);
      clarify.
    exploit hb_check_exec; try apply Hcheck; eauto; clarify.
    exploit distinct_steps; try (eapply exec_t_exec, Hcheck); auto; intro.
    rewrite <- app_assoc in Hinm; exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hmove & Hin2 & Hrest2 & ?); clarify.
    exploit move_exec; try apply Hmove; eauto; clarify.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
    inversion Hrest2; clear Hrest2; subst.
    { generalize (distinct_in Hdistinct' _ _ _ Hin2 Hin'); intro.
      exfalso; eapply (cons_app_neq [_]); simpl; eauto. }
    generalize (in_split _ _ Hin2); clarify.
    exploit exec_next; eauto; clarify.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in.
      { apply Hdistinct'. }
      { rewrite in_app; clarify. }
      { eauto. }
      intro; exploit cons_neq; eauto; contradiction. }
    exploit distinct_step; eauto; intro.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto; [rewrite in_app|]; clarify.
    rewrite upd_three; auto.
    apply iexec_load; auto.
    exploit distinct_thread; try apply H2; clarify.
    rewrite <- app_assoc; auto.
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (i & ?); clarify.
    exploit distinct_step; eauto; intro.
    repeat rewrite <- app_assoc in *.
    exploit exec_t_segment; eauto.
    { rewrite in_app; right.
      unfold In; fold In; left.
      rewrite (app_assoc (hb_check _ _ _ _ _) (move _ _ _)).
      rewrite (app_assoc (_ ++ _) _); eauto. }
    intros (Pm & Gm & loc & lcc & lom & lcm & Hcheck1 & Hinm & Hrest & ?);
      clarify.
    do 2 rewrite <- app_assoc in Hinm; rewrite (app_assoc (move _ _ _)) in Hinm.
    exploit hb_check_exec; try apply Hcheck1; eauto; clarify.
    exploit distinct_steps; try (eapply exec_t_exec, Hcheck1); auto; intro.
    exploit exec_t_segment; eauto.
    intros (Pm' & Gm' & loc' & lcc' & lom' & lcm' & Hcheck2 & Hinm' & Hrest' &
      ?); clarify.
    exploit hb_check_exec; try apply Hcheck2; eauto; clarify.
    exploit distinct_steps; try (eapply exec_t_exec, Hcheck2); auto; intro.
    rewrite <- app_assoc in Hinm'; exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hmove & Hin2 & Hrest2 & ?); clarify.
    exploit move_exec; try apply Hmove; eauto; clarify.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
    inversion Hrest2; clear Hrest2; subst.
    { generalize (distinct_in Hdistinct' _ _ _ Hin2 Hin'); intro.
      exfalso; eapply (cons_app_neq [_]); simpl; eauto. }
    generalize (in_split _ _ Hin2); clarify.
    exploit exec_next; eauto; clarify.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in.
      { apply Hdistinct'. }
      { rewrite in_app; clarify. }
      { eauto. }
      intro; exploit cons_neq; eauto; contradiction. }
    exploit distinct_step; eauto; intro.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto; [rewrite in_app|]; clarify.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_same.
    erewrite eval_old'; eauto.
    rewrite split_app, app_assoc, app_assoc in Hcon.
    exploit consistent_app_SC; eauto; intro Hcon'.
    rewrite <- app_assoc in Hcon'.
    exploit hb_check_twice; try apply Hcon'; auto.
    { intros; apply init_step; auto.
      constructor; simpl; auto. }
    intro; subst.
    erewrite last_def; [|intro; clarify].
    apply iexec_store; auto.
    exploit distinct_thread; try apply H3; clarify.
    repeat rewrite <- app_assoc; auto.
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    unfold lock_handler in *; exploit max_vc_exec; eauto; clarify.
    apply iexec_lock; auto.
  - unfold unlock_handler in *; do 2 rewrite <- app_assoc in Hin.
    rewrite (app_assoc _ [_]) in Hin.
    exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hset & Hin1 & Hrest1 & ?); clarify.
    generalize (in_split _ _ Hin); clarify.
    exploit set_vc_exec; try apply Hset; clarify.
    exploit distinct_steps; try eapply exec_t_exec, Hset; eauto; intro.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Hrest1; clear Hrest1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; try apply H; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_neq; eauto; contradiction. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; try apply Hexec'0; try apply split_in; eauto;
      clarify.
    repeat rewrite upd_same.
    repeat rewrite upd_overwrite.
    apply iexec_unlock; auto.
    unfold unlock_handler; rewrite <- app_assoc; auto.
  - unfold spawn_handler in *; do 2 rewrite <- app_assoc in Hin.
    rewrite (app_assoc _ [_]) in Hin.
    exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hmax & Hin1 & Hrest1 & ?); clarify.
    generalize (in_split _ _ Hin); clarify.
    exploit max_vc_exec; try apply Hmax; try reflexivity; clarify.
    exploit distinct_steps; try eapply exec_t_exec, Hmax; eauto; intro.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Hrest1; clear Hrest1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; try apply H; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_neq; eauto; contradiction. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; try apply Hexec'0; try apply split_in; eauto;
      clarify.
    repeat rewrite upd_same.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_assoc; auto.
    apply iexec_spawn; auto.
    unfold spawn_handler; rewrite <- app_assoc; auto.
    { rewrite map_app in *; auto. }
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    unfold wait_handler in *; rewrite <- app_assoc in *.
    exploit exec_t_segment; eauto; try apply split_in.
    intros (? & ? & ? & ? & ? & ? & Hmax & Hin1 & Hrest1 & ?); clarify.
    generalize (in_split _ _ Hin); clarify.
    exploit max_vc_exec; try apply Hmax; try reflexivity; clarify.
    exploit distinct_steps; try eapply exec_t_exec, Hmax; eauto; intro.
    inversion Hrest1; clear Hrest1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'1; clear Hexec'1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_neq; eauto; contradiction. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; try apply Hexec'0; try apply split_in; eauto;
      clarify.
    repeat rewrite upd_same.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_assoc; auto.
    apply iexec_wait; auto.
    unfold wait_handler; rewrite <- app_assoc; auto.
  - inversion Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
      exploit cons_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    destruct (le_dec (eval (G t) e1) (eval (G t) e2)); clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto; try apply split_in.
    clarify; eapply iexec_assert; eauto.
    { inversion Hexec'. }
Qed.

Lemma exec_minus_reorder : forall t P G lo lc P1 G1 (Hdistinct : distinct P)
  (Hsteps : exec_star_minus t (Some P) G lo lc (Some P1) G1)
  o c P2 G2 (Hstep : exec P1 G1 t o c (Some P2) G2)
  m (Hcon : consistent (m ++ lc ++ opt_to_list c))
  (Hindep : Forall (fun c' => match c with Some a => loc_of c' <> loc_of a
                              | None => True end) lc)
  (Hno_fork : Forall (fun o => match o with fork _ _ => False | _ => True end)
                     lo)
  (Hno_empty : Forall (fun e => snd e = [] -> In e P) P1),
  exists P1' G1', exec P G t o c (Some P1') G1' /\
    exec_star_minus t (Some P1') G1' lo lc (Some P2) G2.
Proof.
  
  intros until G2; remember (Some P) as Pa; remember (Some P1) as Pb;
    generalize dependent P; induction Hsteps; clarify.
  { repeat eexists; eauto; apply exec_refl_m. }
  destruct P'; [|inversion Hsteps].
  exploit distinct_step; eauto; intro.
  specialize (IHHsteps s); clarify.
  rewrite <- app_assoc, app_assoc in Hcon; specialize (IHHsteps _ Hcon).
  rewrite Forall_app in *; clarify.
  assert (t <> t') as Hdiff by auto.
  use IHHsteps; clarify.
  generalize (exec_swap Hdiff Hdistinct Hexec IHHsteps1); intro Hswap.
  use Hswap. use Hswap. use Hswap.
  clarify.
  repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - exploit in_split; eauto; clarify.
    exploit exec_next; eauto; clarify; inversion Hno_fork1; clarify.
  - exploit in_split; eauto; clarify.
    exploit exec_next; eauto; intros (v & ?).
    destruct (instr_result t' i (G t') v) as [((((?, ?), ?), ?), ?)|]; clarify.
    exploit exec_keep; eauto.
    { eapply exec_minus_exec; eauto. }
    { apply split_in. }
    clarify; rewrite skipn_nil in *.
    rewrite Forall_forall in Hno_empty; exploit Hno_empty; eauto; intro.
    exploit distinct_in; [apply Hdistinct | apply split_in | eauto | clarify].
  - intro; exploit in_split; eauto; clarify.
    exploit exec_next; eauto; clarify; inversion Hno_fork1; clarify.
  - eapply Forall_impl; eauto; clarify.
    destruct a; exploit exec_keep.
    { apply Hdistinct. }
    { eapply exec_step; try apply exec_refl; eauto. }
    { eauto. }
    clarify; rewrite skipn_nil in *; auto.
Qed.

Lemma state_suffix_stable : forall P P1 (Hsuffix : state_suffix P P1)
  (Hdistinct : distinct P1)
  G1 lo lc P2 G2 (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2)
  (Hsuffix2 : state_suffix P P2),
  Forall (fun o => match o with fork _ _ => False | _ => True end) lo /\
  Forall (fun e => snd e = [] -> In e P1) P2.
Proof.
    intros; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P1; induction Hsteps; clarify.
  { rewrite Forall_forall; auto. }
  destruct P'; [|inversion Hsteps].
  exploit state_suffix_inter; eauto.
  { eapply exec_step; try apply exec_refl; eauto. }
  exploit distinct_step; eauto; intros ? Hsuffix'.
  exploit IHHsteps; eauto; intros (IH1 & IH2).
  rewrite Forall_app; split; clarify.
  - destruct o; clarify.
    constructor; auto.
    destruct o; auto.
    inversion Hexec; clarify.
    exploit Forall2_in2; try apply Hsuffix'.
    { rewrite in_app; right; simpl; right; eauto. }
    intros ((?, ?) & ?); clarify.
    exploit Forall2_in1; eauto; intros ((?, ?) & ?); clarify.
    contradiction Hnew; rewrite in_map_iff; repeat eexists; eauto; auto.
  - rewrite Forall_forall in *; intros (?, ?) ??.
    exploit IH2; eauto; clarify.
    exploit Forall2_in2; eauto; intros ((?, ?) & ? & ? & ? & ? & Heq).
    destruct l; clarify.
    exploit Forall2_in1; try apply Hsuffix; eauto; intros ((?, ?) & ?); clarify.
    rewrite skipn_nil in *; auto.
    { symmetry in Heq; rewrite skipn_all_iff, app_length in Heq; omega. }
Qed.  

Instance mem_ext_trans : RelationClasses.Transitive mem_ext.
Proof.
  intros ??? (Hext1 & Hinit1) (Hext2 & Hinit2); split; intro.
  - rewrite (Hext1 ops); auto.
  - rewrite (Hinit1 p); auto.
Qed.

(* This could be incorporated into the above and into exec_result. *)
Lemma exec_next' : forall P G t o c P' G' (Hexec : exec P G t o c P' G')
  (Hdistinct : distinct P) Pa Pb i li (Hin : P = Pa ++ (t, i :: li) :: Pb),
  exists v, match instr_result t i (G t) v with
  | Some (th, o1, c1, u1, f) => G' = match u1 with Some (a, v) =>
      upd_env G t a v | None => G end /\ o1 = o /\ c1 = c /\
      P' = Some (Pa ++ (t, li) :: opt_to_list th ++ Pb) /\ f P
  | None => G' = G /\ P' = None /\ o = None /\ c = None end.
Proof.
  intros; exploit exec_next; eauto; intros (v & ?); exists v.
  destruct (instr_result t i (G t) v) eqn: Hi; clarify.
  inversion Hexec; clarify.
Qed.

Fixpoint to_mem' G t li vs :=
  match li with
  | [] => Some ([], G, vs, [])
  | i :: li =>
      match i with
      | Assign a e => to_mem' (upd G a (eval G e)) t li vs
      | Load a x => match vs with [] => None | v :: vs =>
          match to_mem' (upd G a v) t li vs with None => None
          | Some (lc, G, vs, cond) => Some (Read t x v :: lc, G, vs, cond) end
          end
      | Store x e => match to_mem' G t li vs with None => None
          | Some (lc, G', vs, cond) =>
            Some (Write t x (eval G e) :: lc, G', vs, cond)
          end
      | Lock m => match to_mem' G t li vs with None => None
          | Some (lc, G, vs, cond) => Some (Acq t m :: lc, G, vs, cond) end
      | Unlock m => match to_mem' G t li vs with None => None
          | Some (lc, G, vs, cond) => Some (Rel t m :: lc, G, vs, cond) end
      | Assert_le e1 e2 => match to_mem' G t li vs with None => None
          | Some (lc, G', vs, cond) =>
            Some (lc, G', vs, (eval G e1 <= eval G e2) :: cond)
          end
      | _ => to_mem' G t li vs
      end
  end.

Lemma to_mem'_app : forall t li1 li2 G vs lc G' vs' cond,
  to_mem' G t (li1 ++ li2) vs = Some (lc, G', vs', cond) <->
  match to_mem' G t li1 vs with None => False
  | Some (lc1, G1, vs1, cond1) => match to_mem' G1 t li2 vs1 with None => False
  | Some (lc2, G2, vs2, cond2) => lc = lc1 ++ lc2 /\ G' = G2 /\ vs' = vs2 /\
                                  cond = cond1 ++ cond2 end end.
Proof.
  induction li1; clarify.
  - destruct (to_mem' G t li2 vs) as [(((?, ?), ?), ?)|]; split; clarify.
  - assert (forall c G1 vs1, match to_mem' G1 t (li1 ++ li2) vs1 with
      | Some (lc0, G0, vs0, cond0) => Some (c :: lc0, G0, vs0, cond0)
      | None => None end = Some (lc, G', vs', cond) <->
      match match to_mem' G1 t li1 vs1 with
            | Some (lc0, G0, vs0, cond0) => Some (c :: lc0, G0, vs0, cond0)
            | None => None end with
      | Some (lc1, G1, vs1, cond1) =>
          match to_mem' G1 t li2 vs1 with
          | Some (lc2, G2, vs2, cond2) => lc = lc1 ++ lc2 /\ G' = G2 /\
                                          vs' = vs2 /\ cond = cond1 ++ cond2
          | None => False end
      | None => False end).
    { intros.
      specialize (IHli1 li2 G1 vs1).
      destruct (to_mem' G1 t li1 vs1) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' n t li2 l0) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' G1 t (li1 ++ li2) vs1) as [(((?, ?), ?), ?)|];
        clarify.
      * specialize (IHli1 l0 n l5 l6); destruct IHli1; split; clarify.
      * specialize (IHli1 (l ++ l2) n0 l3 (l1 ++ l4)); destruct IHli1; clarify.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto. }
    destruct a; clarify.
    + destruct vs; [split|]; clarify.
    + specialize (IHli1 li2 G vs).
      destruct (to_mem' G t li1 vs) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' n t li2 l0) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' G t (li1 ++ li2) vs) as [(((?, ?), ?), ?)|];
        clarify.
      * specialize (IHli1 l0 n l5 l6); destruct IHli1; split; clarify.
      * specialize (IHli1 (l ++ l2) n0 l3 (l1 ++ l4)); destruct IHli1; clarify.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto.
Qed.

Definition until_last cond li n G' := Forall id cond \/
  exists e1 e2, nth_error li (n - 1) = Some (Assert_le e1 e2) /\
  ~eval G' e1 <= eval G' e2 /\ Forall id (removelast cond) /\ ~last cond True.

Lemma until_last_nil : forall li n G, until_last [] li n G.
Proof.
  unfold until_last; clarify.
Qed.
Hint Resolve until_last_nil.

Lemma t_steps_mem' : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : t_steps P G t n lo lc P' G') li (Hin : In (t, li) P),
  exists vs vs' cond, to_mem' (G t) t (firstn n li) vs =
    Some (filter (fun c => beq (thread_of c) t) lc, G' t, vs', cond) /\
    until_last cond li n (G' t).
Proof.
  induction n; intros.
  { exists [], [], []; clarify. }
  simpl in Hsteps.
  destruct Hsteps as (? & c & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus & ?);
    clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & ?); clarify.
  assert (li = i :: rest).
  { exploit distinct_in; [eauto | eauto | apply split_in | clarify]. }
  assert (match li with [] => [] | a :: l => a :: firstn n l end =
    [i] ++ firstn n rest) as Heq by clarify; subst; rewrite Heq.
  setoid_rewrite to_mem'_app.
  assert (exists lcr, lc = opt_to_list c ++ lcr) as (lcr & ?).
  { destruct P2; clarify; eauto. }
  subst.
  assert (exists vs vs' cond, to_mem' match instr_result t i (G t) v with
    Some (_, _, _, u, _) => upd_env' G t u t | None => G t end t (firstn n rest)
    vs = Some (filter (fun c => beq (thread_of c) t) lcr, G' t, vs', cond) /\
    until_last cond rest n (G' t)) as (vs & vs' & cond & Hm2 & ?).
  { exploit exec_minus_ops; eauto; intro Hops'.
    destruct P1; [|inversion Hminus]; clarify.
    - exploit distinct_step; eauto; intro.
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
      destruct P2; clarify.
      + exploit exec_other_threads; try apply Hminus; try apply split_in; intro.
        exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
        exploit IHn; eauto.
        intros (vs & vs' & cond & Heq); exists vs, vs', cond.
        erewrite exec_minus_env in Heq; eauto.
        exploit app_inv_head; eauto; clarify.
        rewrite filter_app, (filter_none _ Hops'); auto.
      + exploit app_inv_head; eauto; clarify.        
        rewrite (filter_none _ Hops').
        rewrite (exec_minus_env Hminus); exists [], [], []; clarify.
    - exploit app_inv_head; eauto; clarify.
      exists [], [], [].
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  }
  assert (forall i, until_last cond (i :: rest) (S n) (G' t)).
  { unfold until_last in *; clarify.
    destruct n; clarify.
    rewrite <- minus_n_O in *; right; repeat eexists; eauto. }
  exists (match i with Load _ _ => v :: vs | _ => vs end), vs',
    (match i with Assert_le e1 e2 => (eval (G t) e1 <= eval (G t) e2) :: cond
     | _ => cond end); destruct i; clarify.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - destruct (le_dec (eval (G t) e1) (eval (G t) e2)); clarify.
    + unfold until_last in *; clarify; destruct n; clarify.
      rewrite <- minus_n_O in *; right; do 3 eexists; eauto.
    + inversion Hminus; clarify.
      inversion H; clarify.
      right; simpl; repeat eexists; eauto.
Qed.

(* !!! *)

Lemma removelast_firstn_eq : forall A (l : list A),
  removelast l = firstn (length l - 1) l.
Proof.
  induction l; clarify.
Qed.

Lemma removelast_2 : forall A (x y : A) l, removelast (x :: y :: l) =
  x :: removelast (y :: l).
Proof. auto. Qed.

Opaque removelast.

Lemma to_mem_conds : forall t li G vs lc G' vs'
  (Hmem : to_mem' G t li vs = Some (lc, G', vs', [])),
  Forall (fun i => match i with Assert_le _ _ => False | _ => True end) li.
Proof.
  induction li; clarify.
  destruct a; constructor; clarify; eauto.
  - destruct vs; clarify.
    destruct x0 as (((?, ?), ?), ?); clarify; eauto.
  - destruct x0 as (((?, ?), ?), ?); clarify; eauto.
  - destruct x as (((?, ?), ?), ?); clarify; eauto.
  - destruct x as (((?, ?), ?), ?); clarify; eauto.
  - destruct x as (((?, ?), ?), ?); clarify.
  - destruct x as (((?, ?), ?), ?); clarify; eauto.
Qed.

Lemma hb_check_mem_n : forall li t C1 C2 z G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (hb_check C1 C2 z tmp1 tmp2)) vs =
    Some (lc, G', vs', cond))
  (Hcond : until_last cond (hb_check C1 C2 z tmp1 tmp2 ++ li) n G')
  (Hn : n <= length (hb_check C1 C2 z tmp1 tmp2)),
  (exists vs1 vs2 n', n' <= length (mops_hb_check C1 C2 vs1 vs2 z t) /\
                      lc = firstn n' (mops_hb_check C1 C2 vs1 vs2 z t)) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - rewrite firstn_nil in *; clarify.
    exists [], [], 0; auto.
  - destruct n; clarify.
    { exists [], [], 0; auto. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n0], 1; clarify|].
      unfold upd; clarify. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n1], 2; clarify|].
      intros; rewrite VectorClocks.upd_old; auto.
      apply VectorClocks.upd_old; auto. }
    destruct x as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { unfold until_last in *; destruct Hcond as [Hcond | Hcond]; clarify.
      { inversion Hcond; clarify. }
      rewrite removelast_firstn_eq in *; simpl in *.
      destruct l2; clarify.
      inversion Hcond221; clarify.
      rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
      destruct n; clarify.
      repeat rewrite <- minus_n_O; right; repeat eexists; eauto. }
    { omega. }
    intros ((vs1 & vs2 & n' & ?) & HG); subst.
    split.
    + exists (n0 :: vs1), (n1 :: vs2); simpl.
      destruct (n0 <=? n1) eqn: Hle; [exists (S (S n')) | exists 2]; clarify.
      { omega. }
      unfold until_last in Hcond; destruct Hcond as [Hcond | Hcond].
      { inversion Hcond; clarify.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify. }
      clarify.
      destruct n; [clarify | simpl in Hcond1].
      destruct l2.
      * exploit to_mem_conds; eauto; rewrite Forall_forall; intro X; exploit X.
        { eapply nth_error_in; rewrite nth_error_firstn.
          instantiate (2 := n); destruct (lt_dec n (S n)); [|omega].
          rewrite nth_error_app in Hcond1;
            destruct (lt_dec n (length (hb_check C1 C2 z tmp1 tmp2)));
            [eauto |omega]. }
        clarify.
      * rewrite removelast_2 in Hcond221; inversion Hcond221.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify.
    + intros; rewrite HG; auto.
      do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

Lemma hb_check_mem : forall li t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (hb_check C1 C2 z tmp1 tmp2) vs =
    Some (lc, G', vs', cond))
  (Hcond : until_last cond (hb_check C1 C2 z tmp1 tmp2 ++ li)
                      (length (hb_check C1 C2 z tmp1 tmp2)) G'),
  (exists vs1 vs2, lc = mops_hb_check C1 C2 vs1 vs2 z t) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists [], []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { unfold until_last in *; destruct Hcond as [Hcond | Hcond]; clarify.
      { inversion Hcond; clarify. }
      rewrite removelast_firstn_eq in *; simpl in *.
      destruct l2; clarify.
      inversion Hcond221; clarify.
      rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
      destruct (hb_check C1 C2 z tmp1 tmp2); clarify.
      repeat rewrite <- minus_n_O; right; repeat eexists; eauto. }
    intros ((vs1 & vs2 & ?) & HG); subst.
    split.
    + exists (n :: vs1), (n0 :: vs2); simpl.
      destruct (n <=? n0) eqn: Hle; clarify.
      unfold until_last in Hcond; destruct Hcond as [Hcond | Hcond].
      { inversion Hcond; clarify.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify. }
      clarify.
      destruct (length (hb_check C1 C2 z tmp1 tmp2)) eqn: Hlen; clarify.
      { destruct z; clarify. }
      destruct l2; clarify.
      * exploit to_mem_conds; eauto; rewrite Forall_forall; intro X; exploit X.
        { eapply nth_error_in.
          rewrite nth_error_app in Hcond1;
            destruct (lt_dec n1 (length (hb_check C1 C2 z tmp1 tmp2)));
            [eauto | omega]. }
        clarify.
      * rewrite removelast_2 in Hcond221; inversion Hcond221.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify.
    + intros; rewrite HG; auto.
      do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

(* up *)
Lemma le_minus_0 : forall n m, n <= m -> n - m = 0.
Proof. intros; omega. Qed.

Transparent move mops_move.

Lemma move_mem_n : forall t C1 C2 G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (move C1 C2 tmp1)) vs =
    Some (lc, G', vs', cond)) (Hn : n <= length (move C1 C2 tmp1)),
  exists v n', n' <= length (mops_move C1 C2 t v) /\
    lc = firstn n' (mops_move C1 C2 t v) /\ cond = [] /\
    forall a, a <> tmp1 -> G' a = G a.
Proof.
  intros.
  destruct n; clarify.
  { exists 0, 0; auto. }
  destruct vs; clarify.
  destruct x as (((?, ?), ?), ?); clarify.
  exists n0.
  destruct n; clarify.
  { exists 1; clarify.
    apply VectorClocks.upd_old; auto. }
  destruct x as (((?, ?), ?), ?); clarify.
  rewrite firstn_nil in *; clarify.
  exists 2; rewrite upd_new; clarify.
  apply VectorClocks.upd_old; auto.
Qed.

Lemma move_mem : forall t C1 C2 G vs lc G' vs' cond
  (Hmem : to_mem' G t (move C1 C2 tmp1) vs = Some (lc, G', vs', cond)),
  exists v, lc = mops_move C1 C2 t v /\ cond = [] /\
    forall a, a <> tmp1 -> G' a = G a.
Proof.
  clarify.
  destruct vs; clarify.
  exists n; rewrite upd_new; clarify.
  apply VectorClocks.upd_old; auto.
Qed.

Opaque move mops_move.

Lemma until_last_cons : forall cond i li n G
  (Huntil : until_last cond (i :: li) (S n) G)
  (Hi : match i with Assert_le _ _ => False | _ => True end),
  until_last cond li n G.
Proof.
  unfold until_last; clarify.
  destruct n; clarify.
  rewrite <- minus_n_O; right; repeat eexists; eauto.
Qed.

Lemma match_false : forall A (a : option A) P,
  match a with Some x => P x | None => False end <->
  exists b, a = Some b /\ P b.
Proof.
  destruct a; split; clarify; eauto.
Qed.

Lemma until_last_app : forall cond1 cond2 li n G'
  (Huntil : until_last (cond1 ++ cond2) li n G'),
  Forall id cond1 \/ cond2 = [] /\ Forall id (removelast cond1).
Proof.
  unfold until_last; intros.
  rewrite Forall_app in Huntil; clarify.
  rewrite removelast_app in *; destruct cond2; clarify;
    [|rewrite firstn_length', Forall_app in *; [clarify | omega]].
  rewrite app_nil_r, plus_0_r, <- removelast_firstn_eq in *; auto.
Qed.

Lemma t_steps_load_n : forall P G t lo lc P1 G1 a x o li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Load a (x, o)) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Load a (x, o)) t)),
  exists vs1 vs2 vt v n', n' <= length (Acq t (X + x) ::
    mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_move (C' + t, t) (R' + x, t) t vt ++
    [Read t (x, o) v; Rel t (X' + x)]) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (Acq t (X + x) :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_move (C' + t, t) (R' + x, t) t vt ++ [Read t (x, o) v; Rel t (X' + x)])
.
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  destruct n; clarify.
  { exists [], [], 0, 0, 0; auto. }
  destruct x10 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq1.
  destruct (le_dec n (length (hb_check (W' + x) (C' + t) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq1; auto.
    exploit hb_check_mem_n; eauto.
    { eapply until_last_cons; eauto; simpl; auto. }
    intros ((vs1 & vs2 & n' & ?) & ?); exists vs1, vs2, 0, 0, (S n'); clarify.
    rewrite firstn_app, le_minus_0, app_nil_r; auto.
    split; [rewrite app_length; omega | auto]. }
  rewrite firstn_length' in Heq1; [|omega].
  rewrite to_mem'_app in Heq1.
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hcheck & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & Heq1); clarify.
  exploit hb_check_mem; eauto.
  { instantiate (1 := []).
    unfold until_last in *; exploit until_last_app; eauto; clarify.
    rewrite app_nil_r in *; clarify.
    exploit to_mem_conds; eauto; intro Hsafe.
    destruct n; [clarify | simpl in Hcond1].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
      [omega|].
    rewrite Forall_forall in Hsafe; exploit Hsafe.
    { eapply nth_error_in; rewrite nth_error_firstn.
      instantiate (2 := n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2)).
      destruct (lt_dec (n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2))
        (S n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2)));
        [eauto | omega]. }
    clarify. }
  intros ((vs1 & vs2 & ?) & ?); clarify.
  exists vs1, vs2.
  rewrite firstn_app in Hrest.
  destruct (le_dec (n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2))
    (length (move (C + t, t) (R + x, t) tmp1))).
  { setoid_rewrite (le_minus_0 l) in Hrest; rewrite app_nil_r in Hrest.
    exploit move_mem_n; eauto; intros (v & n' & ?); clarify.
    exists v, 0, (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) + n'));
      clarify.
    split.
    { repeat rewrite app_length; simpl.
      apply le_n_S, plus_le_compat_l; etransitivity; eauto.
      apply le_plus_l. }
    { rewrite firstn_app, (firstn_length' (mops_hb_check _ _ _ _ _ _)),
        minus_plus, firstn_app, le_minus_0, app_nil_r; auto; omega. } }
  rewrite firstn_length' in Hrest.
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hmove & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit move_mem; eauto; intros (v & ?); clarify.
  exists v.
  destruct (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
    (length (move (C + t, t) (R + x, t) tmp1))) eqn: Hn'; [omega|].
  setoid_rewrite Hn' in Hrest; clarify.
  destruct l0; clarify.
  destruct x10 as (((?, ?), ?), ?); clarify.
  exists n5; destruct n4; clarify.
  { exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
      (length (mops_move (C + t, t) (R + x, t) t v) + 1))); clarify.
    split; [repeat rewrite app_length; simpl; omega|].
    rewrite firstn_app, firstn_length', minus_plus, firstn_app, firstn_length',
      minus_plus; clarify; omega. }
  destruct x10 as (((?, ?), ?), ?); clarify.
  destruct n4; clarify.
  exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
    (length (mops_move (C + t, t) (R + x, t) t v) + 2))); clarify.
  split; [repeat rewrite app_length; simpl; omega|].
  rewrite firstn_app, firstn_length', minus_plus, firstn_app, firstn_length',
     minus_plus; clarify; omega.
  { exfalso; clear - Hn Hn'.
    repeat rewrite app_length in Hn; simpl in Hn.
    apply le_S_n, (minus_le_compat_r _ _ (length (hb_check (W + x) (C + t) zt
      tmp1 tmp2))) in Hn; rewrite minus_plus in Hn.
    apply (minus_le_compat_r _ _ (length (move (C + t, t) (R + x, t) tmp1)))
      in Hn; rewrite minus_plus, Hn' in Hn; omega. }
  { clear - n2.
    destruct (le_gt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
      (length (move (C + t, t) (R + x, t) tmp1))); [contradiction|].
    apply lt_le_weak; auto. }
Qed.

Lemma last_app : forall A (l1 l2 : list A) d, last (l1 ++ l2) d =
  match l2 with [] => last l1 d | _ => last l2 d end.
Proof.
  induction l2 using rev_ind.
  - rewrite app_nil_r; auto.
  - intro; rewrite app_assoc, last_snoc.
    destruct l2; clarify.
    rewrite <- list_cons_plus_assoc, last_snoc; auto.
Qed.  

Lemma t_steps_store_n : forall P G t lo lc P1 G1 x o e li
  (Hdistinct : distinct P) (Hfresh : expr_fresh tmp1 e /\ expr_fresh tmp2 e)
  (Hin : In (t, instrument_instr (Store (x, o) e) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Store (x, o) e) t)),
  exists vs1 vs2 vs2' vs3 v n', n' <= length (Acq t (X + x) ::
    mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_hb_check (R' + x) (C' + t) vs3 vs2' zt t ++
    mops_move (C' + t, t) (W' + x, t) t v ++
    [Write t (x, o) (eval (G t) e); Rel t (X' + x)]) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (Acq t (X + x) :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_hb_check (R' + x) (C' + t) vs3 vs2' zt t ++
    mops_move (C' + t, t) (W' + x, t) t v ++
    [Write t (x, o) (eval (G t) e); Rel t (X' + x)]).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  destruct n; clarify.
  { exists [], [], [], [], 0, 0; auto. }
  destruct x10 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq1.
  destruct (le_dec n (length (hb_check (W' + x) (C' + t) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq1; auto.
    exploit hb_check_mem_n; eauto.
    { eapply until_last_cons; eauto; simpl; auto. }
    intros ((vs1 & vs2 & n' & ?) & ?); exists vs1, vs2, [], [], 0, (S n');
      clarify.
    rewrite firstn_app, le_minus_0, app_nil_r; auto.
    split; [rewrite app_length; omega | auto]. }
  rewrite firstn_length' in Heq1; [|omega].
  rewrite to_mem'_app in Heq1.
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hcheck1 & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit hb_check_mem; eauto.
  { instantiate (1 := []).
    unfold until_last in *; exploit until_last_app; eauto; clarify.
    rewrite app_nil_r in *; clarify.
    exploit to_mem_conds; eauto; intro Hsafe.
    destruct n; [clarify | simpl in Hcond1].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
      [omega|].
    rewrite Forall_forall in Hsafe; exploit Hsafe.
    { eapply nth_error_in; rewrite nth_error_firstn.
      instantiate (2 := n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2)).
      destruct (lt_dec (n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2))
        (S n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2)));
        [eauto | omega]. }
    clarify. }
  intros ((vs1 & vs2 & ?) & HG1); exists vs1, vs2; clarify.
  rewrite firstn_app in Hrest.
  destruct (le_dec (n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2))
    (length (hb_check (R' + x) (C' + t) zt tmp1 tmp2))).
  { setoid_rewrite (le_minus_0 l) in Hrest; rewrite app_nil_r in Hrest.
    exploit hb_check_mem_n; eauto.
    { unfold until_last in *; rewrite Forall_app in *; clarify.
      rewrite removelast_app, Forall_app in *.
      destruct n; [clarify | simpl in Hcond1].
      rewrite nth_error_app in Hcond1;
        destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
        [omega|].
      rewrite <- minus_Sn_m; [simpl | omega].
      rewrite <- minus_n_O.
      rewrite last_app in *; destruct l5; clarify.
      right; repeat eexists; eauto. }
    intros ((vs3 & vs2' & n' & ?) & ?); clarify.
    exists vs2', vs3, 0,
      (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) + n')); clarify.
    split; [repeat rewrite app_length; omega|].
    rewrite firstn_app, (firstn_length' _ (le_plus_l _ _)),
      minus_plus, firstn_app, le_minus_0, app_nil_r; auto; omega. }
  rewrite firstn_length' in Hrest; [|omega].
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hcheck2 & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit hb_check_mem; try apply Hcheck2.
  { instantiate (1 := []).
    rewrite app_assoc in Hcond.
    unfold until_last in *; exploit until_last_app; eauto; clarify.
    repeat rewrite Forall_app in *; clarify.
    rewrite app_nil_r in *; clarify.
    exploit to_mem_conds; eauto; intro Hsafe.
    destruct n; [clarify | simpl in Hcond1].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
      [omega|].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
        (length (hb_check (R + x) (C + t) zt tmp1 tmp2))); [omega|].
    rewrite Forall_forall in Hsafe; exploit Hsafe.
    { eapply nth_error_in; rewrite nth_error_firstn.
      instantiate (2 := n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2) -
         length (hb_check (R' + x) (C' + t) zt tmp1 tmp2)).
      destruct (lt_dec (n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2) -
         length (hb_check (R' + x) (C' + t) zt tmp1 tmp2))
        (S n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2) -
         length (hb_check (R' + x) (C' + t) zt tmp1 tmp2)));
        [eauto | abstract omega]. }
    clarify. }
  intros ((vs3 & vs2' & ?) & HG2); exists vs2', vs3; clarify.
  rewrite firstn_app in Hrest.
  destruct (le_dec (n - length (hb_check (W' + x) (C' + t) zt tmp1 tmp2) -
    length (hb_check (R' + x) (C' + t) zt tmp1 tmp2))
    (length (move (C + t, t) (W + x, t) tmp1))).
  { setoid_rewrite (le_minus_0 l) in Hrest; rewrite app_nil_r in Hrest.
    exploit move_mem_n; eauto; intros (v & n' & ?); clarify.
    exists v, (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) + 
      (length (mops_hb_check (R + x) (C + t) vs3 vs2' zt t) + n'))); clarify.
    split.
    { repeat rewrite app_length; simpl.
      apply le_n_S, plus_le_compat_l, plus_le_compat_l; etransitivity; eauto.
      apply le_plus_l. }
    { rewrite firstn_app, (firstn_length' (mops_hb_check _ _ _ _ _ _)),
        minus_plus, firstn_app, (firstn_length' (mops_hb_check _ _ _ _ _ _)),
        minus_plus, firstn_app, le_minus_0, app_nil_r; auto; abstract omega. } }
  rewrite firstn_length' in Hrest.
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hmove & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit move_mem; eauto; intros (v & ? & ? & HG3); clarify.
  exists v.
  destruct (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
    length (hb_check (R + x) (C + t) zt tmp1 tmp2) -
    length (move (C + t, t) (W + x, t) tmp1)) eqn: Hn'.
  { rewrite Nat.sub_0_le in Hn'; contradiction. }
  setoid_rewrite Hn' in Hrest; clarify.
  destruct x10 as (((?, ?), ?), ?); clarify.
  destruct n6; clarify.
  { exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
      ((length (mops_hb_check (R + x) (C + t) vs3 vs2' zt t) +
       (length (mops_move (C + t, t) (W + x, t) t v) + 1))))); clarify.
    split.
    { repeat rewrite app_length; simpl.
      apply le_n_S, plus_le_compat_l, plus_le_compat_l, plus_le_compat_l; auto.
    }
    { rewrite firstn_app, firstn_length', minus_plus, firstn_app,
        firstn_length', minus_plus, firstn_app, firstn_length', minus_plus;
        try (clear; omega).
      rewrite (eval_sim _ (G t)); auto; intros.
      rewrite HG3, HG2, HG1; try intro; clarify. } }
  destruct x10 as (((?, ?), ?), ?); clarify.
  destruct n6; clarify.
  exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
    (length (mops_hb_check (R + x) (C + t) vs3 vs2' zt t) +
    (length (mops_move (C + t, t) (W + x, t) t v) + 2)))); clarify.
  split.
  { repeat rewrite app_length; simpl.
    apply le_n_S, plus_le_compat_l, plus_le_compat_l, plus_le_compat_l; auto. }
  rewrite firstn_app, firstn_length', minus_plus, firstn_app, firstn_length',
     minus_plus, firstn_app, firstn_length', minus_plus; try (clear; omega).
  rewrite (eval_sim _ (G t)); auto; intros.
  rewrite HG3, HG2, HG1; try intro; clarify.
  { exfalso; clear - Hn Hn'.
    repeat rewrite app_length in Hn; simpl in Hn.
    apply le_S_n, (minus_le_compat_r _ _ (length (hb_check (W + x) (C + t) zt
      tmp1 tmp2))) in Hn; rewrite minus_plus in Hn.
    apply (minus_le_compat_r _ _ (length (hb_check (R + x) (C + t) zt
      tmp1 tmp2))) in Hn; rewrite minus_plus in Hn.
    apply (minus_le_compat_r _ _ (length (move (C + t, t) (W + x, t) tmp1)))
      in Hn; rewrite minus_plus, Hn' in Hn; omega. }
  { clear - n4.
    destruct (le_gt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
      length (hb_check (R + x) (C + t) zt tmp1 tmp2))
      (length (move (C + t, t) (R + x, t) tmp1))); [contradiction|].
    apply lt_le_weak; auto. }
Qed.

Lemma max_vc_mem_n : forall t C1 C2 z G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (max_vc C1 C2 z tmp1 tmp2)) vs =
    Some (lc, G', vs', cond))
  (Hn : n <= length (max_vc C1 C2 z tmp1 tmp2)),
  (exists vs1 vs2 n', n' <= length (mops_max_vc C1 C2 vs1 vs2 t z) /\
                      lc = firstn n' (mops_max_vc C1 C2 vs1 vs2 t z)) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - rewrite firstn_nil in *; clarify.
    exists [], [], 0; auto.
  - destruct n; clarify.
    { exists [], [], 0; auto. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n0], 1; clarify|].
      unfold upd; clarify. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n1], 2; clarify|].
      intros; rewrite VectorClocks.upd_old; auto.
      apply VectorClocks.upd_old; auto. }
    destruct n; clarify.
    { split; [exists [n0], [n1], 2; clarify|].
      intros; rewrite VectorClocks.upd_old; auto.
      rewrite VectorClocks.upd_old, VectorClocks.upd_old; auto. }
    destruct x as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { omega. }
    intros ((vs1 & vs2 & n' & ?) & HG); subst.
    repeat rewrite upd_new in *.
    rewrite VectorClocks.upd_old, upd_new in *; auto.
    split.
    + exists (n0 :: vs1), (n1 :: vs2), (S (S (S n'))); clarify; omega.
    + intros; rewrite HG; auto.
      do 3 (rewrite VectorClocks.upd_old; auto).
Qed.

Lemma max_vc_mem : forall t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (max_vc C1 C2 z tmp1 tmp2) vs =
    Some (lc, G', vs', cond)),
  (exists vs1 vs2, lc = mops_max_vc C1 C2 vs1 vs2 t z) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists [], []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto; intros ((vs1 & vs2 & ?) & HG); subst.
    repeat rewrite upd_new in *.
    rewrite VectorClocks.upd_old, upd_new in *; auto.
    split.
    + exists (n :: vs1), (n0 :: vs2); auto.
    + intros; rewrite HG; auto.
      do 3 (rewrite VectorClocks.upd_old; auto).
Qed.

Transparent move mops_move.

Lemma set_vc_mem_n : forall t C1 C2 z G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (set_vc C1 C2 z tmp1)) vs =
    Some (lc, G', vs', cond))
  (Hn : n <= length (set_vc C1 C2 z tmp1)),
  (exists vs n', n' <= length (mops_set_vc C1 C2 z t vs) /\
                 lc = firstn n' (mops_set_vc C1 C2 z t vs)) /\
  forall a, a <> tmp1 -> G' a = G a.
Proof.
  induction z; clarify.
  - rewrite firstn_nil in *; clarify.
    exists [], 0; auto.
  - destruct n; clarify.
    { exists [], 0; auto. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], 1; clarify; omega|].
      unfold upd; clarify. }
    destruct x as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { omega. }
    intros ((vs1 & n' & ?) & HG); subst.
    rewrite upd_new in *.
    split.
    + exists (n0 :: vs1), (S (S n')); clarify; omega.
    + intros; rewrite HG; auto.
      rewrite VectorClocks.upd_old; auto.
Qed.

Lemma set_vc_mem : forall t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (set_vc C1 C2 z tmp1) vs = Some (lc, G', vs', cond)),
  (exists vs, lc = mops_set_vc C1 C2 z t vs) /\
  forall a, a <> tmp1 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto; intros ((vs1 & ?) & HG); subst.
    rewrite upd_new in *.
    split.
    + exists (n :: vs1); auto.
    + intros; rewrite HG; auto.
      rewrite VectorClocks.upd_old; auto.
Qed.

Opaque move mops_move.

Lemma t_steps_lock_n : forall P G t lo lc P1 G1 m li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Lock m) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Lock m) t)),
  exists vs1 vs2 n', n' <= length (Acq t m ::
    mops_max_vc (L' + m) (C' + t) vs1 vs2 t zt) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (Acq t m :: mops_max_vc (L' + m) (C' + t) vs1 vs2 t zt).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  destruct n; clarify.
  { exists [], [], 0; auto. }
  destruct x9 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  unfold lock_handler in *.
  rewrite firstn_app, le_minus_0, app_nil_r in Heq1; [|omega].
  exploit max_vc_mem_n; eauto.
  { omega. }
  intros ((vs1 & vs2 & n' & ?) & ?); exists vs1, vs2, (S n'); clarify; omega.
Qed.

Lemma t_steps_unlock_n : forall P G t lo lc P1 G1 m li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Unlock m) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Unlock m) t)),
  exists vs v n', n' <= length (mops_set_vc (C' + t) (L' + m) zt t vs ++
    mops_inc_vc (C + t) v t ++ [Rel t m]) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (mops_set_vc (C' + t) (L' + m) zt t vs ++
      mops_inc_vc (C + t) v t ++ [Rel t m]).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  unfold instrument_instr, unlock_handler in *;
    repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq;
    destruct (le_dec n (length (set_vc (C + t) (L + m) zt tmp1))).
  { rewrite le_minus_0, app_nil_r in Heq; auto.
    exploit set_vc_mem_n; eauto; intros ((vs1 & n' & ?) & ?).
    exists vs1, 0, n'; clarify.
    split; [rewrite app_length; omega|].
    rewrite firstn_app, le_minus_0, app_nil_r; auto. }
  rewrite firstn_length', to_mem'_app in Heq; [|omega].
  rewrite match_false in Heq;
    destruct Heq as ((((?, ?), ?), ?) & Hset & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit set_vc_mem; eauto; intros ((vs1 & ?) & ?); exists vs1; clarify.
  destruct (n - length (set_vc (C' + t) (L' + m) zt tmp1)) eqn: Hn'; clarify.
  { exists 0, (length (mops_set_vc (C + t) (L + m) zt t vs1)).
    rewrite firstn_app, firstn_length, minus_diag; clarify.
    rewrite app_length; omega. }
  destruct l0; clarify.
  destruct x as (((?, ?), ?), ?); clarify.
  exists n3.
  destruct n2; clarify.
  { exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  { exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x as (((?, ?), ?), ?); clarify.
  repeat rewrite upd_overwrite1 in *; repeat rewrite upd_new in *.
  destruct n2; clarify.
  { exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 2).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x as (((?, ?), ?), ?); clarify.
  destruct n2; clarify.
  exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 3).
  rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
  rewrite app_length; simpl; omega.
  { repeat rewrite app_length in Hn; simpl in Hn; omega. }
Qed.

Lemma t_steps_spawn_n : forall P G t lo lc P1 G1 u li' li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Spawn u li') t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Spawn u li') t)),
  exists vs1 vs2 v n', n' <= length (mops_max_vc (C' + t) (C' + u) vs1 vs2 t zt 
    ++ mops_inc_vc (C + t) v t) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (mops_max_vc (C' + t) (C' + u) vs1 vs2 t zt ++
      mops_inc_vc (C + t) v t).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  simpl in *; unfold spawn_handler in *; repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq;
    destruct (le_dec n (length (max_vc (C + t) (C + u) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq; auto.
    exploit max_vc_mem_n; eauto; intros ((vs1 & vs2 & n' & ?) & ?).
    exists vs1, vs2, 0, n'; clarify.
    split; [rewrite app_length; omega|].
    rewrite firstn_app, le_minus_0, app_nil_r; auto. }
  rewrite firstn_length', to_mem'_app in Heq; [|omega].
  rewrite match_false in Heq;
    destruct Heq as ((((?, ?), ?), ?) & Hmax & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit max_vc_mem; eauto; intros ((vs1 & vs2 & ?) & ?); exists vs1, vs2;
    clarify.
  destruct (n - length (max_vc (C' + t) (C' + u) zt tmp1 tmp2)) eqn: Hn';
    clarify.
  { exists 0, (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt)).
    rewrite firstn_app, firstn_length, minus_diag; clarify.
    rewrite app_length; omega. }
  destruct l0; clarify.
  destruct x as (((?, ?), ?), ?); clarify.
  exists n3.
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x as (((?, ?), ?), ?); clarify.
  repeat rewrite upd_overwrite1 in *; repeat rewrite upd_new in *.
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 2).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 2).
  rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
  rewrite app_length; simpl; omega.
  { repeat rewrite app_length in Hn; simpl in Hn; omega. }
Qed.

Lemma t_steps_wait_n : forall P G t lo lc P1 G1 u li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Wait u) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Wait u) t)),
  exists vs1 vs2 v n', n' <= length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt ++
    mops_inc_vc' (C + u) v t u) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (mops_max_vc (C + u) (C + t) vs1 vs2 t zt ++
      mops_inc_vc' (C + u) v t u).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  simpl in *; destruct n; clarify.
  { exists [], [], 0, 0; auto. }
  unfold wait_handler in *; rewrite <- app_assoc in *.
  rewrite firstn_app in Heq;
    destruct (le_dec n (length (max_vc (C + u) (C + t) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq; auto.
    exploit max_vc_mem_n; eauto; intros ((vs1 & vs2 & n' & ?) & ?).
    exists vs1, vs2, 0, n'; clarify.
    split; [rewrite app_length; simpl; omega|].
    rewrite firstn_app, le_minus_0, app_nil_r; auto. }
  rewrite firstn_length', to_mem'_app in Heq; [|omega].
  rewrite match_false in Heq;
    destruct Heq as ((((?, ?), ?), ?) & Hmax & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit max_vc_mem; eauto; intros ((vs1 & vs2 & ?) & ?); exists vs1, vs2;
    clarify.
  destruct (n - length (max_vc (C' + u) (C' + t) zt tmp1 tmp2)) eqn: Hn';
    clarify.
  { exists 0, (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt)).
    rewrite firstn_app, firstn_length, minus_diag; clarify.
    rewrite app_length; omega. }
  destruct l0; clarify.
  destruct x9 as (((?, ?), ?), ?); clarify.
  exists n3.
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x9 as (((?, ?), ?), ?); clarify.
  repeat rewrite upd_overwrite1 in *; repeat rewrite upd_new in *.
  destruct n2; clarify.
  exists (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt) + 2).
  rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
  rewrite app_length; simpl; omega.
  { repeat rewrite app_length in Hn; simpl in Hn; omega. }
Qed.

(* up *)
Lemma Forall_firstn : forall A (P : A -> Prop) n l, Forall P l ->
  Forall P (firstn n l).
Proof.
  intros; rewrite <- (firstn_skipn n), Forall_app in H; clarify.
Qed.

Lemma instrument_own_thread' : forall t (Ht : t < zt) P G lo lc P1 G1
  (Hsteps : exec_star (Some P) G lo lc (Some P1) G1)
  P0 (Hsafe : safe_locs P0) P0' (Hdistinct : distinct P0')
  (Hspawns : safe_spawns P0') (Hsim : state_sim P0 P0') G0 lo0 lc0
  (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  li (Hin : In (t, li) P) li1 (Hin : In (t, li1) P1) (Hlive : li1 <> [])
  t' o c P' G' (Hstep : exec P1 G1 t' o c P' G'),
  Forall (fun c => fst (loc_of c) <> C' + t)
    (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c)).
Proof.
  intros; rewrite filter_app, Forall_app.
  split; [eapply instrument_own_thread; eauto|].
  exploit exec_ops; eauto; intro Ht'.
  destruct c; clarify.
  inversion Ht'; unfold negb, beq in *; clarify.
  eapply own_thread; try apply Hsim; auto.
  - exploit exec_step_m; try apply Hstep; try apply exec_refl_m; eauto.
  - eapply exec_star_trans; eauto.
  - eauto.
  - auto.
  - eapply safe_spawns_steps; eauto.
    eapply exec_star_trans; eauto.
Qed.

Transparent move.

Lemma skipn_S_tl : forall A (l : list A) n, skipn (S n) l = skipn n (tl l).
Proof.
  intros; rewrite <- Nat.add_1_l, <- skipn_skipn; auto.
Qed.

Lemma tl_app : forall A (l1 l2 : list A), l1 <> [] ->
  tl (l1 ++ l2) = tl l1 ++ l2.
Proof.
  destruct l1; clarify.
Qed.

Lemma protect_spawn_step : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hl : u < zt) t li (Hin : In (t, li) P) li' (Hspawn : In (Spawn u li') li)
  t' o c P' G' (Hstep : exec P G t' o c P' G'),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) (opt_to_list c)).
Proof.
  intros.
  exploit safe_spawns_steps; eauto; intros (Hcount & Hrest).
  instantiate (1 := u) in Hcount.
  generalize (in_split _ _ Hin); intros (Pa & Pb & ?); subst.
  rewrite spawn_count_app in *; clarify.
  exploit has_spawn; eauto; intro.
  exploit distinct_steps; eauto; intro.
  exploit exec_ops; eauto; intro Hops.
  destruct (eq_dec t' t).
  { subst; rewrite (filter_negb_none _ Hops); auto. }
  destruct c; clarify.
  constructor; auto.
  repeat intro; exploit instrument_thread''; eauto; intros [? | Hspawn'].
  { subst; exploit exec_result; eauto; intros (? & ? & ? & ? & ? & Heq & ?).
    exploit Hrest; [|omega].
    rewrite Heq; apply split_in. }
  destruct Hspawn' as (? & ? & ? & ? & i' & n' & rest & ? & ? & ? & ? & Hin' &
    ?); clarify.
  destruct i'; try contradiction; clarify.
  - assert (spawn_count t0 (Pa ++ Pb) > 0);
      [|rewrite spawn_count_app in *; omega].
    rewrite app_length in *; simpl in *.
    rewrite skipn_app, le_minus_0 in *; [|omega].
    eapply lt_le_trans; [|apply has_spawn_thread; rewrite in_app in *;
      simpl in Hin'; destruct Hin' as [? | [? | ?]]; clarify; eauto].
    eapply has_spawn; simpl; repeat rewrite in_app; simpl; eauto.
  - exploit Hrest; eauto; omega.
Qed.

(* !! replace previous *)
Lemma protect_wait' : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0')
  (Hwaits : safe_waits P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hdone : In (u, []) P)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  t li (Hin : In (t, Wait u :: li) P),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros; remember (Some P) as P1; rewrite exec_rev in Hsteps';
    induction Hsteps'; clarify.
  rewrite filter_app, Forall_app; clarify.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t0 i (G' t0) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite <- exec_rev in Hsteps'.
  rewrite Forall_forall; intros.
  destruct c; clarify; intro.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; try apply Hdone; eauto; intros (? & Hdone').
  rewrite skipn_nil in Hdone'; clarify.
  exploit instrument_thread''; try apply Hexec'; eauto.
  { eapply exec_star_trans; eauto. }
  { exploit bounded_sim; eauto; intro.
    exploit bounded_steps; eauto; intro Hu.
    setoid_rewrite Forall_forall in Hu; specialize (Hu _ Hdone); clarify. }
  intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Hin' & ?)].
  { exploit distinct_steps; eauto; intro; subst.
    exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify]. }
  destruct i'; clarify.
  - generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
    generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
    specialize (Hspawns' t1); clarify.
    specialize (Hspawns'2 []); clarify.
    rewrite skipn_app in Hin'.
    rewrite app_length in *; simpl in *.
    assert (n' - length (spawn_handler t0 t1 zt) = 0) as Hzero by omega.
    rewrite Hzero in Hin'; simpl in Hin'.
    generalize (has_spawn_thread t1 _ _ Hin'); simpl.
    repeat rewrite spawns_list_app; clarify.
    unfold spawns in *; clarify; rewrite (spawns_list_def t1) in *; omega.
  - assert (t0 <> t).
    { exploit exec_ops; eauto; simpl; intro Hx; inversion Hx; clarify.
      unfold negb, beq in *; clarify. }
    exploit unique_wait; eauto; intros (t' & Ht').
    exploit Ht'; try apply Hin; eauto; clarify.
    exploit Ht'; try apply H2; eauto.
  - inversion Hexec'; clarify.
Qed.

(* Can this subsume instrument_indep? *)
Lemma instrument_indep_n : forall P0 G0 t o c P G lo lc P1 G1 P2 G2 i rest
  (Hdistinct : distinct P0) P0' (Hsim : state_sim P0' P0)
  (Hsafe : safe_locs P0') (Hfresh : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  (Hsafe_i : safe_instr i) (Hfresh_i : fresh tmp1 i /\ fresh tmp2 i)
  lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  (Ht1 : t < zt) (Hin : In (t, instrument_instr i t ++ rest) P1)
  (Hstep1 : exec P1 G1 t o c (Some P) G)
  (Hsteps : exec_star (Some P) G lo lc (Some P2) G2)
  n (Hn : n < length (instrument_instr i t))
  (Hin' : In (t, skipn n (instrument_instr i t) ++ rest) P2)
  t' o' c' P3 G3 (Hstep' : exec P2 G2 t' o' c' P3 G3)
  m (Hcon : consistent (m ++ lc0 ++ opt_to_list c ++ lc ++ opt_to_list c'))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t)
            (opt_to_list c ++ lc ++ opt_to_list c')))
    (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')).
Proof.
  intros.
  exploit step_thread'; eauto; intros (i' & ? & Hin1 & ?).
  exploit distinct_steps; eauto; intro Hdistinct1.
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_steps; eauto; intro Hdistinct2.
  exploit distinct_in; [try apply Hdistinct1 | eauto | apply Hin | intro Hi].
  rewrite <- (firstn_skipn n (instrument_instr i t)), <- app_assoc in Hin.
  exploit exec_thread'; try apply Hdistinct1; eauto.
  rewrite List.firstn_length, Min.min_l; [|omega]; intro Ht_steps.
  rewrite app_assoc, firstn_skipn in Hin.
  assert (n <> 0).
  { intro; clarify.
    exploit exec_keep; eauto; clarify.
    exploit distinct_in; [apply Hdistinct1 | apply Hin1 | eauto |
      apply skip_cons_neq]. }
  destruct i; try destruct x0.
  - generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit exec_keep; try apply Hsteps; eauto; clarify.
    destruct n; [|omega].
    exploit distinct_in.
    { apply Hdistinct2. }
    { apply Hin'. }
    { eauto. }
    simpl; intro; exploit skip_cons_neq; eauto; clarify.
  - assert (exists vs1 vs2 vt v0 n', n' <= length (Acq t (X' + v) ::
        mops_hb_check (W' + v) (C' + t) vs1 vs2 zt t ++
        mops_move (C' + t, t) (R' + v, t) t vt ++
        [Read t (v, n0) v0; Rel t (X' + v)]) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (Acq t (X' + v) :: mops_hb_check (W' + v) (C' + t) vs1 vs2 zt t 
        ++ mops_move (C' + t, t) (R' + v, t) t vt ++
        [Read t (v, n0) v0; Rel t (X' + v)]))
      as (vs1 & vs2 & vt & v0 & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_load_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_load_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    assert (Forall (fun a0 => ~ v_access (v, n0) a0 /\
                              loc_of a0 <> (X' + fst (v, n0), 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { exploit exec_ops; try apply Hstep'; intro Hops.
      assert (Forall (fun a0 : conc_op => a0 <> Rel t (X' + fst (v, n0))) lc).
      { rewrite Forall_forall; repeat intro; subst.
        clear Ht_steps; destruct n; clarify.
        exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
        { rewrite app_assoc, firstn_skipn; apply split_in. }
        rewrite firstn_app, in_app; intros [? | ?].
        * exploit firstn_in; eauto.
          repeat rewrite in_app; intros [? | ?]; clarify.
          exploit hb_check_instrs; eauto; clarify.
        * destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2 ++
            move (C' + t, t) (R' + v, t) tmp1)) eqn: Hrest; clarify.
          destruct n1; clarify.
          repeat rewrite app_length in *; simpl in *; omega. }
      destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha).
    apply Forall_firstn.
    constructor; clarify.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros [? _].
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x); eauto.
    + repeat constructor; simpl; intro Heq; rewrite <- Heq in *; clarify.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
  - simpl in Hfresh_i; destruct Hfresh_i.
    assert (exists vs1 vs2 vs2' vs3 v0 n', n' <= length (Acq t (X' + v) ::
        mops_hb_check (W' + v) (C' + t) vs1 vs2 zt t ++
        mops_hb_check (R' + v) (C' + t) vs3 vs2' zt t ++
        mops_move (C' + t, t) (W' + v, t) t v0 ++
        [Write t (v, n0) (eval (G1 t) e); Rel t (X' + v)]) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (Acq t (X' + v) ::
        mops_hb_check (W' + v) (C' + t) vs1 vs2 zt t ++
        mops_hb_check (R' + v) (C' + t) vs3 vs2' zt t ++
        mops_move (C' + t, t) (W' + v, t) t v0 ++
        [Write t (v, n0) (eval (G1 t) e); Rel t (X' + v)]))
      as (vs1 & vs2 & vs2' & vs3 & v0 & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_store_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_store_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    assert (Forall (fun a0 => ~ v_access (v, n0) a0 /\
                              loc_of a0 <> (X' + fst (v, n0), 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { exploit exec_ops; try apply Hstep'; intro Hops.
      assert (Forall (fun a0 : conc_op => a0 <> Rel t (X' + fst (v, n0))) lc).
      { rewrite Forall_forall; repeat intro; subst.
        clear Ht_steps; destruct n; clarify.
        exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
        { rewrite app_assoc, firstn_skipn; apply split_in. }
        rewrite firstn_app, in_app; intros [? | ?].
        * exploit firstn_in; eauto.
          repeat rewrite in_app; intros [? | [? | ?]]; clarify;
            exploit hb_check_instrs; eauto; clarify.
        * destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2 ++
            hb_check (R' + v) (C' + t) zt tmp1 tmp2 ++
            move (C' + t, t) (W' + v, t) tmp1)) eqn: Hrest; clarify.
          destruct n1; clarify.
          repeat rewrite app_length in *; simpl in *; omega. }
      destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha).
    apply Forall_firstn.
    constructor; clarify.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros [? _].
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    do 2 rewrite Forall_app; split; [|split].
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x); eauto.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x); eauto.
    + repeat constructor; simpl; intro Heq; rewrite <- Heq in *; clarify.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
  - assert (exists vs1 vs2 n', n' <= length (Acq t m0 ::
        mops_max_vc (L' + m0) (C' + t) vs1 vs2 t zt) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (Acq t m0 :: mops_max_vc (L' + m0) (C' + t) vs1 vs2 t zt))
      as (vs1 & vs2 & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_lock_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_lock_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    specialize (Hlocks m0); use Hlocks.
    assert (Forall (fun a0 : conc_op => a0 <> Rel t m0) lc).
    { rewrite Forall_forall; repeat intro; subst.
      clear Ht_steps; destruct n; clarify.
      exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
      { rewrite app_assoc, firstn_skipn; apply split_in. }
      intro; exploit firstn_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify. }
    exploit exec_ops; try apply Hstep'; intro Hops.
    assert (Forall (fun a0 => loc_of a0 <> (m0, 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    assert (Forall (fun a0 => forall o, loc_of a0 <> (L + m0, o))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as HL.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha);
      specialize (HL _ Ha).
    apply Forall_firstn.
    constructor; clarify.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_forall; intros.
    exploit in_mops_max_vc'; eauto.
    repeat intro; destruct x2; clarify.
    destruct (loc_of x); eapply HL; eauto.
    { eapply locks_spec; eauto; clarify. }
  - assert (exists vs v n', n' <= length (mops_set_vc (C + t) (L + m0) zt t vs
      ++ mops_inc_vc (C + t) v t ++ [Rel t m0]) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (mops_set_vc (C + t) (L + m0) zt t vs ++
                 mops_inc_vc (C + t) v t ++ [Rel t m0]))
      as (vs & v & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_unlock_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_unlock_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    specialize (Hlocks m0); use Hlocks.
    assert (x = tl (unlock_handler t m0 zt tmp1) ++ Unlock m0 :: rest).
    { simpl in Hi; destruct zt; clarify.
      rewrite <- app_assoc; auto. }
    clarify; exploit unlock_locked; try apply Hlocks; try apply Hsim;
      try apply Hsteps; try apply H; auto.
    { eapply exec_step_inv; eauto. }
    { rewrite Forall_forall; intros.
      exploit tl_in; eauto; intro Hi'.
      setoid_rewrite in_app in Hi'; destruct Hi'; clarify.
      exploit set_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC.
      do 2 rewrite <- app_assoc; eauto. }
    intro Hheld.
    assert (Forall (fun a0 : conc_op => a0 <> Rel t m0) lc).
    { rewrite Forall_forall; repeat intro; subst.
      clear Ht_steps; destruct n; [clarify|].
      exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
      { rewrite skipn_S_tl, app_assoc, firstn_skipn.
        rewrite tl_app; [|destruct zt; clarify].
        rewrite <- app_assoc; auto. }
      rewrite tl_app; [|destruct zt; clarify].
      rewrite firstn_app, le_minus_0, app_nil_r.
      intro Hrel; apply firstn_in, tl_in in Hrel.
      setoid_rewrite in_app in Hrel; clear - Hrel; destruct Hrel; clarify.
      exploit set_vc_instrs; eauto; clarify.
      { rewrite app_length in *; simpl in *.
        clear - Hn; destruct zt; clarify; omega. } }
    exploit exec_ops; try apply Hstep'; intro Hops.
    assert (Forall (fun a0 => loc_of a0 <> (m0, 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    assert (Forall (fun a0 => forall o, loc_of a0 <> (L + m0, o))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as HL.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha);
      specialize (HL _ Ha).
    apply Forall_firstn.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    * rewrite Forall_forall; intros.
      exploit in_mops_set_vc''; eauto.
      repeat intro; destruct x0; clarify; destruct (loc_of x); clarify.
      eapply HL; auto.
    * rewrite Forall_forall; simpl; intros ? [? | [? |?]] ?; clarify;
        destruct (loc_of x); clarify.
    * eapply locks_spec; eauto.
      rewrite Hi; repeat rewrite in_app; simpl; auto.
  - assert (exists vs1 vs2 v n', n' <= length (mops_max_vc (C + t) (C + t0)
      vs1 vs2 t zt ++ mops_inc_vc (C + t) v t) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (mops_max_vc (C + t) (C + t0) vs1 vs2 t zt ++
                 mops_inc_vc (C + t) v t))
      as (vs1 & vs2 & v & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_spawn_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_spawn_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    exploit exec_ops; try apply Hstep'; intro Hops; clarify.
    rewrite app_length in Hn; simpl in Hn.
    rewrite skipn_app, le_minus_0 in *; [|omega].
    assert (Forall (fun a0 => forall o, loc_of a0 <> (C + t0, o))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Ht0.
    { rewrite filter_app, Forall_app; split.
      + eapply protect_spawn'; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; eauto.
        { eapply exec_step_inv; eauto. }
        { repeat rewrite in_app; simpl; eauto. }
      + eapply protect_spawn_step; try apply Hsafe_i1; try apply Hsim;
          try apply Hstep'; eauto.
        { eapply exec_star_trans; eauto.
          eapply exec_step; eauto. }
        { repeat rewrite in_app; simpl; eauto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Ht0 _ Ha).
    apply Forall_firstn.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      exploit app_eq_nil; eauto; clarify. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    * rewrite Forall_forall; intros.
      exploit in_mops_max_vc'; eauto.
      repeat intro; destruct x1; try contradiction; clarify;
        destruct (loc_of x0); clarify; eapply Ht0; eauto.
    * rewrite Forall_forall; simpl; intros ? [? | [? |?]] ?; clarify;
        destruct (loc_of x0); clarify.
  - assert (exists vs1 vs2 v n', n' <= length (mops_max_vc (C + t0) (C + t)
      vs1 vs2 t zt ++ mops_inc_vc' (C + t0) v t t0) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (mops_max_vc (C + t0) (C + t) vs1 vs2 t zt ++
                 mops_inc_vc' (C + t0) v t t0))
      as (vs1 & vs2 & v & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_wait_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_wait_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    exploit exec_ops; eauto; intro Hops.
    simpl in Hin; assert (In (t0, []) P1).
    { generalize (in_split _ _ Hin); clarify.
      exploit exec_next; eauto; clarify. }
    exploit protect_wait'; try apply Hsim; try apply Hin; eauto.
    { eapply exec_step; [|eapply exec_step_inv]; eauto. }
    rewrite filter_app, Forall_app; intros (_ & Ht0).
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      rewrite skipn_all_iff in *; simpl in *; omega. }
    repeat rewrite Forall_forall in *; intros Hthread ? Ha;
      specialize (Hthread _ Ha); specialize (Ht0 _ Ha).
    apply Forall_firstn; rewrite Forall_app; split.
    * rewrite Forall_forall; intros.
      exploit in_mops_max_vc'; eauto.
      destruct x1; try contradiction; repeat intro; clarify;
        destruct (loc_of x0); clarify; eapply Ht0; eauto.
    * rewrite Forall_forall; simpl; intros ? [? | [? | ?]]; clarify.
  - generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit exec_keep; try apply Hsteps; eauto; clarify.
    destruct n; [|omega].
    exploit distinct_in.
    { apply Hdistinct2. }
    { apply Hin'. }
    { eauto. }
    simpl; intro; exploit skip_cons_neq; eauto; clarify.
Qed.

(* If the above can be proven, the original instrument_indep can be removed. *)
Corollary instrument_indep' : forall P0 G0 t o c P G lo lc P1 G1 o' c' P2 G2 i
  rest (Hdistinct : distinct P0) P0' (Hsim : state_sim P0' P0)
  (Hsafe : safe_locs P0') (Hfresh : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  (Hsafe_i : safe_instr i) (Hfresh_i : fresh tmp1 i /\ fresh tmp2 i)
  lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  (Ht1 : t < zt) (Hin : In (t, instrument_instr i t ++ rest) P1)
  (Hstep1 : exec P1 G1 t o c (Some P) G)
  (Hsteps : exec_star (Some P) G lo lc (Some P2) G2)
  P3 G3 (Hstep2 : exec P2 G2 t o' c' (Some P3) G3) (Hin' : In (t, rest) P3)
  m (Hcon : consistent (m ++ lc0 ++ opt_to_list c ++ lc ++ opt_to_list c'))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t)
            (opt_to_list c ++ lc ++ opt_to_list c')))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; eauto.
  { eapply exec_step; eauto. }
  intros (n & Hin2).
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto; intro.
  exploit step_thread; eauto; intros (? & ? & Hskip & ?).
  exploit distinct_step; eauto; intro.
  exploit distinct_in; [eauto | eauto | apply Hin' | clarify].
  rewrite skipn_app in Hskip.
  destruct (le_gt_dec (length (instrument_instr i t)) n).
  { rewrite skipn_all in Hskip; auto.
    simpl in Hskip; exploit skip_cons_neq; eauto; contradiction. }
  rewrite <- app_nil_r.
  erewrite <- filter_negb_none, <- filter_app.
  eapply instrument_indep_n; try apply Hsim; eauto.
  - rewrite skipn_app, not_le_minus_0 in Hin2; [auto | omega].
  - eapply exec_ops; eauto.
Qed.

Lemma t_minus : forall t P G lo lc P' G' t'
  (Hsteps : exec_star_t t P G lo lc P' G') (Hdiff : t' <> t),
  exec_star_minus t' P G lo lc P' G'.
Proof.
  intros; induction Hsteps; clarify; econstructor; eauto.
Qed.

Lemma first_mem : forall P G t o c P' G' (Hstep : exec P G t o c P' G')
  (Hdistinct : distinct P)
  i rest (Hinstr : In (t, instrument_instr i t ++ rest) P)
  (Hi : match i with Assign _ _ | Assert_le _ _ => False | _ => True end),
  exists a, o = Some a.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i1 & ? & ? & v & ?); clarify.
  exploit distinct_in; [eauto | apply split_in | apply Hinstr | intro Heq].
  destruct i; try destruct x2; clarify; eauto.
  - destruct zt; clarify; eauto.
  - destruct zt; clarify; eauto.
Qed.

Lemma exec_rd_ops : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  Forall (fun x => VectorClocks.thread_of x = t) (opt_to_list o).
Proof.
  intros; inversion Hstep; clarify.
Qed.
Lemma bounded_sim' : forall P P' (Hsim : state_sim P P')
  (Hbound : bounded_threads P'), Forall (fun e => fst e < zt) P.
Proof.
  induction P; clarify.
  inversion Hsim; inversion Hbound; clarify.
  constructor; [|eapply IHP; eauto].
  destruct a, y; clarify.
Qed.

Lemma noninterference : forall t P P0 (Hsim0 : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P0' (Hsim : state_sim P' P0')
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P')
  G0 lo0 lc0 G0' (Hroot0 : exec_star (Some P0) G0 lo0 lc0 (Some P0') G0')
  lo0' lc0' P1 G1 (Hroot : exec_star_t t (Some P0') G0' lo0' lc0' (Some P1) G1)
  lo lc P2 G2 (Hsteps : exec_star_minus t (Some P1) G1 lo lc (Some P2) G2)
  (Hsuffix2 : state_suffix P' P2) o c P3 G3
  (Hstep : exec P2 G2 t o c P3 G3)
  m (Hcon : consistent (m ++ lc0 ++ lc0' ++ lc ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c' => match c with Some a => loc_of c' <> loc_of a
      | None => True end) lc. 
Proof.
  intros.
  exploit distinct_steps; eauto; intro.
  assert (forall t', t' <> t -> Forall (fun c1 =>
    Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t') lc))
    (filter (fun x => negb (beq (thread_of x) t')) (lc ++ opt_to_list c)))
    as Hindep.
  { exploit state_suffix_inv; try apply Hsim; auto.
    { eapply exec_t_exec; eauto. }
    { eapply exec_minus_exec; eauto. }
    { auto. }
    intro Hsuffix1.
    exploit distinct_steps; eauto.
    { eapply exec_t_exec; eauto. }
    intro; assert (exists P1' G1' lo1' lc1',
      exec_star_t t (Some P0') G0' lo0' lc0' (Some P1') G1' /\
      exec_star_minus t (Some P1') G1' lo1' lc1' (Some P1) G1 /\
      Forall (fun c' => Forall (fun c1 => Forall (fun c2 =>
        loc_of c2 <> loc_of c1)
        (filter (fun c0 => beq (thread_of c0) (VectorClocks.thread_of c')) lc))
        (filter (fun x => negb (beq (thread_of x) (VectorClocks.thread_of c')))
        (lc ++ opt_to_list c))) lo1' /\
      (forall t' li (Hdiff : t' <> t) (Hin : In (t', li) P1)
       (Horig : Forall (fun c' => VectorClocks.thread_of c' <> t') lo1'),
       exists li0, In (t', li0) P' /\ li = instrument li0 t') /\
      consistent (m ++ lc0 ++ lc0' ++ lc1' ++ lc ++ opt_to_list c))
      as (P1' & G1' & lo1' & lc1' & Hroot0' & Hroot' & Hsep & Hinstr & Hcon').
    { do 5 eexists; eauto.
      split; [apply exec_refl_m | clarify].
      exploit Forall2_in2; eauto; intros ((?, ?) & ?); clarify.
      exploit Forall2_in1; try apply Hsim; eauto; intros ((?, ?) & ?); clarify.
      exploit exec_other_threads; eauto.
      { eapply t_minus; eauto. }
      intro; exploit distinct_in; [eauto | apply Hin | eauto | eauto]. }
    clear Hroot Hcon.
    remember (Some P1) as Pa; remember (Some P2) as Pb; generalize dependent P1;
      generalize dependent lc1'; generalize dependent lo1'; induction Hsteps;
      clarify.
    { rewrite Forall_forall; auto. }
    destruct P'0; [|inversion Hsteps].
    exploit exec_ops; eauto; intro Ht'.
    exploit exec_rd_ops; eauto; intro Ho.
    destruct (find (fun x => beq (VectorClocks.thread_of x) t'0) lo1')
      eqn: Hfind.
    { rewrite find_spec in Hfind; clarify.
      exploit nth_error_in; eauto; intro.
      rewrite Forall_forall in Hsep; exploit Hsep; eauto.
      unfold beq in Hfind21; clarify. }
    destruct (find (fun x => beq (VectorClocks.thread_of x) t') lo1')
      eqn: Hfind'.
    - destruct (eq_dec t'0 t'); clarify.
      rewrite find_spec in Hfind'; clarify.
      exploit nth_error_in; eauto; intro.
      rewrite Forall_forall in Hsep; exploit Hsep; eauto; intro Hsep'.
      rewrite <- Forall_forall in Hsep.
      exploit state_suffix_inter.
      { eauto. }
      { auto. }
      { eapply exec_step, exec_refl; eauto. }
      { eapply exec_minus_exec; eauto. }
      { auto. }
      exploit distinct_step; eauto; intros.
      exploit IHHsteps; try (eapply exec_step_inv_m; eauto); eauto.
      { rewrite Forall_app; split.
        + eapply Forall_impl; eauto; intros ? Hx; clarify.
          rewrite <- app_assoc in Hx.
          setoid_rewrite filter_app in Hx at 2.
          rewrite Forall_app in Hx; clarify.
          eapply Forall_impl; eauto; clarify.
          rewrite filter_app, Forall_app in *; clarify.
        + rewrite Forall_forall; intros.
          rewrite Forall_forall in Ho; exploit Ho; eauto; intro.
          rewrite <- app_assoc in Hsep'.
          setoid_rewrite filter_app in Hsep' at 2.
          rewrite Forall_app in Hsep'; clarify.
          unfold beq in *; clarify.
          rewrite <- e; eapply Forall_impl; eauto; clarify.
          rewrite filter_app, Forall_app in *; clarify. }
      { rewrite <- app_assoc in *; auto. }
      { intros.
        exploit in_step_rev; eauto.
        rewrite Forall_app in Horig; intros [? | [? | ?]]; clarify.
        + exploit (Hinstr t'); eauto; intros (li0 & ? & Heq).
          destruct li0; clarify.
          rewrite Heq in *; exploit first_mem; eauto.
          { destruct i; auto; clarify.
            * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                clarify.
              destruct n'; [|omega].
              exploit distinct_in; [eauto | apply Hin0 | eauto |].
              intro; eapply cons_neq; eauto.
            * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                clarify.
              destruct n'; [|omega].
              exploit distinct_in; [eauto | apply Hin0 | eauto |].
              intro; eapply cons_neq; eauto. }
          clarify.
          inversion Ho; inversion Horig2; clarify.
        + exploit in_split; eauto; clarify.
          exploit exec_next; eauto; clarify.
          exploit Forall2_in2.
          { eauto. }
          { rewrite in_app; right; simpl; right; eauto. }
          intros ((?, ?) & ?); clarify.
          contradiction H62222; rewrite in_map_iff.
          exploit Forall2_in1; try apply Hsuffix1; eauto.
          intros ((?, ?) & ?); clarify.
          do 2 eexists; eauto; auto. }
      rewrite <- app_assoc; repeat rewrite (filter_app _ (opt_to_list c0)).
      rewrite filter_none with (l := opt_to_list c0).
      rewrite filter_all with (l := opt_to_list c0).
      simpl; rewrite Forall_app; clarify.
      unfold beq in Hfind'21; destruct c0; clarify.
      constructor; auto.
      inversion Ht'; clarify.
      rewrite Forall_forall; intros.
      rewrite filter_In in *; clarify.
      rewrite Forall_forall in Hsep'; exploit Hsep'.
      { rewrite filter_In, in_app; split; eauto 2.
        unfold negb, beq in *; clarify. }
      intro X; inversion X; auto.
      + rewrite Forall_forall in *; intros.
        exploit Ht'; eauto 2; unfold negb, beq; clarify.
      + rewrite Forall_forall in *; intros.
        exploit Ht'; eauto 2; unfold negb, beq; clarify.
    - rewrite find_fail in *.
      exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
      exploit Hinstr; try apply split_in; auto.
      { eapply Forall_impl; eauto; unfold beq; clarify. }
      intros (li0 & ? & Heq); rewrite Heq in *.
      destruct li0; clarify.
      exploit instrument_indep_n; try apply Hsim0; try apply Hexec; eauto;
        try apply split_in.
      { setoid_rewrite Forall_forall in Hsafe; exploit Hsafe; eauto.
        intro X; inversion X; auto. }
      { setoid_rewrite Forall_forall in Hfresh; exploit Hfresh; eauto.
        intro X; inversion X; auto. }
      { eapply exec_star_trans; eauto.
        eapply exec_star_trans; [eapply exec_t_exec | eapply exec_minus_exec];
          eauto. }
      { exploit bounded_sim; try apply Hsim0; auto; intro.
        exploit bounded_steps; eauto; intro.
        exploit bounded_sim'; eauto.
        rewrite Forall_forall; intro X; exploit X; eauto. }
      intro X.
      use X; [|eapply exec_minus_exec; eauto].
      exploit Forall2_in1; try apply Hsuffix2; eauto.
      intros ((?, ?) & ?); clarify.
      rewrite skipn_app' in *; [|omega].
      exploit X; eauto.
      { repeat rewrite <- app_assoc in *; auto. }
      rewrite <- app_assoc; intro Hsep'.
      destruct (eq_dec t'0 t').
      + subst; setoid_rewrite filter_app at 2.
        rewrite (filter_negb_none _ Ht'); simpl.
        eapply Forall_impl; eauto; intros ? Hsep''.
        rewrite app_assoc, filter_app, Forall_app in Hsep''; clarify.
      + do 2 rewrite (filter_app _ (opt_to_list c0)).
        rewrite filter_none with (l := opt_to_list c0).
        rewrite filter_all with (l := opt_to_list c0).
        rewrite Forall_app; split.
        * destruct c0; clarify.
          inversion Ht'; clarify.
          constructor; auto.
          rewrite Forall_forall; intros.
          rewrite filter_In in *; clarify.
          rewrite filter_app, filter_app, Forall_app in Hsep'; clarify.
          rewrite Forall_forall in Hsep'1; exploit Hsep'1; eauto.
          { rewrite filter_In; unfold beq in *; clarify. }
          { intro X'; inversion X'; auto. }
        * exploit state_suffix_inter.
          { eauto. }
          { auto. }
          { eapply exec_step, exec_refl; eauto. }
          { eapply exec_minus_exec; eauto. }
          { auto. }
          exploit distinct_step; eauto; intros.
          eapply IHHsteps; try (eapply exec_step_inv_m; eauto); eauto.
          { rewrite Forall_app; split.
            + eapply Forall_impl; try apply Hsep; intros ? Hx.
              rewrite <- app_assoc in Hx.
              setoid_rewrite filter_app in Hx at 2.
              rewrite Forall_app in Hx; clarify.
              eapply Forall_impl; eauto; clarify.
              rewrite filter_app, Forall_app in *; clarify.
            + rewrite Forall_forall; intros.
              rewrite Forall_forall in Ho; exploit Ho; eauto; intro.
              rewrite Forall_forall; intros.
              rewrite filter_In in *; clarify.
              rewrite Forall_forall in Hsep'; exploit Hsep'.
              { rewrite filter_In; split; eauto. }
              repeat rewrite filter_app, Forall_app; clarify. }
          { rewrite <- app_assoc in *; auto. }
          { intros.
            exploit in_step_rev; eauto.
            rewrite Forall_app in Horig; intros [? | [? | ?]]; clarify.
            + exploit (Hinstr t'); eauto; intros (li' & ? & Heq').
              destruct li'; clarify.
              rewrite Heq' in *; exploit first_mem; eauto.
              { destruct i1; auto; clarify.
                * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                    clarify.
                  destruct n'; [|omega].
                  exploit distinct_in; [eauto | apply Hin0 | eauto |].
                  intro; eapply cons_neq; eauto.
                * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                    clarify.
                  destruct n'; [|omega].
                  exploit distinct_in; [eauto | apply Hin0 | eauto |].
                  intro; eapply cons_neq; eauto. }
              clarify.
              inversion Ho; inversion Horig2; clarify.
            + exploit in_split; eauto; clarify.
              exploit exec_next; eauto; clarify.
              exploit Forall2_in2.
              { eauto. }
              { rewrite in_app; right; simpl; right; eauto. }
              intros ((?, ?) & ?); clarify.
              contradiction H72222; rewrite in_map_iff.
              exploit Forall2_in1; try apply Hsuffix1; eauto.
              intros ((?, ?) & ?); clarify.
              do 2 eexists; eauto; auto. }
        * rewrite Forall_forall in *; intros.
          exploit Ht'; eauto 2; unfold negb, beq; clarify.
        * rewrite Forall_forall in *; intros.
          exploit Ht'; eauto 2; unfold negb, beq; clarify. }
  rewrite Forall_forall; intros.
  exploit exec_minus_ops; eauto; intro Hdiff.
  rewrite Forall_forall in Hdiff; exploit Hdiff; eauto; unfold beq; clarify.
  destruct c; auto.
  specialize (Hindep _ n); rewrite Forall_forall in Hindep.
  exploit exec_ops; eauto; intro Hc; inversion Hc; clarify.
  specialize (Hindep c); rewrite filter_In, in_app in Hindep; use Hindep;
    [|unfold negb, beq in *; clarify].
  rewrite Forall_forall in Hindep; apply Hindep.
  rewrite filter_In; unfold beq; clarify.
Qed.

Lemma init_comm : forall m1 ops1 ops2 m2 p (Hprog1 : Forall prog_op ops1),
  initialized (m1 ++ ops1 ++ ops2 ++ m2) p ->
  initialized (m1 ++ ops2 ++ ops1 ++ m2) p.
Proof.
  unfold initialized; clarify.
  repeat rewrite lower_app in H; repeat rewrite lower_app.
  repeat rewrite last_op_app in H; destruct H as [[[? | ?] | ?] | ?].
  - exists x; repeat rewrite last_op_app; auto.
  - destruct (find (fun c => writesb c p) (rev ops1)) eqn: Hfind.
    + assert (exists v, write_val c = Some v) as (v & ?).
      { rewrite find_spec in Hfind; clarify.
        exploit nth_error_in; eauto; rewrite <- in_rev; intro.
        rewrite Forall_forall in Hprog1; exploit Hprog1; eauto; intro.
        destruct c; clarify; eauto. }
      exists v; rewrite last_op_app; left.
      rewrite last_op_app; left.
      rewrite last_op_app; right; clarify.
      rewrite last_write; eauto.
    + exists x; rewrite last_op_app; left.
      rewrite last_op_app; right; rewrite Forall_app; clarify.
      rewrite find_fail, Forall_rev in Hfind.
      clear - Hfind; induction ops1; clarify.
      * unfold lower; simpl; auto.
      * rewrite lower_cons, Forall_app; inversion Hfind; clarify.
        destruct a; clarify; unfold beq in *; constructor; clarify.
  - exists x; rewrite Forall_app in *; repeat rewrite last_op_app; clarify.
  - exists x; repeat rewrite last_op_app; repeat rewrite Forall_app in *;
      clarify.
Qed.      

Corollary init_comm' : forall m1 ops1 ops2 p (Hprog1 : Forall prog_op ops1)
  (Hprog2 : Forall prog_op ops2),
  initialized (m1 ++ ops1 ++ ops2) p <-> initialized (m1 ++ ops2 ++ ops1) p.
Proof.
  intros; split; intro.
  - rewrite <- (app_nil_r (m1 ++ ops1 ++ ops2)), <- app_assoc, <- app_assoc
      in H.
    exploit init_comm; try apply H; auto; rewrite app_nil_r; auto.
  - rewrite <- (app_nil_r (m1 ++ ops2 ++ ops1)), <- app_assoc, <- app_assoc
      in H.
    exploit init_comm; try apply H; auto; rewrite app_nil_r; auto.
Qed.

Lemma first_finished : forall P P0 (Hsim0 : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P0' (Hsim : state_sim P' P0')
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P')
  G0 lo0 lc0 G0' (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P0') G0')
  t P3 (Hsuffix : state_suffix P' P3) 
  P2 G2 lo' lc' G3 (Hsteps2 : exec_star (Some P2) G2 lo' lc' (Some P3) G3)
  lo0' lc0' P1 G1
  (Hsteps0 : exec_star_t t (Some P0') G0' lo0' lc0' (Some P1) G1)
  lo lc  (Hsteps1 : exec_star_minus t (Some P1) G1 lo lc (Some P2) G2)
  o c P4 G4 i li (Hin0 : In (t, i :: li) P')
  (Hin : In (t, last (instrument_instr i t) (Lock 0) :: instrument li t) P3)
  (Hstep : exec P3 G3 t o c (Some P4) G4)
  m (Hcon : consistent (m ++ lc0 ++ lc0' ++ lc ++ lc' ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1 P' G' lo2 lc2, iexec P0' G0' t lo1 lc1 P' G' /\
    exec_star (Some P') G' lo2 lc2 (Some P4) G4 /\
    mem_ext (m ++ lc0 ++ lc1 ++ lc2)
            (m ++ lc0 ++ lc0' ++ lc ++ lc' ++ opt_to_list c).
Proof.
   intros until G3; intro.
  remember (Some P2) as Pa; remember (Some P3) as Pb; generalize dependent P2;
    induction Hsteps2; clarify.
  - exploit distinct_steps; eauto; intro.
    exploit state_suffix_inv; try apply Hsim; auto.
    { eapply exec_t_exec; eauto. }
    { eapply exec_minus_exec; eauto. }
    { auto. }
    intro; exploit Forall2_in1; eauto; intros ((?, ?) & ?); clarify.
    exploit distinct_steps; eauto.
    { eapply exec_t_exec; eauto. }
    intro; exploit state_suffix_stable; try eapply exec_minus_exec; eauto.
    exploit noninterference; try apply Hroot; eauto.
    intro X; exploit X; eauto.
    clarify; exploit exec_minus_reorder; try apply Hsteps1; eauto.
    { do 2 rewrite app_assoc in Hcon; eauto. }
    intros (P1' & ?); clarify.
    assert (In (t, instrument li t) P1').
    { exploit Forall2_in1; try apply H; eauto; intros ((?, ?) & ?); clarify.
      exploit exec_other_threads; eauto; intro.
      exploit distinct_steps; eauto.
      { eapply exec_minus_exec; eauto. }
      intro; exploit distinct_in; [eauto | apply Hin | eauto | intro Heq].
      rewrite <- Heq in *.
      exploit exec_result; eauto; intros (? & ? & ? & ? & v & ?); clarify.
      exploit distinct_in; [eauto | apply split_in | eauto | clarify].
      destruct (instr_result t (last (instrument_instr i t) (Lock 0)) (G1 t) v)
        as [((((?, ?), ?), ?), ?)|]; clarify.
      apply split_in. }
    exploit exec_t_iexec; try apply H.
    { exploit Forall2_in1; try apply Hsim; eauto; intros ((?, ?) & ?); clarify;
        eauto. }
    { exploit bounded_sim; try apply Ht; eauto; intro Hbound.
      eapply bounded_steps in Hbound; eauto.
      eapply bounded_steps in Hbound; [|eapply exec_t_exec; eauto].
      setoid_rewrite Forall_forall in Hbound; exploit Hbound; eauto; clarify. }
    { setoid_rewrite Forall_forall in Hfresh; exploit Hfresh; eauto; intro X'.
      inversion X'; clarify. }
    { eapply exec_step_inv_t; eauto. }
    { auto. }
    { do 2 rewrite app_assoc in Hcon; rewrite <- app_nil_r in Hcon.
      rewrite <- app_assoc, <- (app_assoc lc) in Hcon.
      rewrite <- loc_comm_ops_SC, <- app_assoc in Hcon.
      instantiate (1 := m ++ lc0).
      eapply consistent_app_SC; rewrite <- app_assoc, <- (app_assoc lc0');
        eauto.
      { destruct c; clarify. }
      { eapply prog_step; eauto. }
      { eapply prog_steps, exec_minus_exec; eauto. } }
    { intros; eapply init_steps; eauto.
      eapply prog_steps; eauto. }
    intro; do 7 eexists; eauto.
    split; [eapply exec_minus_exec; eauto|].
    split; intro; repeat rewrite <- app_assoc.
    + do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0)); apply loc_comm_ops_SC.
      { destruct c; clarify. }
      { eapply prog_step; eauto. }
      { eapply prog_steps, exec_minus_exec; eauto. }
    + do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0)); apply init_comm'.
      { eapply prog_step; eauto. }
      { eapply prog_steps, exec_minus_exec; eauto. }
  - exploit distinct_steps; eauto; intro.
    destruct P'0; [|inversion Hsteps2].
    specialize (IHHsteps2 _ eq_refl).
    destruct (eq_dec t0 t).
    + subst.
      exploit state_suffix_inv; try apply Hsim; auto.
      { eapply exec_star_trans; [eapply exec_t_exec | eapply exec_minus_exec];
          eauto. }
      { eapply exec_step; eauto. }
      { auto. }
      intro; exploit state_suffix_inv.
      { eauto. }
      { auto. }
      { eapply exec_t_exec; eauto. }
      { eapply exec_minus_exec; eauto. }
      { auto. }
      exploit distinct_steps; eauto 2.
      { eapply exec_t_exec; eauto. }
      intros; exploit state_suffix_stable; try eapply exec_minus_exec, Hsteps1;
        eauto.
      exploit noninterference; try apply Hroot; eauto 2.
      intro X; exploit X; eauto 2.
      { eapply consistent_app_SC.
        do 4 rewrite <- app_assoc; rewrite <- app_assoc in Hcon; eauto. }
      clarify; exploit exec_minus_reorder; try apply Hsteps1; eauto.
      { eapply consistent_app_SC.
        rewrite <- app_assoc in Hcon.
        do 4 rewrite app_assoc in Hcon.
        rewrite <- (app_assoc _ lc1) in Hcon; eauto. }
      clarify; exploit IHHsteps2.
      { eapply exec_step_inv_t; eauto. }
      { eauto. }
      { eauto. }
      { auto. }
      { eauto. }
      { rewrite <- app_assoc, app_assoc, app_assoc in Hcon.
        rewrite loc_comm_ops_SC in Hcon.
        rewrite <- app_assoc, <- app_assoc, (app_assoc lc0') in Hcon; eauto.
        { eapply Forall_impl; eauto; clarify.
          destruct c; clarify. }
        { eapply prog_steps, exec_minus_exec; eauto. }
        { eapply prog_step; eauto. } }
      { auto. }
      { auto. }
      { auto. }
      clarify; do 7 eexists; eauto.
      split; eauto.
      etransitivity; eauto.
      split; intro; repeat rewrite <- app_assoc.
      * do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0));
          apply loc_comm_ops_SC.
        { destruct c; clarify. }
        { eapply prog_step; eauto. }
        { eapply prog_steps, exec_minus_exec; eauto. }
      * do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0));
          split; apply init_comm.  
        { eapply prog_step; eauto. }
        { eapply prog_steps, exec_minus_exec; eauto. }
    + exploit IHHsteps2; eauto 2.
      { eapply exec_step_inv_m; eauto. }
      { rewrite <- app_assoc in *; auto. }
      intros (? & ? & ? & ? & ? & ? & ? & ? & Hm).
      do 7 eexists; eauto; split; eauto.
      rewrite <- app_assoc in *; auto.
Qed.

Corollary first_finished' : forall P P0 (Hsim : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P1 (Hsim : state_sim P' P1)
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P')
  G0 lo0 lc0 G1 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  t P3 (Hsuffix : state_suffix P' P3)
  lo' lc' G3 (Hsteps2 : exec_star (Some P1) G1 lo' lc' (Some P3) G3)
  o c P4 G4 i li (Hin0 : In (t, i :: li) P')
  (Hin : In (t, last (instrument_instr i t) (Lock 0) :: instrument li t) P3)
  (Hstep : exec P3 G3 t o c (Some P4) G4)
  m (Hcon : consistent (m ++ lc0 ++ lc' ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1 P' G' lo2 lc2, iexec P1 G1 t lo1 lc1 P' G' /\
    exec_star (Some P') G' lo2 lc2 (Some P4) G4 /\
    mem_ext (m ++ lc0 ++ lc1 ++ lc2) (m ++ lc0 ++ lc' ++ opt_to_list c).
Proof.
  intros; eapply first_finished with (lc0' := [])(lc := []); try apply Hroot;
    eauto; constructor.
Qed.

Lemma sim_next_iexec : forall P P1 P2 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hfresh : fresh_tmps P)
  P0 P0' (Hsim : state_sim P0 P0') (Hdistinct : distinct P0')
  (Hsafe : safe_locs P0) (Hfresh : fresh_tmps P0)
  (Ht : Forall (fun e => fst e < zt) P0)
  (Hlocks : forall l, locks l P0' -> good_lock (l, 0) P0')
  (Hlocks2 : forall l, l < zl -> well_locked l P0')
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0')
  (Hvars : forall v, v < zv -> good_var v P0')
  (Hspawns : safe_spawns P0') (Hwaits : safe_waits P0')
  G0 lo0 lc0 G1 (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P1) G1)
  lo lc G2 (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2)
  m (Hcon : consistent (m ++ lc0 ++ lc))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  state_suffix P P2 \/ exists t lo1 lc1 P' G' lo2 lc2,
    iexec P1 G1 t lo1 lc1 P' G' /\ exec_star (Some P') G' lo2 lc2 (Some P2) G2
    /\ mem_ext (m ++ lc0 ++ lc1 ++ lc2) (m ++ lc0 ++ lc).
Proof.
   intros; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P2; rewrite exec_rev in Hsteps; induction Hsteps;
    clarify.
  { left; apply sim_suffix; auto. }
  rewrite <- exec_rev in Hsteps.
  use IHHsteps; [|eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto].
  specialize (IHHsteps _ eq_refl); destruct IHHsteps.
  - exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    exploit distinct_steps; eauto; intro.
    exploit distinct_steps; eauto; intro.
    subst; exploit state_suffix_inv'; eauto; intros (? & li & ? & n & ?);
      clarify.
    destruct li; [rewrite skipn_nil in *|]; clarify.
    destruct (length (skipn n (instrument_instr i0 t))) eqn: Hlen.
    { rewrite skipn_length in Hlen; omega. }
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    destruct n0.
    + right; rewrite skipn_app, not_le_minus_0 in *; [|omega].
      destruct (skipn n (instrument_instr i0 t)) eqn: Hlast; clarify.
      destruct l; clarify.
      exploit first_finished'; try apply Hroot; eauto.
      intro X; exploit X; eauto; try apply split_in.
      rewrite <- (app_nil_r (instrument_instr _ _)) in Hlast.
      exploit skipn_last; eauto.
      instantiate (1 := Lock 0); clarify; apply split_in.
    + left; destruct o0.
      { destruct i; clarify.
        assert (nth_error (instrument_instr i0 t) n = Some (Spawn t0 li0)).
        { rewrite <- (plus_O_n n), <- skipn_nth.
          rewrite skipn_app, not_le_minus_0 in *; [|omega].
          destruct (skipn n (instrument_instr i0 t)); clarify. }
        exploit spawn_in_handler'; eauto; intros (? & ? & ? & Hn).
        rewrite skipn_length in Hlen; omega. }
      simpl; apply Forall2_app; [|constructor]; clarify.
      rewrite skipn_length in Hlen; exists (S n); split; [omega|].
      generalize (instrument_nonnil i0 t); destruct (instrument_instr i0 t);
        clarify.
      symmetry; eapply skipn_cons; eauto.
  - clarify; right; do 8 eexists; eauto.
    split; [eapply exec_step_inv; eauto|].
    repeat rewrite app_assoc in *; apply mem_ext_app; auto.
Qed.


Fixpoint legal_spawn_instr (i: instr) :=
  let legal_spawn := fix f p :=
   match p with
     | [] => True
     | instr1::ins=> legal_spawn_instr instr1 /\ (f ins)
   end
  in 
  match i with
   | Spawn u li => u < zt /\ legal_spawn li 
   | _          => True
  end.

Fixpoint legal_spawn (p : prog) :=
  match p with
    | [] => True
    | instr1::ins => legal_spawn_instr instr1 /\ legal_spawn ins
  end.                 

Definition legal_tids (P:list (tid * prog)) :=
  Forall (fun e => legal_spawn (snd e)) P /\ Forall (fun e => fst e < zt) P .


Fixpoint spawn_wait_other_inst t i:=
  let spawn_wait_other := fix f t' p:=
                       match p with
                         | [] => True
                         | i'::insts => spawn_wait_other_inst t' i'/\ f t' insts
                       end
                         in
  match i with
    | Spawn u li => u <> t /\ spawn_wait_other u li
    | Wait u     => u <> t                                           
    | _ => True
  end.

Fixpoint spawn_wait_other t p:=
  match p with
    | [] => True
    | i'::insts => spawn_wait_other_inst t i' /\ spawn_wait_other t insts
  end.

Definition spawn_wait_other_prog (tps: list (tid * list instr)):=
  Forall (fun tp => spawn_wait_other (fst tp) (snd tp) ) tps. 
  

Lemma spawn_wait_other_prog_step : forall P G o c P' G' t
                               (Hlegal: spawn_wait_other_prog P)
                               (Hstep: exec P G t o c (Some P') G'),
                          spawn_wait_other_prog P'.
Proof.
  intros. unfold spawn_wait_other_prog,spawn_wait_other in *.
  inversion Hstep; clarify; rewrite Forall_app in * ; clarify;
  inversion Hlegal2; clarify. 
Qed.


Lemma legal_tids_step : forall P G o c P' G' t
                               (Hlegal: legal_tids P)
                               (Hstep: exec P G t o c (Some P') G'),
                          legal_tids P'.
Proof.
  intros. unfold legal_tids in *; split.
  -inversion Hstep; clarify; rewrite Forall_app in * ; clarify;
   inversion Hlegal12; clarify; inversion H1; clarify;
   apply Forall_cons; clarify.
  -inversion Hstep; clarify; rewrite Forall_app in *; clarify;
   inversion Hlegal22; clarify.
   inversion Hlegal12; clarify.
Qed.

Lemma legal_tids_steps : forall P G lo lc P' G'
                                (Hlegal : legal_tids P)
                                (Hsteps: exec_star (Some P) G lo lc (Some P') G'),
                           legal_tids P'.
Proof.
  intros. remember (Some P) as Pa; remember (Some P') as Pb;
  generalize dependent P; induction Hsteps; clarify.
  (* base case discharged automatically *)
  destruct P'0; clarify.
  -specialize(IHHsteps s). apply IHHsteps; auto.
   eapply legal_tids_step with (P:=P0); eauto.
  -inversion Hsteps.
Qed.
                     

Lemma state_sim_step' : forall P1 P2 G2 t lo lc P2' G2'
  (Hdistinct : distinct P2) (HPsim : state_sim P1 P2) (Hsafe : safe_locs P1)
  (Htmps : fresh_tmps P1) (Hiexec : iexec P2 G2 t lo lc P2' G2') ,
  exists P1', state_sim P1' P2' /\ safe_locs P1' /\ fresh_tmps P1'.
Proof.
   intros.
  inversion Hiexec; subst; exploit state_sim_inv'; eauto 2;
    intros (P1a & [|??] & P1b & ? & ? & ? & ?); clarify;
    try (exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
         contradiction); exploit state_sim_inv; eauto; clarify.
  - exploit (instrument_incom (Assign a e)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Load a (x, o))).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Store (x, o) e)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Lock m)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Unlock m)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit spawn_in_instrument.
    { instantiate (2 := (i :: l)); simpl.
      setoid_rewrite <- H2; rewrite in_app; clarify. }
    clarify.
    exploit (instrument_incom (Spawn u x)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    { apply (Forall2_cons (u, x)); eauto. }
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
    rewrite safe_instrs in *.
    repeat split; auto; repeat constructor; auto.
    apply Forall_and; split; rewrite <- list_fresh_iff; auto.
  - exploit (instrument_incom (Wait u)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Assert_le e1 e2)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hsafei; inversion Hfreshi; clarify.
Qed.


Lemma state_sim_step_legal : forall P1 P2 G2 t lo lc P2' G2'
  (Hdistinct : distinct P2) (HPsim : state_sim P1 P2) (Hsafe : safe_locs P1)
  (Htmps : fresh_tmps P1) (Hiexec : iexec P2 G2 t lo lc P2' G2') (Hlegal: legal_tids P1),
  exists P1', state_sim P1' P2' /\ safe_locs P1' /\ fresh_tmps P1' /\ legal_tids P1'.
Proof.
   intros.
  inversion Hiexec; subst; exploit state_sim_inv'; eauto 2;
    intros (P1a & [|??] & P1b & ? & ? & ? & ?); clarify;
    try (exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
         contradiction); exploit state_sim_inv; eauto; clarify.
  - exploit (instrument_incom (Assign a e)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
    inversion Hsafei; inversion Hfreshi; clarify. 
  - exploit (instrument_incom (Load a (x, o))).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Store (x, o) e)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Lock m)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Unlock m)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit spawn_in_instrument.
    { instantiate (2 := (i :: l)); simpl.
      setoid_rewrite <- H2; rewrite in_app; clarify. }
    clarify.
    exploit (instrument_incom (Spawn u x)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    { apply (Forall2_cons (u, x)); eauto. }
    unfold safe_locs, fresh_tmps,legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
    rewrite safe_instrs in *.
    repeat split; auto; repeat constructor; auto.
    apply Forall_and; split; rewrite <- list_fresh_iff; auto.
  - exploit (instrument_incom (Wait u)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
  - exploit (instrument_incom (Assert_le e1 e2)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, legal_tids in *; repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];inversion Hlegal12 as [|?? Hlegal1i]; inversion Hlegal22 as [|?? Hlegal2i];
      inversion Hsafei; inversion Hfreshi; clarify.
Qed.

Instance mem_ext_sym : RelationClasses.Symmetric mem_ext.
Proof.
  intros ?? (? & ?).
  split; symmetry; auto.
Qed.

Lemma exec_iexec1 : forall P P' G' G lo lc
  (Hexec : exec_star (Some P) G lo lc (Some P') G')
  P1 (HP : state_sim P1 P) (Hsafe : safe_locs P1) (Hfresh : fresh_tmps P1)
  P0 (Hdistinct0 : distinct P0) P0' (Hsim0 : state_sim P0' P0)
  (Hsafe0 : safe_locs P0') (Hfresh0 : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0)
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  G0 lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P) G)
  m (Hcon : consistent (m ++ lc0 ++ lc))
  (Hinit_l : forall l, l < zl -> initialized m (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m (X' + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo'1 lc'1 G2' P2' lo'2 lc'2, safe_locs P2' /\ fresh_tmps P2' /\
    state_suffix P2' P' /\ iexec_star P G lo'1 lc'1 (instrument_prog P2') G2' /\
    exec_star (Some (instrument_prog P2')) G2' lo'2 lc'2 (Some P') G' /\
    mem_ext (m ++ lc0 ++ lc'1 ++ lc'2) (m ++ lc0 ++ lc).
Proof.
  intros ???.
  remember (size P) as z; generalize dependent P;
    induction z using lt_wf_ind; clarify.
  exploit distinct_steps; eauto; intro Hdistinct.
  exploit sim_next_iexec; try apply Hroot; eauto.
  intros [? | (t & lo1 & lc1 & Pt & Gt & lo2 & lc2 & Hiexec & Hrest & Hcon')].
  { rewrite instrumented_iff in HP; subst.
    do 6 eexists; split; [|split; [|split; [|split; [apply iexec_refl|]]]];
      auto.
    split; [eauto | reflexivity]. }
  clarify; exploit iexec_decr; eauto; intro Hlt.
  specialize (H _ Hlt _ eq_refl _ _ _ Hrest).
  exploit state_sim_step'; eauto; intros (? & Hsim' & ?).
  specialize (H _ Hsim'); clarify.
  specialize (H _ Hdistinct0 _ Hsim0); clarify.
  exploit H; auto.
  - eapply exec_star_trans; eauto.
    eapply iexec_exec; eauto.
  - destruct Hcon' as (Hcon' & ?).
    specialize (Hcon' []); repeat rewrite app_nil_r in Hcon'.
    rewrite <- app_assoc, Hcon'; auto.
  - clarify; do 7 eexists; eauto; repeat (split; [solve [eauto]|]).
    split; [|split; eauto 2].
    + eapply iexec_step; eauto.
    + repeat rewrite <- app_assoc in *.
      etransitivity; eauto.
Qed.

Lemma final_suffix : forall P P' (Hsuffix : state_suffix P P')
  (Hfinal : final_state (Some P')), final_state (Some P).
Proof.
  induction P; clarify.
  inversion Hsuffix; clarify.
  destruct a, y; clarify.
  inversion Hfinal; clarify.
  constructor; [|eapply IHP; eauto].
  rewrite skipn_all_iff in *; destruct l; clarify.
  rewrite app_length in *; omega.
Qed.

Lemma final_steps : forall P (Hfinal : final_state P)
  G lo lc P' G' (Hsteps : exec_star P G lo lc P' G'),
  P' = P /\ G' = G /\ lo = [] /\ lc = [].
Proof.
  intros; inversion Hsteps; clarify.
  inversion Hexec; subst; rewrite Forall_app in *; clarify;
    inversion Hfinal2; clarify.
Qed.

Lemma instrument_final : forall P (Hfinal : final_state (Some P)),
  instrument_prog P = P.
Proof.
  induction P; clarify.
  destruct a; inversion Hfinal; clarify.
  rewrite IHP; clear IHP; clarify.
Qed.

Lemma exec_iexec : forall P P' (Hfinal : final_state (Some P')) G' G lo lc
  (Hexec : exec_star (Some P) G lo lc (Some P') G')
  P1 (HP : state_sim P1 P) (Hsafe : safe_locs P1) (Hfresh : fresh_tmps P1)
  P0 (Hdistinct0 : distinct P0) P0' (Hsim0 : state_sim P0' P0)
  (Hsafe0 : safe_locs P0') (Hfresh0 : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0)
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  G0 lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P) G)
  m (Hcon : consistent (m ++ lc0 ++ lc))
  (Hinit_l : forall l, l < zl -> initialized m (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m (X' + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo' lc', iexec_star P G lo' lc' P' G' /\
    mem_ext (m ++ lc0 ++ lc') (m ++ lc0 ++ lc).
Proof.
  intros.
  exploit exec_iexec1; try apply Hexec; try apply Hroot; eauto.
  intros (? & ? & ? & P2 & ?); clarify.
  exploit final_suffix; eauto; intro.
  rewrite instrument_final in *; auto.
  exploit final_steps; eauto; clarify.
  rewrite app_nil_r in *; eauto.
Qed.

Corollary exec_iexec' : forall P P' (Hfinal : final_state (Some P')) G' G lo lc
  (Hexec : exec_star (Some P) G lo lc (Some P') G')
  P1 (HP : state_sim P1 P) (Hsafe : safe_locs P1) (Hfresh : fresh_tmps P1)
  (Hdistinct : distinct P) (Ht : Forall (fun e => fst e < zt) P1)
  (Hlocks : forall l, locks l P -> good_lock (l, 0) P)
  (Hlocks2 : forall l, l < zl -> well_locked l P)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P)
  (Hvars : forall v, v < zv -> good_var v P)
  (Hspawns : safe_spawns P) (Hwaits : safe_waits P)
  m (Hcon : consistent (m ++ lc))
  (Hinit_l : forall l, l < zl -> initialized m (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m (X' + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo' lc', iexec_star P G lo' lc' P' G' /\ mem_ext (m ++ lc') (m ++ lc).
Proof.
  intros; eapply exec_iexec with (lc0 := []); eauto; apply exec_refl.
Qed.

Inductive fail_iexec P t :
  list operation -> list conc_op -> (*state -> env -> *)Prop :=
  | fail_raw P1 P2 a x o v1 v2 rest vs1 vs2
    (Hload: P=P1++(t, load_handler t x zt ++
                                   Load a (x, o) :: Unlock (X + x) :: rest) :: P2)
      (Hgt : first_gt vs1 vs2 = Some (v1,v2) )  (Hlen1: length vs1 <=zt) (Hlen2: length vs2 <=zt):
      fail_iexec P  t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t )
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t)
  | fail_waw P1 P2 x o e v1 v2 rest vs1 vs2
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hgt : first_gt vs1 vs2 = Some (v1,v2) ) (Hlen1: length vs1 <=zt) (Hlen2: length vs2 <=zt)  :
      fail_iexec P  t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t )
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t )
  | fail_war P1 P2 x o e v1 v2 rest vs1 vs2 vs3
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hle : first_gt vs1 vs2 = None ) (Hgt: first_gt vs3 vs2 = Some (v1, v2) )
      (Hlen3: length vs3 = zt) (Hlen2: length vs2 = zt):
      fail_iexec P  t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
                       events_hb_check (R + x) (C + t) vs3 vs2 t)
                  (Acq t (X + x) ::
                       mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                  mops_hb_check (R+x) (C + t) vs3 vs2 zt t ).

Definition no_asserts := state_forall
  (fun i => match i with Assert_le _ _ => False | _ => True end).

Lemma hb_check_fail_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt
  Pa Pb (HP : P = Pa ++ (t, hb_check src tgt z tmp1 tmp2 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G')
  n (Hn : n < length (hb_check src tgt z tmp1 tmp2))
  (Hin' : In (t, skipn n (hb_check src tgt z tmp1 tmp2) ++ li) P')
  o c G'' (Hfail : exec P' G' t o c None G''),
  exists vs1 vs2 k, lo = events_hb_check src tgt vs1 vs2 t /\
    lc = mops_hb_check src tgt vs1 vs2 z t /\
    first_gt vs1 vs2 = Some (last vs1 0, last vs2 0) /\ 0 < k <= z /\
    length vs1 = k /\ length vs2 = k /\
    (forall i (Hi : i < k - 1) v1 v2 (Hv1 : nth_error vs1 i = Some v1)
      (Hv2 : nth_error vs2 i = Some v2), v1 <= v2) /\
    G' = upd_env (upd_env G t tmp1 (last vs1 (G t tmp1)))
                 t tmp2 (last vs2 (G t tmp2)).
Proof.
  induction z; clarify; [omega|].
  inversion Hfail; clarify.
  inversion Ht; clarify.
  { exploit distinct_thread; eauto; clarify. }
  exploit exec_next; eauto; intros (v1 & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clarify.
  { exploit distinct_thread; eauto; clarify. }
  exploit exec_next; eauto; intros (v2 & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'0; clarify.
  { exploit distinct_thread; eauto; clarify.
    exists [v1], [v2]; simpl.
    rewrite upd_same, upd_old, upd_same in Hfail0; auto.
    rewrite <- leb_le in Hfail0; clarify.
    exists 1; clarify.
    split; [omega | clarify].
    omega. }
  exploit exec_next; eauto; simpl; intros (? & ?).
  rewrite upd_same, upd_assoc, upd_same in *; auto.
  destruct (le_dec v1 v2); clarify; [|inversion Hexec'1].
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
  destruct n; clarify.
  { exploit distinct_in; [eauto | apply Hin' | apply split_in | clarify]. }
  destruct n; clarify.
  { exploit distinct_in; [eauto | apply Hin' | apply split_in | clarify]. }
  destruct n; clarify.
  { exploit distinct_in; [eauto | apply Hin' | apply split_in | clarify].
    exploit exec_mono; try eapply exec_t_exec, Hexec'1; try apply split_in;
      clarify.
    exploit skip_cons_neq; eauto; contradiction. }
  exploit IHz; try apply eq_refl; eauto.
  { omega. }
  intros (vs1 & vs2 & k & ? & ? & ? & ? & ? & ? & Hle & ?);
    exists (v1 :: vs1), (v2 :: vs2), (S k); clarify.
  rewrite <- leb_le in l; clarify.
  rewrite last_cons, last_cons; try (intro; clarify; omega).
  clarify.
  split; [omega | clarify].
  rewrite upd_overwrite, upd_same.
  rewrite upd_three, upd_old, upd_same, upd_assoc; auto.
  do 2 rewrite last_cons'; auto.
  split; auto.
  rewrite leb_le in cond; destruct i; clarify.
  eapply Hle; eauto; omega.
Qed.

Lemma exec_star_t_steps : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t (Some P) G lo lc P' G'),
  exists n, t_steps P G t n lo lc P' G'.
Proof.
  intros; remember (Some P) as Pa; generalize dependent P; induction Hsteps;
    clarify.
  - exists 0; simpl; auto.
  - destruct P'.
    + specialize (IHHsteps _ eq_refl); destruct IHHsteps as (n & ?);
        exists (S n); simpl.
      repeat eexists; eauto.
      { apply exec_refl_m. }
      clarify.
    + inversion Hsteps; clarify.
      exists 1; simpl.
      do 5 eexists; eauto.
      do 4 eexists; exists [], []; split; [apply exec_refl_m | clarify].
Qed.

Lemma hb_check_match_n : forall C1 C2 t z vs1 vs2 k (Hk : k <= z)
  (Hlen1 : length vs1 = k) (Hlen2 : length vs2 = k)
  (Hle : forall i (Hi : i < k - 1) v1 v2 (Hv1 : nth_error vs1 i = Some v1)
    (Hv2 : nth_error vs2 i = Some v2), v1 <= v2)
  m (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t)) n (Hlt : n < k), 
  exists v, nth_error vs2 n = Some v /\ can_read m (C2, z - n - 1) v.
Proof.
  induction z; clarify; [omega|].
  destruct vs1, vs2; clarify; try omega.
  destruct n.
  - do 2 eexists; simpl; eauto.
    rewrite <- minus_n_O.
    rewrite read_noop_SC in Hcon.
    eapply can_read_thread'.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
    { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  - exploit (IHz vs1 vs2 (length vs1)); auto; try omega.
    { intros; specialize (Hle (S i)); use Hle; [clarify | omega]. }
    { exploit (Hle 0); simpl; eauto.
      { omega. }
      rewrite <- leb_le; clarify.
      rewrite read_noop_SC, read_noop_SC in Hcon; eauto.
      { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
      { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. } }
    { instantiate (1 := n); omega. }
    eauto.
Qed.

Corollary hb_check_twice_n : forall C1 C1' C2 t z vs1 vs1' vs2 vs2' k
  (Hlen1 : length vs1 = z) (Hlen1' : length vs1' = k) (Hlen2 : length vs2 = z)
  (Hlen2' : length vs2' = k) (Hle : first_gt vs1 vs2 = None) (Hk : k <= z)
  (Hle' : forall i (Hi : i < k - 1) v1 v2 (Hv1 : nth_error vs1' i = Some v1)
    (Hv2 : nth_error vs2' i = Some v2), v1 <= v2)
  m (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t ++
                             mops_hb_check C1' C2 vs1' vs2' z t))
  (Hinit : forall o, o < z -> initialized m (C2, o)),
  vs2' = firstn k vs2.
Proof.
  intros.
  apply list_ext; intro n.
  destruct (lt_dec n k).
  rewrite app_assoc in Hcon.
  exploit hb_check_match_n.
  { apply Hk. }
  { apply Hlen1'. }
  { apply Hlen2'. }
  { auto. }
  { eauto. }
  { eauto. }
  intros (? & ? & Hread').
  exploit consistent_app_SC; eauto; intro Hcon'.
  generalize (hb_check_match _ _ _ _ _ Hlen1 Hlen2 Hle _ Hcon'); intro Hvs2.
  specialize (Hvs2 n); use Hvs2; [|omega].
  destruct Hvs2 as (? & ? & Hread).
  unfold can_read in Hread'; rewrite <- app_assoc in Hread'.
  rewrite reads_noops_SC in Hread'; auto; [|apply mops_hb_check_read].
  exploit can_read_unique.
  { eapply consistent_app_SC; eauto. }
  { specialize (Hinit (z - n - 1)).
    use Hinit; [eauto | omega]. }
  { apply Hread. }
  { apply Hread'. }
  clarify.
  rewrite nth_error_firstn; clarsimp.
  { rewrite nth_error_firstn; clarify.
    destruct (nth_error vs2' n) eqn: Hn; auto.
    exploit nth_error_lt; eauto; omega. }
Qed.

Lemma events_hb_check_extend : forall src tgt vs1 vs2 t vs1' vs2'
  (Hfail : first_gt vs1 vs2 <> None),
  events_hb_check src tgt (vs1 ++ vs1') (vs2 ++ vs2') t =
  events_hb_check src tgt vs1 vs2 t.
Proof.
  induction vs1; clarify.
  destruct vs2; clarify.
  rewrite IHvs1; auto.
Qed.

Lemma mops_hb_check_extend : forall src tgt z vs1 vs2 t vs1' vs2'
  (Hfail : first_gt vs1 vs2 <> None),
  mops_hb_check src tgt (vs1 ++ vs1') (vs2 ++ vs2') z t =
  mops_hb_check src tgt vs1 vs2 z t.
Proof.
  induction z; destruct vs1, vs2; clarify.
  rewrite IHz; auto.
Qed.

Lemma first_gt_extend : forall vs1 vs2 x vs1' vs2'
  (Hfirst : first_gt vs1 vs2 = Some x),
  first_gt (vs1 ++ vs1') (vs2 ++ vs2') = Some x.
Proof.
  induction vs1; destruct vs2; clarify.
Qed.

Lemma exec_t_fail_iexec : forall t P G lo lc P' G' i li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr i t ++ li) P)
  (Hi : match i with Assert_le _ _ => False | _ => True end)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G')
  n (Hn : n < length (instrument_instr i t))
  (Hin' : In (t, skipn n (instrument_instr i t) ++ li) P')
  o c G'' (Hfail : exec P' G' t o c None G'')
  m (Hcon : consistent (m ++ lc ++ opt_to_list c))
  (HC_init : forall o, o < zt -> initialized m (C + t, o)),
  fail_iexec P t lo lc.
Proof.
  intros; inversion Hfail; clarify.
  exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
  exploit distinct_in; [eauto | apply Hin' | apply split_in | intro Heq].
  destruct i; try destruct x; clarify.
  - destruct n; clarify; omega.
  - inversion Ht; clear Ht; clarify.
    { exploit distinct_in; [eauto | apply Hin | apply split_in | clarify]. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (i & ?); clarify.
    exploit distinct_step; eauto; intro.
    repeat rewrite <- app_assoc in *.
    destruct n; clarify.
    destruct (le_gt_dec (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)) n).
    { rewrite skipn_app, skipn_all in Heq; auto.
      destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)) eqn: Hn';
        clarify.
      destruct n1; clarify.
      destruct n1; clarify.
      destruct n1; clarify.
      rewrite app_length in *; simpl in *; omega. }
    rewrite <- Heq in Hexec'.
    exploit hb_check_fail_exec; eauto.
    { rewrite skipn_app, not_le_minus_0; [|omega].
      rewrite <- app_assoc; simpl; apply split_in. }
    { rewrite Heq; eauto. }
    clarify.
    eapply fail_raw; eauto; try omega.
    unfold load_handler, move; simpl.
    rewrite <- (app_assoc (hb_check _ _ _ _ _)); simpl; eauto.
  - inversion Ht; clear Ht; clarify.
    { exploit distinct_in; [eauto | apply Hin | apply split_in | clarify]. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (i & ?); clarify.
    exploit distinct_step; eauto; intro.
    repeat rewrite <- app_assoc in *.
    destruct n; clarify.
    destruct (le_gt_dec (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)) n).
    rewrite skipn_app, skipn_all in Heq; auto.
    rewrite <- Heq in Hexec'.
    exploit exec_t_segment; eauto; try apply (split_in P1).
    { rewrite in_app; right; simpl; left.
      erewrite (app_assoc _ (skipn _ _) li), firstn_skipn.
      rewrite <- (app_assoc _ _ li); eauto. }
    intros (? & ? & ? & ? & ? & ? & Hcheck1 & Hin1 & Hrest & ?); clarify.
    rewrite app_assoc, firstn_skipn in Hin1.
    exploit hb_check_exec; try apply Hcheck1; auto.
    { rewrite <- app_assoc in *; auto. }
    clarify.
    destruct (le_gt_dec (length (hb_check (R' + v) (C' + t) zt tmp1 tmp2))
      (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))).
    rewrite skipn_app, skipn_all in Heq; auto.
    destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2) -
      length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)) eqn: Hn'; clarify.
    destruct n1; clarify.
    destruct n1; clarify.
    destruct n1; clarify.
    repeat rewrite app_length in *; simpl in *; omega.
    + exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
      exploit hb_check_fail_exec; try apply Hrest; eauto.
      { rewrite skipn_app.
        rewrite (not_le_minus_0 _
          (length (hb_check (R' + v) (C' + t) zt tmp1 tmp2))); [|omega].
        rewrite <- app_assoc; simpl; apply split_in. }
      { rewrite Heq; eauto. }
      intros (vs1' & ? & ? & ? & ? & Hgt & ? & ? & ? & Hle & ?); subst.
      rewrite split_app, app_nil_r in Hcon.
      exploit hb_check_twice_n; try apply Hcon; auto; try omega.
      { rewrite plus_0_r; intros; eapply Hle; eauto. }
      { intros; eapply init_step; auto.
        constructor; simpl; auto. }
      intro; subst.
      erewrite <- (events_hb_check_extend (R + v) _ _ _ _
        (replicate 0 (zt - length vs1'))), firstn_skipn.
      erewrite <- (mops_hb_check_extend (R + v) _ _ _ _ _
        (replicate 0 (zt - length vs1'))), firstn_skipn.
      eapply fail_war; eauto.
      * unfold store_handler, move; simpl.
        do 2 rewrite <- (app_assoc (hb_check _ _ _ _ _)); simpl; eauto.
      * exploit first_gt_extend; eauto.
        rewrite firstn_skipn; eauto.
      * rewrite app_length, replicate_length, le_plus_minus_r; auto; omega.
      * intro; clarify.
      * intro; clarify.
    + rewrite <- Heq in Hexec'.
      exploit hb_check_fail_exec; eauto.
      { rewrite skipn_app, not_le_minus_0; [|omega].
        simpl; do 2 rewrite <- app_assoc; simpl; apply split_in. }
      { rewrite Heq; eauto. }
      clarify.
      eapply fail_waw; eauto; try omega.
      unfold store_handler, move; simpl.
      do 2 rewrite <- (app_assoc (hb_check _ _ _ _ _)); simpl; eauto.
  - destruct n; clarify.
    destruct (skipn n (lock_handler t m0 zt)) eqn: Hskip.
    { rewrite skipn_all_iff in *; omega. }
    clarify.
    exploit max_vc_instrs.
    { eapply skipn_in; setoid_rewrite Hskip; simpl; eauto. }
    clarify.
  - rewrite app_length in *; simpl in *.
    rewrite skipn_app in Heq;
      destruct (skipn n (unlock_handler t m0 zt tmp1)) eqn: Hskip; clarify.
    { destruct (n - length (unlock_handler t m0 zt tmp1)) eqn: Hminus; clarify;
        omega. }
    unfold unlock_handler in Hskip; rewrite skipn_app in Hskip.
    destruct (skipn n (set_vc (C' + t) (L' + m0) zt tmp1)) eqn: Hskip'.
    + destruct (n - length (set_vc (C' + t) (L' + m0) zt tmp1)); clarify.
      destruct n0; clarify.
      destruct n0; clarify.
      rewrite skipn_nil in Hskip; clarify.
    + exploit set_vc_instrs.
      { eapply skipn_in; setoid_rewrite Hskip'; simpl; eauto. }
      clarify.
  - rewrite app_length in *; simpl in *.
    rewrite skipn_app in Heq;
      destruct (skipn n (spawn_handler t t0 zt)) eqn: Hskip; clarify.
    { destruct (n - length (spawn_handler t t0 zt)) eqn: Hminus; clarify;
        omega. }
    unfold spawn_handler in Hskip; rewrite skipn_app in Hskip.
    destruct (skipn n (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)) eqn: Hskip'.
    + destruct (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)); clarify.
      destruct n0; clarify.
      destruct n0; clarify.
      rewrite skipn_nil in Hskip; clarify.
    + exploit max_vc_instrs.
      { eapply skipn_in; setoid_rewrite Hskip'; simpl; eauto. }
      clarify.
  - destruct n; clarify.
    destruct (skipn n (wait_handler t t0 zt)) eqn: Hskip; clarify.
    { rewrite skipn_all_iff in *; omega. }
    unfold wait_handler in Hskip; rewrite skipn_app in Hskip.
    destruct (skipn n (max_vc (C' + t0) (C' + t) zt tmp1 tmp2)) eqn: Hskip'.
    + destruct (n - length (max_vc (C' + t0) (C' + t) zt tmp1 tmp2)); clarify.
      destruct n0; clarify.
      destruct n0; clarify.
      rewrite skipn_nil in Hskip; clarify.
    + exploit max_vc_instrs.
      { eapply skipn_in; setoid_rewrite Hskip'; simpl; eauto. }
      clarify.
Qed.

Lemma first_fail : forall P P0 (Hsim0 : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P0' (Hsim : state_sim P' P0')
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P') (Hno : no_asserts P')
  G0 lo0 lc0 G0' (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P0') G0')
  t P3 (Hsuffix : state_suffix P' P3) 
  P2 G2 lo' lc' G3 (Hsteps2 : exec_star (Some P2) G2 lo' lc' (Some P3) G3)
  lo0' lc0' P1 G1
  (Hsteps0 : exec_star_t t (Some P0') G0' lo0' lc0' (Some P1) G1)
  lo lc  (Hsteps1 : exec_star_minus t (Some P1) G1 lo lc (Some P2) G2)
  o c G4
  (Hstep : exec P3 G3 t o c None G4)
  m (Hcon : consistent (m ++ lc0 ++ lc0' ++ lc ++ lc' ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1, fail_iexec P0' t lo1 lc1 /\ consistent (m ++ lc0 ++ lc1).
Proof.
  
  intros until G3; intro.
  remember (Some P2) as Pa; remember (Some P3) as Pb; generalize dependent P2;
    induction Hsteps2; clarify.
  - inversion Hstep; clarify.
    exists lo0', lc0'; split.
    + exploit distinct_steps; eauto; intro.
      exploit Forall2_in2; eauto; try apply split_in;
        intros ((?, ?) & ? & ? & ? & ? & Heq).
      destruct l; clarify.
      { rewrite skipn_nil in *; clarify. }
      exploit Forall2_in1; try apply Hsim; eauto; intros ((?, ?) & ?); clarify.
      assert (In (t, Assert_le e1 e2 :: rest) P4).
      { exploit exec_keep; try eapply exec_t_exec; eauto; clarify.
        exploit exec_other_threads; eauto; intro.
        exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
        exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
        exploit distinct_in; [eauto | eauto | apply split_in |].
        intro Heq'; rewrite Heq' in *; auto. }
      eapply exec_t_fail_iexec; eauto.
      * setoid_rewrite Forall_forall in Hno; exploit Hno; eauto; intro Hno'.
        inversion Hno'; destruct i; auto; clarify.
      * rewrite skipn_app, not_le_minus_0 in Heq; [|omega].
        rewrite Heq in *; auto.
      * exploit in_split; eauto; clarify.
        econstructor; eauto.
        erewrite exec_minus_env in Hfail; eauto.
      * rewrite app_assoc in Hcon; simpl in *; rewrite app_nil_r in *.
        eapply consistent_app_SC; rewrite <- app_assoc; eauto.
      * intros; eapply init_steps; eauto.
        apply HC_init; auto.
        exploit bounded_sim; try apply Ht; eauto; intro Hbound.
        eapply bounded_steps in Hbound; eauto.
        setoid_rewrite Forall_forall in Hbound; exploit Hbound; eauto; clarify.
        { eapply prog_steps; eauto. }
    + eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto.
  - exploit distinct_steps; eauto; intro.
    destruct P'0; [|inversion Hsteps2].
    specialize (IHHsteps2 _ eq_refl).
    destruct (eq_dec t0 t).
    + subst.
      exploit state_suffix_inv; try apply Hsim; auto.
      { eapply exec_star_trans; [eapply exec_t_exec | eapply exec_minus_exec];
          eauto. }
      { eapply exec_step; eauto. }
      { auto. }
      intro; exploit state_suffix_inv.
      { eauto. }
      { auto. }
      { eapply exec_t_exec; eauto. }
      { eapply exec_minus_exec; eauto. }
      { auto. }
      exploit distinct_steps; eauto 2.
      { eapply exec_t_exec; eauto. }
      intros; exploit state_suffix_stable; try eapply exec_minus_exec, Hsteps1;
        eauto.
      exploit noninterference; try apply Hroot; eauto 2.
      intro X; exploit X; eauto 2.
      { eapply consistent_app_SC.
        do 4 rewrite <- app_assoc; rewrite <- app_assoc in Hcon; eauto. }
      clarify; exploit exec_minus_reorder; try apply Hsteps1; eauto.
      { eapply consistent_app_SC.
        rewrite <- app_assoc in Hcon.
        do 4 rewrite app_assoc in Hcon.
        rewrite <- (app_assoc _ lc1) in Hcon; eauto. }
      clarify; eapply IHHsteps2.
      { eapply exec_step_inv_t; eauto. }
      { eauto. }
      { eauto. }
      { rewrite <- app_assoc, app_assoc, app_assoc in Hcon.
        rewrite loc_comm_ops_SC in Hcon.
        rewrite <- app_assoc, <- app_assoc, (app_assoc lc0') in Hcon; eauto.
        { eapply Forall_impl; eauto; clarify.
          destruct c; clarify. }
        { eapply prog_steps, exec_minus_exec; eauto. }
        { eapply prog_step; eauto. } }
      { auto. }
      { auto. }
      { auto. }
    + eapply IHHsteps2; eauto 2.
      { eapply exec_step_inv_m; eauto. }
      { rewrite <- app_assoc in *; auto. }
Qed.

Corollary first_fail' : forall P P0 (Hsim0 : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P0' (Hsim : state_sim P' P0')
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P') (Hno : no_asserts P')
  G0 lo0 lc0 G0' (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P0') G0')
  t P3 (Hsuffix : state_suffix P' P3) 
  lo' lc' G3 (Hsteps2 : exec_star (Some P0') G0' lo' lc' (Some P3) G3)
  o c G4 (Hstep : exec P3 G3 t o c None G4)
  m (Hcon : consistent (m ++ lc0 ++ lc' ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1, fail_iexec P0' t lo1 lc1 /\ consistent (m ++ lc0 ++ lc1).
Proof.
  
  intros; eapply first_fail with (lc0' := [])(lc := []); try apply Hstep;
    try apply Hroot; eauto; constructor.
Qed.

Lemma state_sim_steps : forall P1 P2 G2 lo lc P2' G2'
  (Hdistinct : distinct P2) (HPsim : state_sim P1 P2) (Hsafe : safe_locs P1)
  (Htmps : fresh_tmps P1) (Hiexec : iexec_star P2 G2 lo lc P2' G2'),
  exists P1', state_sim P1' P2' /\ safe_locs P1' /\ fresh_tmps P1'.
Proof.
  intros.
  generalize dependent P1; induction Hiexec; clarify; eauto.
  exploit distinct_steps; eauto.
  { eapply iexec_exec; eauto. }
  exploit state_sim_step'; eauto; clarify; eauto.
Qed.


Lemma state_sim_steps' : forall P1 P2 G2 lo lc P2' G2'
  (Hdistinct : distinct P2) (HPsim : state_sim P1 P2) (Hsafe : safe_locs P1)
  (Htmps : fresh_tmps P1) (Hiexec : iexec_star P2 G2 lo lc P2' G2') (Hlegal_tids: legal_tids P1),
  exists P1', state_sim P1' P2' /\ safe_locs P1' /\ fresh_tmps P1' /\ legal_tids P1'.
Proof.
  intros.
  generalize dependent P1; induction Hiexec; clarify; eauto.
  exploit distinct_steps; eauto.
  { eapply iexec_exec; eauto. }
  exploit state_sim_step_legal; eauto. clarify; eauto.
Qed.

Lemma iexec_execs : forall P G lo lc P' G', iexec_star P G lo lc P' G' ->
  exec_star (Some P) G lo lc (Some P') G'.
Proof.
  intros; induction H; clarify.
  - apply exec_refl.
  - exploit iexec_exec; eauto; intro.
    eapply exec_star_trans; eauto.
Qed.

Lemma state_sim_step'' : forall P1 P2 G2 t lo lc P2' G2'
  (Hdistinct : distinct P2) (HPsim : state_sim P1 P2) (Hsafe : safe_locs P1)
  (Htmps : fresh_tmps P1) (Hno : no_asserts P1)
  (Hiexec : iexec P2 G2 t lo lc P2' G2'),
  exists P1', state_sim P1' P2' /\ safe_locs P1' /\ fresh_tmps P1' /\
    no_asserts P1'.
Proof.
  intros.
  inversion Hiexec; subst; exploit state_sim_inv'; eauto 2;
    intros (P1a & [|??] & P1b & ? & ? & ? & ?); clarify;
    try (exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
         contradiction); exploit state_sim_inv; eauto; clarify.
  - exploit (instrument_incom (Assign a e)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
  - exploit (instrument_incom (Load a (x, o))).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
  - exploit (instrument_incom (Store (x, o) e)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
  - exploit (instrument_incom (Lock m)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
  - exploit (instrument_incom (Unlock m)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
  - exploit spawn_in_instrument.
    { instantiate (2 := (i :: l)); simpl.
      setoid_rewrite <- H2; rewrite in_app; clarify. }
    clarify.
    exploit (instrument_incom (Spawn u x)).
    { simpl; rewrite <- app_assoc; simpl; eauto. }
    clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    { apply (Forall2_cons (u, x)); eauto. }
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
    rewrite safe_instrs in *.
    repeat split; auto; repeat constructor; auto.
    + apply Forall_and; split; rewrite <- list_fresh_iff; auto.
    + rewrite instr_forall_list in *; auto.
  - exploit (instrument_incom (Wait u)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
  - exploit (instrument_incom (Assert_le e1 e2)); simpl; eauto; clarify.
    eexists; split;
      [apply Forall2_app; try (apply (Forall2_cons (t, l))); eauto|].
    unfold safe_locs, fresh_tmps, no_asserts, state_forall in *;
      repeat rewrite Forall_app in *; clarify.
    inversion Hsafe2 as [|?? Hsafei]; inversion Htmps2 as [|?? Hfreshi];
      inversion Hno2 as [|?? Hnoi]; inversion Hsafei; inversion Hfreshi;
      inversion Hnoi; clarify.
Qed.

Lemma exec_iexec1' : forall P P' G' G lo lc
  (Hexec : exec_star (Some P) G lo lc (Some P') G')
  P1 (HP : state_sim P1 P) (Hsafe : safe_locs P1) (Hfresh : fresh_tmps P1)
  (Hno : no_asserts P1)
  P0 (Hdistinct0 : distinct P0) P0' (Hsim0 : state_sim P0' P0)
  (Hsafe0 : safe_locs P0') (Hfresh0 : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0)
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  G0 lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P) G)
  m (Hcon : consistent (m ++ lc0 ++ lc))
  (Hinit_l : forall l, l < zl -> initialized m (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m (X' + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo'1 lc'1 G2' P2' lo'2 lc'2, safe_locs P2' /\ fresh_tmps P2' /\
    no_asserts P2' /\ state_suffix P2' P' /\
    iexec_star P G lo'1 lc'1 (instrument_prog P2') G2' /\
    exec_star (Some (instrument_prog P2')) G2' lo'2 lc'2 (Some P') G' /\
    mem_ext (m ++ lc0 ++ lc'1 ++ lc'2) (m ++ lc0 ++ lc).
Proof.
  intros ???.
  remember (size P) as z; generalize dependent P;
    induction z using lt_wf_ind; clarify.
  exploit distinct_steps; eauto; intro Hdistinct.
  exploit sim_next_iexec; try apply Hroot; eauto.
  intros [? | (t & lo1 & lc1 & Pt & Gt & lo2 & lc2 & Hiexec & Hrest & Hcon')].
  { rewrite instrumented_iff in HP; subst.
    do 6 eexists; split; [|split; [|split; [|split; [|split;
      [apply iexec_refl|]]]]]; auto.
    split; [eauto | reflexivity]. }
  clarify; exploit iexec_decr; eauto; intro Hlt.
  specialize (H _ Hlt _ eq_refl _ _ _ Hrest).
  exploit state_sim_step''; eauto; intros (? & Hsim' & ?).
  specialize (H _ Hsim'); clarify.
  specialize (H _ Hdistinct0 _ Hsim0); clarify.
  exploit H; auto.
  - eapply exec_star_trans; eauto.
    eapply iexec_exec; eauto.
  - destruct Hcon' as (Hcon' & ?).
    specialize (Hcon' []); repeat rewrite app_nil_r in Hcon'.
    rewrite <- app_assoc, Hcon'; auto.
  - clarify; do 7 eexists; eauto; repeat (split; [solve [eauto]|]).
    split; [|split; eauto 2].
    + eapply iexec_step; eauto.
    + repeat rewrite <- app_assoc in *.
      etransitivity; eauto.
Qed.


Definition mem_vals m1 m2 := forall x (Hmeta : ~meta_loc x)
  (Hinit1 : initialized m1 x) v,
  can_read m1 x v <-> can_read m2 x v.

(* up *)
Lemma rev_filter : forall A (l : list A) f, rev (filter f l) = filter f (rev l).
Proof.
  induction l; clarify.
  rewrite filter_app; simpl.
  destruct (f a); clarify; rewrite IHl; clarsimp.
Qed.

Lemma mem_vals_sim : forall m1 m2 m1' (Hcon1 : consistent m1)
  (Hcon2 : consistent m2) (Hsim : mem_sim' m1 m2),
  mem_vals m1 m1' <-> mem_vals m2 m1'.
Proof.
  intros.
  assert (forall x, ~meta_loc x ->
    find (fun c => writesb c x) (rev (filter (fun c =>
      if meta_loc_dec (loc_of c) then false else true) m2)) =
      find (fun c => writesb c x) (rev m2)) as Heq.
  { intros; rewrite rev_filter; apply find_filter.
    unfold implb; intro c; clarify.
    destruct c; clarify; unfold beq in *; clarify. }
  assert (forall x, ~meta_loc x -> (initialized m1 x <-> initialized m2 x))
    as Hinit.
  { unfold mem_sim' in *; clarify.
    unfold initialized; split; intros (v & ?); exists v;
      rewrite last_write in *; clarify; rewrite Heq in *; eauto. }
  assert (forall x v, ~meta_loc x -> initialized m1 x ->
    (can_read m1 x v <-> can_read m2 x v)) as Hval.
  { unfold mem_sim' in *; clarify.
    rewrite init_read; auto.
    rewrite Heq; auto; symmetry; apply init_read; auto.
    rewrite Hinit in *; auto. }
  split; repeat intro.
  - rewrite <- Hinit in *; auto.
    rewrite <- Hval; auto.
  - rewrite Hval; auto.
    rewrite Hinit in *; auto.
Qed.      
  
Lemma mem_vals_ext : forall m m' m1 (Hext : mem_ext m m'),
  mem_vals m m1 <-> mem_vals m' m1.
Proof.
  intros ??? (Hext & Hinit); unfold mem_vals.
  setoid_rewrite Hinit; setoid_rewrite Hext; reflexivity.
Qed.


Instance mem_vals_refl: RelationClasses.Reflexive mem_vals.
Proof.
  intros ?????.
  split; clarify.
Qed.

Lemma mem_vals_cond_trans: forall m1 m2 m3
   (Hinit: forall x, initialized m1 x <-> initialized m2 x)
   (Hmem_vals12: mem_vals m1 m2) (Hmem_vals23: mem_vals m2 m3),
                             mem_vals m1 m3.
Proof.
  intros. unfold mem_vals in *.
  intros.
  rewrite Hmem_vals12; auto. rewrite Hmem_vals23; auto.
  reflexivity.
  rewrite <- Hinit. auto.
Qed.

Lemma mem_vals_cond_symm: forall m1 m2
  (Hinit: forall x, initialized m1 x <-> initialized m2 x)                              
  (Hmem_vals12: mem_vals m1 m2),
                            mem_vals m2 m1.
Proof.
  unfold mem_vals. clarify.
  rewrite <- Hmem_vals12; clarify.
  -reflexivity.
  -rewrite Hinit. auto.
Qed.
Lemma can_read_iff_SC: forall p ops m v
  (Hcon : consistent (m ++ ops)) (Hprog : Forall prog_op ops)
  (Hno_write : Forall (fun c => match c with Write _ x _ | ARW _ x _ _ => p <> x
     | _ => True end) ops),
  can_read (m ++ ops) p v <-> can_read m p v.
Proof.
  induction ops; clarify.
  { rewrite app_nil_r; reflexivity. }
  specialize (IHops (m ++ [a]) v); rewrite <- app_assoc in *;
    inversion Hprog; inversion Hno_write; clarify.
  rewrite IHops.
  destruct (eq_dec (loc_of a) p).
  - destruct a; clarify.
    unfold can_read; rewrite <- app_assoc.
    simpl; rewrite read_noop_SC; [reflexivity|].
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
  - unfold can_read; rewrite <- app_assoc.
    simpl; rewrite loc_valid_ops2_SC; auto.
    + split; clarify.
      eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
    + constructor; clarify.
Qed.

Lemma writesb_write : forall c p v (Hwrite : writesb c p = true)
  (Hval : write_val c = Some v),
  exists i, nth_error (to_seq c) i = Some (MWrite p v).
Proof.
  destruct c; clarify.
  - unfold beq in Hwrite; exists 0; clarify.
  - unfold beq in Hwrite; exists 1; clarify.
Qed.

Lemma writesb_val : forall c p (Hwrite : writesb c p = true)
  (Hprog : prog_op c), exists v, write_val c = Some v.
Proof.
  destruct c; clarify; eauto.
Qed.

Notation lower := (@lower _ _ _ _ _ Base).

Typeclasses eauto := 4.

Lemma lift_last : forall ops p a
  (Hlast : last_op (lower ops) (Ptr p) a) (Hprog : Forall prog_op ops),
  exists i w, nth_error ops i = Some w /\ last_op (to_seq w) (Ptr p) a /\
    forall i2 w2, nth_error ops i2 = Some w2 -> writesb w2 p = true -> i2 <= i.
Proof.
  intros.
  assert (exists i, last_mod_op (lower ops) (Ptr p) i /\
    inth (lower ops) i = Some a) as (i & Hlast_mod & Hnth) by eauto.
  inversion Hlast_mod; setoid_rewrite Hop1 in Hnth; clarify.
  rewrite inth_nth_error in Hop1; generalize (nth_lower_split _ _ Hop1); 
    intros (ops1 & c & ops2 & i' & ? & Hi' & ?); clarify.
  exists (length ops1); rewrite nth_error_split; do 2 eexists; eauto.
  rewrite lower_app, lower_cons in Hlast.
  repeat setoid_rewrite last_op_app in Hlast.
  destruct Hlast as [[Hlast | Hlast] | Hlast].
  - destruct Hlast as (i2 & Hi2).
    specialize (Hlast0 (length (lower ops1) + (length (to_seq c) + i2))).
    rewrite inth_nth_error, lower_app, lower_cons in Hlast0.
    repeat rewrite nth_error_plus in Hlast0; specialize (Hlast0 a); clarsimp.
    generalize (nth_error_lt _ _ Hi'); intro; exfalso.
    apply plus_le_reg_l in Hlast0.
    assert (length (to_seq c) <= i') by omega.
    rewrite Nat.le_ngt in *; contradiction.
  - split; [clarify | intros i2 w2 Hw2 Hmods2].
    rewrite nth_error_app in *; destruct (lt_dec i2 (length ops1)); [omega|].
    destruct (i2 - length ops1) eqn: Hminus; [omega | clarify].
    rewrite Forall_app in Hprog; destruct Hprog as [_ Hprog];
      inversion Hprog as [|??? Hprog2]; subst.
    exploit nth_error_split'; eauto; clarify.
    rewrite Forall_app in Hprog2; clarify; inversion Hprog22; subst.
    exploit writesb_val; eauto; intros (v & ?).
    exploit writesb_write; eauto; intros (i2' & ?).
    specialize (Hlast0 (length (lower ops1) + (length (to_seq c) +
      (length (lower x) + i2')))).
    rewrite inth_nth_error in Hlast0; repeat rewrite lower_app in Hlast0.
    rewrite nth_error_plus, lower_cons, nth_error_plus in Hlast0.
    setoid_rewrite lower_app in Hlast0; rewrite nth_error_plus in Hlast0.
    setoid_rewrite lower_cons in Hlast0; rewrite nth_error_app in Hlast0.
    exploit nth_error_lt; eauto; clarify.
    specialize (Hlast0 (MWrite p v)); clarify.
    rewrite <- NPeano.Nat.add_le_mono_l in Hlast0.
    assert (i' < length (to_seq c) + (length (lower x) + i2')) as Hlt.
    { generalize (nth_error_lt _ _ Hi'); intro.
      eapply lt_le_trans; [eauto | apply le_plus_l]. }
    omega.
  - rewrite Forall_app in *; clarify.
    generalize (nth_error_in _ _ Hi'); intro.
    rewrite Forall_forall in Hlast21; specialize (Hlast21 a); clarify.
Qed.
(* /up *)

Lemma can_read_write_SC: forall p ops m v
  (Hcon : consistent (m ++ ops)) (Hprog : Forall prog_op ops) c v'
  (Hin : In c ops) (Hp : writesb c p = true) (Hv : write_val c = Some v')
  (Hwrite : Forall (fun c => writesb c p = true -> write_val c = Some v') ops),
  can_read (m ++ ops) p v <-> v = v'.
Proof.
  intros.
  unfold can_read, consistent, SC; rewrite lower_app, lower_single; simpl.
  rewrite read_last; auto; try reflexivity.
  assert (exists a, last_op (lower (m ++ ops)) (Ptr p) a) as (a & Hlast).
  { exploit in_split; eauto; intros (ops1 & ops2 & ?); subst.
    exploit writesb_write; eauto; intros (i & Hi).
    generalize (has_last_op(op := MWrite p v') _ (length (lower m) +
      (length (lower ops1) + i)) Hcon); intro X; use X.
    destruct X as (i' & Hlast); inversion Hlast.
    exists op, i'; auto.
    { rewrite lower_app, nth_error_plus, lower_app, nth_error_plus.
      rewrite lower_cons, nth_error_app; exploit nth_error_lt; eauto; clarify. }
  }
  rewrite lower_app, last_op_app in Hlast; destruct Hlast as [Hlast | Hlast].
  - rewrite lower_app, last_op_app; left.
    exploit lift_last; eauto; intros (? & w & ? & Hlast' & ?); clarify.
    exploit nth_error_in; eauto; intro.
    rewrite Forall_forall in *; exploit Hprog; eauto; intro.
    destruct w; clarify; try rewrite last_single in Hlast'; clarify.
    + destruct (eq_dec x0 p); clarify.
      exploit Hwrite; eauto; simpl; unfold beq; clarify.
    + destruct Hlast' as (i & Hlast' & ?); destruct i; inversion Hlast';
        clarsimp.
      destruct i; clarify; [|rewrite inth_nil in *; clarify].
      destruct (eq_dec x0 p); clarify.
      exploit Hwrite; eauto; simpl; unfold beq; clarify.
  - clarify.
    rewrite Forall_forall in Hlast2; exploit Hlast2.
    { exploit writesb_write; eauto; clarify.
      eapply flatten_in; setoid_rewrite in_map_iff; do 2 eexists; eauto.
      eapply nth_error_in; eauto. }
    clarify.
Qed.

Lemma writesb_loc : forall w p (Hwrite : writesb w p = true)
  (Hprog : prog_op w), loc_of w = p.
Proof.
  destruct w; clarify; unfold beq in *; clarify.
Qed.

Lemma init_snoc : forall m c p (Hinit : initialized (m ++ [c]) p),
  writesb c p = true \/ initialized m p.
Proof.
  unfold initialized in *; clarify.
  rewrite lower_app, last_op_app in Hinit; destruct Hinit; [|clarify; eauto].
  destruct H as (i & Hlast & ?); inversion Hlast; clarsimp.
  rewrite lower_single in H; destruct c; simpl in *;
    try rewrite nth_error_single in *; unfold beq; clarify.
  destruct i; clarify; rewrite nth_error_single in *; clarify.
Qed.

Lemma mem_vals_sim_app : forall m1 m2 c1 c2
  (Hmem_vals: mem_vals m1 m2) (Hsim: mem_sim c1 c2) (Hprog: Forall prog_op (opt_to_list c1)),                              
                           mem_vals (m1++(opt_to_list c1)) (m2++c2).
Proof.
  intros.
  unfold mem_sim, mem_vals in *. clarify.
  destruct c1; clarify.
  - destruct (eq_dec (loc_of c) x).
    + inversion Hprog; destruct c; clarify.
      * rewrite can_read_iff_SC; auto.
        rewrite can_read_iff_SC; auto.
        apply Hmem_vals; auto.
        { exploit init_snoc; eauto; clarify. }
        { rewrite Forall_forall; intros c' ?.
          specialize (Hsim c'); destruct Hsim; clarify.
          destruct (meta_loc_dec (loc_of c')); clarify.
          destruct c'; clarify; intro; clarify. }
      * rewrite can_read_write_SC; simpl; eauto; simpl; unfold beq; clarify.
        generalize (Hsim (Write t x v0)); intros [? _]; clarify.
        symmetry; eapply can_read_write_SC; eauto; simpl; unfold beq; clarify.
        rewrite Forall_forall in *; intros a ?.
        exploit Hprog2; eauto; intro.
        intro; exploit writesb_loc; eauto.
        specialize (Hsim a); destruct Hsim as [_ ?]; clarify.
        rewrite <- H4; auto.
      * rewrite can_read_write_SC; simpl; eauto; simpl; unfold beq; clarify.
        generalize (Hsim (ARW t x v0 v')); intros [? _]; clarify.
        symmetry; eapply can_read_write_SC; eauto; simpl; unfold beq; clarify.
        rewrite Forall_forall in *; intros a ?.
        exploit Hprog2; eauto; intro.
        intro; exploit writesb_loc; eauto.
        specialize (Hsim a); destruct Hsim as [_ ?]; clarify.
        rewrite <- H4; auto.
    + inversion Hprog; subst.
      destruct (writesb c x) eqn: Hwrite.
      { exploit writesb_loc; eauto; clarify. }
      rewrite can_read_iff_SC; auto.
      rewrite can_read_iff_SC; auto.
      apply Hmem_vals; auto.
      { exploit init_snoc; eauto; clarify. }
      { rewrite Forall_forall in *; intros a ?.
        destruct (meta_loc_dec (loc_of a)).
        { destruct a; auto; intro; clarify. }
        specialize (Hsim a); destruct Hsim as [_ ?]; clarify.
        destruct a; clarify. }
      { constructor; auto.
        specialize (Hsim c); destruct Hsim as [? _]; clarify.
        destruct c; clarify. }
  - rewrite app_nil_r in *.
    rewrite can_read_iff_SC; auto.
    rewrite Forall_forall in *; intros a ?.
    specialize (Hsim a); destruct Hsim; clarify.
    destruct a; auto; intro; clarify.
Qed.

Lemma mem_vals_app_meta : forall m1 m2 (Hvals : mem_vals m1 m2)
  (Hinit : forall x, ~meta_loc x -> initialized m1 x)
  lc (Hmeta : Forall (fun a => meta_loc (loc_of a)) lc)
  (Hprog : Forall prog_op lc) (Hcon : consistent (m1 ++ lc)),
  mem_vals (m1 ++ lc) m2.
Proof.
  unfold mem_vals; intros.
  rewrite <- Hvals; auto.
  unfold can_read; rewrite <- app_assoc.
  rewrite loc_valid_ops1_SC; clarify.
  split; clarify.
  { eapply Forall_impl; try apply Hmeta; repeat intro; clarify. }
Qed.  
(*
Lemma part_complete : forall P0 P (Hsim : state_sim P0 P)
  (Ht : Forall (fun e => fst e < zt) P0)
  (Hsafe : safe_locs P0) (Hfresh : fresh_tmps P0) (Hdistinct : distinct P)
  G lo lc P' G' (Hexec : exec_star (Some P) G lo lc (Some P') G')
  (Hsuffix : state_suffix P0 P') m (Hcon : consistent (m ++ lc))
  (Hinit : forall p, ~meta_loc p -> initialized m p),
  exists lo1 lc1 P1 G1 P1' lo2 lc2 P2, iexec_star P G lo1 lc1 P1 G1 /\
    mem_vals (m ++ lc) (m ++ lc1) /\ env_sim G' G1 /\
    state_sim P1' P1 /\ safe_locs P1' /\ fresh_tmps P1' /\
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G' /\ state_suffix P1' P2 /\
    consistent (m ++ lc1 ++ lc2) /\
    forall t li (Hin : In (t, li) P'), In (t, li) P2 /\
      (forall li0, In (t, li0) P1' <-> In (t, li0) P0) \/
    match li with [] => False | i :: li => In (t, li) P2 /\
      exists l, i = Unlock l /\ meta_loc (l, 0) end \/
    exists n l, n < length (instrument_instr (Lock l) t) /\
      exists li', li = skipn n (instrument_instr (Lock l) t) ++ li' /\
      In (t, li') P2.
Proof.
  intros; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; rewrite exec_rev in Hexec; induction Hexec;
    clarify.
  { do 9 eexists; [apply iexec_refl|].
    split; [reflexivity|].
    split; [apply env_sim_refl|].
    split; eauto; clarify.
    split; [apply exec_refl|].
    split; [apply sim_suffix; auto | clarify].
    left; clarify; reflexivity. }
  rewrite <- exec_rev in Hexec.
  rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto; clarify.
  specialize (IHHexec _ eq_refl).
  exploit state_suffix_inv; eauto.
  { eapply exec_step, exec_refl; eauto. }
  intro Hsuffix0; use IHHexec.
  destruct IHHexec as (? & ? & ? & ? & ? & ? & ? & P2 & Hiexec & Hmem & Henv &
    ? & ? & ? & ? & Hsuffix' & ? & HP2); clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & ?); clarify.
  exploit HP2; [apply split_in|]; intros [[? Hiff] | [? | ?]].
  - destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    assert (P1 P2) by admit.
    exploit in_split; eauto; clarify.
    exploit result_exec; eauto; setoid_rewrite Hi; intro X.
    exploit X; clear X; eauto; intro Hexec2.
    destruct (find (fun c => if meta_loc_dec (loc_of c) then false else true)
      (opt_to_list c)) eqn: Hfind.
    + destruct c; clarify.
      exploit distinct_steps.
      { eauto. }
      { eapply exec_star_trans; [eapply iexec_execs; eauto | eauto]. }
      intro Hdistinct1; exploit state_suffix_inv'; eauto.
      intros (? & li & ? & n0 & ?); clarify.
      destruct li; [rewrite skipn_nil in *; clarify | simpl in *].
      rewrite skipn_app, le_minus_0 in *; [|omega].
      destruct (skipn n0 (instrument_instr i0 t)) eqn: Hskip.
      { rewrite skipn_all_iff in Hskip; omega. }
      clarify.
      destruct (eq_dec n0 (length (instrument_instr i0 t) - 1)).
      { exploit distinct_steps; try apply Hexec; auto; intro.
        assert (l = []).
        { assert (length (skipn n0 (instrument_instr i0 t)) = length (i1 :: l))
            as Hlen by (rewrite Hskip; auto).
          clarify; rewrite skipn_length in Hlen.
          destruct l; auto; simpl in Hlen; omega. }
        subst; exploit state_suffix_inv'; try apply Hsuffix0; auto.
        intros (? & li0 & ?); clarify.
        assert (li0 = i0 :: li).
        { specialize (Hiff li0); destruct Hiff as [_ Hiff].
          rewrite in_app in Hiff; clarify.
          rewrite <- distinct_suffix in Hdistinct1; eauto.
          eapply distinct_in; eauto; apply split_in. }
        subst; exploit state_suffix_inv'; try apply Hsuffix.
        { eapply distinct_step; eauto. }
        intros (? & ? & ? & n' & Heq & ? & ? & Hskip' & ?); clarify.
        exploit distinct_thread; try apply Heq; auto.
        { rewrite (distinct_suffix Hsuffix0); auto. }
        clarify.
        rewrite skipn_app, le_minus_0 in Hskip'; [|omega].
        destruct (skipn n' (instrument_instr i0 t)) eqn: H';
          [rewrite skipn_all_iff in H'; omega|].
        simpl in *; exploit cons_app_neq; eauto; contradiction. }
      assert (t < zt).
      { rewrite Forall_forall in Ht; exploit Ht.
        { rewrite <- Hiff; apply split_in. }
        auto. }
      destruct i0; simpl in *; try omega.
      * admit.
      * admit.
      * admit.
      * admit.
      * exfalso; assert (In i1 (i1 :: l)) as Hin by (simpl; auto).
        rewrite <- Hskip in Hin; exploit skipn_in; eauto.
        assert (t0 < zt).
        { exploit bounded_sim; try apply Hsim; auto; intro Hbound.
          eapply bounded_steps in Hbound; eauto.
          setoid_rewrite Forall_forall in Hbound; exploit Hbound.
          { apply split_in. }
          simpl; rewrite <- list_cons_plus_assoc, <- Hskip, skipn_app,
            le_minus_0; [|rewrite app_length in *; simpl in *; omega].
          repeat rewrite Forall_app; intros (_ & ((_ & Ht0) & _));
            inversion Ht0; clarify.
          unfold bounded_instr in *; clarify. }
        unfold spawn_handler; repeat rewrite in_app; intros [[? | Hin'] | ?];
          clarify.
        { exploit max_vc_instrs; eauto; intros [[? [? [? | [? | ?]]]] | ?];
            clarify; apply n, C_meta; auto. }
        { destruct Hin' as [? | [? | ?]]; clarify; apply n, C_meta; auto. }
      * exfalso; assert (In i1 (i1 :: l)) as Hin by (simpl; auto).
        rewrite <- Hskip in Hin; exploit skipn_in; eauto.
        destruct n0; clarify.
        assert (t0 < zt).
        { specialize (Hiff (Wait t0 :: li)); destruct Hiff as [Hiff _].
          use Hiff; [|apply split_in].
          exploit Forall2_in1; try apply Hsim; eauto; intros ((?, ?) & Hin0 &
            ?); clarify.
          exploit step_instr; try apply Hin0; eauto.
          { rewrite <- list_cons_plus_assoc, <- Hskip.
            rewrite skipn_app, le_minus_0; [apply split_in | omega]. }
          clarify.
          exploit exec_other_threads; eauto; intro.
          exploit distinct_steps; [|eapply exec_minus_exec; eauto|]; auto.
          exploit in_split; eauto; clarify.
          exploit exec_next; eauto; clarify.
          exploit bounded_sim; try apply Hsim; auto; intro Hbound.
          eapply bounded_steps in Hbound; [|eapply exec_minus_exec; eauto].
          setoid_rewrite Forall_forall in Hbound; exploit Hbound; eauto.
          clarify. }
        setoid_rewrite in_app in H8; destruct H8 as [? | Hin']; clarify.
        { exploit max_vc_instrs; eauto; intros [[? [? [? | [? | ?]]]] | ?];
            clarify; apply n, C_meta; auto. }
        { destruct Hin' as [? | [? | ?]]; clarify; apply n, C_meta; auto. }
    + exploit exec_step_inv; eauto; intro Hsteps2.
      do 9 eexists; eauto.
      split.
      { rewrite app_assoc; apply mem_vals_app_meta; auto.
        * intros; eapply init_steps, prog_steps; eauto.
        * destruct c; clarify.
        * eapply prog_step; eauto. }
      repeat (split; eauto).
      * admit.
      * admit.
      * admit.
      * intros.
        exploit distinct_steps; eauto; intro.
        exploit in_step_rev; try apply Hin; eauto; intros [? | [? | ?]].
        { destruct (eq_dec t0 t).
          { subst; exploit distinct_in;
              [eauto | apply split_in | eauto | clarify].
            exploit distinct_step; eauto; intro.
            exploit distinct_in;
              [eauto | apply split_in | eauto | clarify].
            exploit cons_neq; eauto; contradiction. }
          exploit HP2; eauto; intros [Hin' | Hin'].
          * left; rewrite in_app; simpl.
            rewrite in_app; rewrite in_app in Hin'; clarify.
          * right; destruct li; clarify.
            split; eauto.
            rewrite in_app; simpl.
            rewrite in_app; rewrite in_app in Hin'1; clarify. }
        { clarify.
          exploit distinct_step; eauto; intro.
          exploit distinct_in; [eauto | apply split_in | eauto | clarify].
          rewrite in_app; simpl; auto. }
        { clarify.
          exploit distinct_in; [eauto | apply split_in | eauto | clarify].
          rewrite in_app; simpl; auto. }
  - clarify.
    do 9 eexists; eauto.
    split.
    { rewrite app_assoc; apply mem_vals_app_meta; auto.
      * intros; eapply init_steps, prog_steps; eauto.
      * constructor; simpl; auto. }
    split; auto.
    repeat (split; eauto).
    intros.
    destruct (eq_dec t0 t).
    + exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      subst; exploit distinct_in; [eauto | apply split_in | eauto | clarify].
    + apply HP2; rewrite in_app in *; clarify.
Qed.

Lemma fail_safe : forall Pa P (Hsim : state_sim Pa P) (Hsafe : safe_locs Pa)
  (Hfresh : fresh_tmps Pa) (Hno : no_asserts Pa)
  G lo lc P' G' (Hexec : exec_star (Some P) G lo lc (Some P') G')
  (Hsuffix : state_suffix Pa P') t o c G'' (Hfail : exec P' G' t o c None G'')
  P0 (Hdistinct0 : distinct P0) P0' (Hsim0 : state_sim P0' P0)
  (Hsafe0 : safe_locs P0') (Hfresh0 : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0)
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  G0 lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P) G)
  m (Hcon : consistent (m ++ lc0 ++ lc ++ opt_to_list c))
  (Hinit_l : forall l, l < zl -> initialized m (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m (X' + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1 P1 G1 lo2 lc2, iexec_star P G lo1 lc1 P1 G1 /\
    mem_vals (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1) /\ env_sim G' G1 /\
    fail_iexec P1 t lo2 lc2 /\ consistent (m ++ lc0 ++ lc1 ++ lc2).
Proof.
  intros.
  inversion Hfail; subst; rewrite app_nil_r in *.
  exploit part_complete; try apply Hsim; eauto.
  { rewrite app_assoc in Hcon; eauto. }
  intros (? & ? & ? & ? & ? & ? & ? & P4 & Hiexec & ? & ? & ? & ? & ? & Hrest &
    ? & ? & HP4).
  repeat rewrite <- app_assoc in *.
  assert (exec P4 G'' t None None None G'').
  { exploit HP4.
    { apply split_in. }
    clarify.
    exploit in_split; eauto; clarify.
    eapply exec_assert_fail; eauto. }
  exploit exec_star_trans; try apply Hroot.
  { eapply iexec_execs; eauto. }
  intro Hroot'.
  exploit first_fail'; try apply Hroot'; eauto.
  { admit. }
  intro X; exploit X; clear X; eauto.
  { rewrite app_nil_r, <- app_assoc; auto. }
  clarify; do 7 eexists; eauto.
  do 2 (split; auto).
  split; eauto.
  rewrite <- app_assoc in *; auto.
Qed.*)

Lemma iexec_trans : forall P G lo lc P' G' lo' lc' P'' G''
  (Hiexec1 : iexec_star P G lo lc P' G')
  (Hiexec2 : iexec_star P' G' lo' lc' P'' G''),
  iexec_star P G (lo ++ lo') (lc ++ lc') P'' G''.
Proof.
  intros ???????????; induction Hiexec1; clarify.
  repeat rewrite <- app_assoc; eapply iexec_step; eauto.
Qed.
  
Lemma exec_fail_iexec : forall P P' G'' G' G lo lc o c t
  (Hexec : exec_star (Some P) G lo lc (Some P') G')
  (Hfail : exec P' G' t o c None G'')
  P1 (HP : state_sim P1 P) (Hsafe : safe_locs P1) (Hfresh : fresh_tmps P1)
  (Hno_asserts : no_asserts P1)
  P0 (Hdistinct0 : distinct P0) P0' (Hsim0 : state_sim P0' P0)
  (Hsafe0 : safe_locs P0') (Hfresh0 : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0)
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  G0 lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P) G)
  m0 (Hcon : consistent (m0 ++ lc0 ++ lc ++ opt_to_list c))
  (Hinit : forall p, initialized m0 p),
  exists lo1' lc1' P1' G1' lo2' lc2', iexec_star P G lo1' lc1' P1' G1' /\
    fail_iexec P1' t lo2' lc2' /\ consistent (m0 ++ lc0 ++ lc1' ++ lc2').
Proof.
  intros.
  exploit exec_iexec1'; try apply Hexec; try apply Hroot; eauto.
  { eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto. }
  intros (? & lc'1 & ? & P2 & ? & lc'2 & ? & ? & ? & ? & Hiexec & Hrest & Hext);
  clarify.
  exploit first_fail'; try apply Hfail.
  { eauto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
  { apply instrumented. }
  { eauto. }
  { auto. }
  { auto. }
  { eapply exec_star_trans; eauto.
    apply iexec_execs; eauto. }
  { auto. }
  { eauto. }
  intro X; exploit X; clear X; eauto.
  { inversion Hfail; subst; rewrite app_nil_r in *.
    destruct Hext as (Hext & _).
    specialize (Hext []); repeat rewrite app_nil_r in *.
    rewrite <- Hext in *; repeat rewrite app_assoc in *; eauto. }
  clarify; repeat rewrite <- app_assoc in *.
  do 7 eexists; eauto.
Qed.

  
Lemma length_hb_check : forall C1 C2 z t1 t2,
  length (hb_check C1 C2 z t1 t2) = z+z+z.
Proof.
  induction z; intros.
  -clarify.
  -simpl. specialize(IHz t1 t2). rewrite IHz. omega.
Qed.

Lemma Forall2_cons_inv (X:Type) l1 l2 (x1 x2: X) P:
  Forall2 P (x1 :: l1) (x2 :: l2)-> P x1 x2 /\ Forall2 P l1 l2.
Proof.
  intros. inversion H. clarify. Qed.

Lemma first_gt_vc : forall (V1 V2: tid->nat) l
  (Hgt: first_gt (map V1 l) (map V2 l) = None) i (Hi : In i l), V1 i <= V2 i.
Proof.
  induction l; clarify.
  rewrite leb_le in *; clarify.
Qed.

Lemma first_gt_vc_le : forall (V1 V2: tid->nat) m x1 x2
  (Hgt: first_gt (map V1 (rev (interval 0 zt))) (map V2 (rev (interval 0 zt))) =
     None)
  (Hmatch1 : clock_match m V1 x1) (Hmatch2 : clock_match m V2 x2),
  vc_le V1 V2.
Proof.
  repeat intro.
  specialize (Hmatch1 t); specialize (Hmatch2 t).
  destruct (lt_dec t zt); clarsimp.
  eapply first_gt_vc; eauto.
  rewrite <- in_rev, interval_in_iff; auto.
Qed.

Lemma mops_max_vc_off' : forall src tgt vs1 vs2 t n
  (Hvs1: length vs1 = n) (Hvs2: length vs2 = n),
  Forall (fun c' => match loc_of c' with (x, o) => o < n end)
     (mops_max_vc src tgt vs1 vs2 t n).
Proof.
  intros. generalize dependent vs1. generalize dependent vs2.
  induction n; clarify.
  -apply empty_list in Hvs1. apply empty_list in Hvs2. clarify.
  -apply nonempty_list in Hvs1. apply nonempty_list in Hvs2.
   inversion Hvs1. inversion H. inversion Hvs2. inversion H1.
   inversion H0. inversion H2. rewrite H3, H5.
   rewrite mops_max_vc_step. rewrite Forall_app. split.
   +unfold mops_max. rewrite Forall_forall. intros c Hin.
    inversion Hin; clarify. destruct Hin as [Hc|[Hc|[Hc|Hc]]]; clarify.
   +assert( forall c ,
              (fun c' : conc_op => let (_, o) := loc_of c' in o < n) c ->
              (fun c' : conc_op => let (_, o) := loc_of c' in o < S n) c) as Himpl.
      intros. destruct (loc_of c); clarify.
    eapply Forall_impl; eauto.
Qed.

Lemma max_vc_vals1: forall m C1 C2 z vs1 vs2 t V1 V2
  (Hinit1: forall z, z < zt -> initialized m (C1, z))
  (Hinit2: forall z, z < zt -> initialized m (C2, z))
  (Hcon: consistent (m ++mops_max_vc C1 C2 vs1 vs2  t z))
  (Hvs1: length vs1 =z) (Hvs2: length vs2 = z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2),
  vs1 = map V1 (rev (interval 0 z)) /\ vs2 = map V2 (rev (interval 0 z)).
Proof.
  induction z; destruct vs1, vs2; clarify.
  rewrite rev_app_distr; clarify.
  assert ( consistent (m++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert ( consistent (m++ [Read t (C2, z) n0])) as Hn0.
  { rewrite read_noop_SC in Hcon; auto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert ( consistent (m++ [Write t (C2, z) (Peano.max n n0)])) as Hwn0.
  { do 2 (rewrite read_noop_SC in Hcon; auto).
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  exploit (IHz vs1 vs2); eauto.
  {do 2 (rewrite read_noop_SC in Hcon; eauto).
   rewrite loc_valid_ops2_SC in Hcon; eauto.
   -clarify. eauto.
   -rewrite Forall_forall. intros c Hin. simpl.
    inversion Hvs1. inversion Hvs2.
    exploit mops_max_vc_off'.
    { apply H0. }
    { apply H1. }
    instantiate(1:= t). instantiate (1:= C2). instantiate (1:= C1).
    intro Hcltz. rewrite Forall_forall in Hcltz. apply Hcltz in Hin.
    intro Heq. destruct (loc_of c); clarify.
    eapply lt_irrefl. eauto.
   -clarify.
  }
  { apply le_Sn_le. auto. }
  {
    intros (IH1 & IH2); rewrite IH1, IH2.
    specialize (Hmatch1 z); specialize (Hmatch2 z).
    destruct (lt_dec z zt); [| omega ].
    generalize (can_read_thread' _ _ _ _ Hn), (can_read_thread' _ _ _ _ Hn0); clarify.
    generalize ( consistent_app_SC _ _ Hn); intro.
    generalize (can_read_unique(m:=m) (p:= (C1, z)) n (V1 z)); clarify.
    generalize (can_read_unique(m:=m) (p:= (C2, z)) n0 (V2 z)); clarify.
  }
Qed.

Corollary max_vc_vals : forall m C1 C2 vs1 vs2 t V1 V2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_max_vc C1 C2 vs1 vs2 t zt))
  (Hvs1 : length vs1 = zt) (Hvs2 : length vs2 = zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2),
  vs1 = map V1 (rev (interval 0 zt)) /\ vs2 = map V2 (rev (interval 0 zt)).
Proof.
  intros; eapply max_vc_vals1 with (C1 := C1); eauto.
Qed.


Lemma mops_set_vc_off':
  forall (src tgt : var) (vs: list nat) (t : tid) (n : nat),
  length vs = n ->
  Forall (fun c' : conc_op => let (_, o) := loc_of c' in o < n)
         (mops_set_vc src tgt n t vs).
Proof.
  clarify.
  rewrite Forall_forall. induction vs; clarify.
  destruct H as [Hx|[Hx|Hin]]; clarify.
  apply IHvs in Hin. destruct (loc_of x); clarify.
Qed.


Transparent move mops_move.
Lemma set_vc_vals1: forall m C1 C2 z vs t V1
  (Hinit1: forall z, z < zt -> initialized m (C1, z))
  (Hcon: consistent (m ++mops_set_vc C1 C2 z t vs ))
  (Hvs: length vs =z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) ,
  vs = map V1 (rev (interval 0 z)) .
Proof.
  induction z; destruct vs; clarify.
  rewrite rev_app_distr; clarify.
  assert ( consistent (m++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC. rewrite <- app_assoc; simpl; eauto. }

  exploit (IHz vs); eauto.
  {rewrite read_noop_SC in Hcon; eauto.
   rewrite loc_valid_ops2_SC in Hcon; eauto.
   -clarify. eauto.
   -rewrite Forall_forall. intros c Hin. simpl.
    inversion Hvs.  
    exploit mops_set_vc_off'.
    instantiate(1:= z). instantiate (1:= vs). auto. 
    intro Hcltz. rewrite Forall_forall in Hcltz. apply Hcltz in Hin.
    intro Heq. destruct (loc_of c); clarify.
    eapply lt_irrefl. eauto.
   -clarify.
  }
  { apply le_Sn_le. auto. }
  { 
    intros IH1; rewrite IH1.
    destruct (lt_dec z zt); [| omega ].
    generalize (can_read_thread' _ _ _ _ Hn); clarify.
    generalize ( consistent_app_SC _ _ Hn); intro.
    generalize (can_read_unique(m:=m) (p:= (C1, z)) n (V1 z)); clarify.
    specialize (Hmatch1 z); clarify.
  }
Qed.



Corollary set_vc_vals : forall m C1 C2 vs t V1
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hcon : consistent (m ++ mops_set_vc C1 C2 zt t vs))
  (Hvs : length vs = zt)
  (Hmatch1 : clock_match m V1 C1) ,
  vs = map V1 (rev (interval 0 zt)).
Proof.
  intros; eapply set_vc_vals1 with (C1 := C1); eauto.
Qed.

Lemma hb_check_vals1 : forall m C1 C2 z vs1 vs2 t V1 V2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t))
  (Hvs1 : length vs1 = z) (Hvs2 : length vs2 = z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hle : first_gt vs1 vs2 = None),
  vs1 = map V1 (rev (interval 0 z)) /\ vs2 = map V2 (rev (interval 0 z)).
Proof.
  induction z; destruct vs1, vs2; clarify.
  rewrite rev_app_distr; clarify.
  assert (consistent (m ++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert (consistent (m ++ [Read t (C2, z) n0])) as Hn0.
  { rewrite read_noop_SC in Hcon; auto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  exploit (IHz vs1 vs2); eauto.
  { do 2 (rewrite read_noop_SC in Hcon; eauto). }
  { omega. }
  intros (IH1 & IH2); rewrite IH1, IH2.
  specialize (Hmatch1 z); specialize (Hmatch2 z).
  destruct (lt_dec z zt); [|omega].
  generalize (can_read_thread' _ _ _ _ Hn), (can_read_thread' _ _ _ _ Hn0);
    clarify.
  generalize (consistent_app_SC _ _ Hn); intro.
  generalize (can_read_unique(m := m)(p := (C1, z)) n (V1 z)); clarify.
  generalize (can_read_unique(m := m)(p := (C2, z)) n0 (V2 z)); clarify.
Qed.  

Corollary hb_check_vals : forall m C1 C2 vs1 vs2 t V1 V2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 zt t))
  (Hvs1 : length vs1 = zt) (Hvs2 : length vs2 = zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hle : first_gt vs1 vs2 = None),
  vs1 = map V1 (rev (interval 0 zt)) /\ vs2 = map V2 (rev (interval 0 zt)).
Proof.
  intros; eapply hb_check_vals1 with (C1 := C1); eauto.
Qed.
  
Typeclasses eauto := 5.


Lemma clock_match_value: forall m vct ct t v x
  (Hmatch: clock_match (m++[Read t (ct, x) v]) vct ct) (Hinit: initialized m (ct,x))
  (Hx : x < zt),                         v = vct x.
Proof.
  intros.
  unfold clock_match in *. specialize (Hmatch x). clarify.
  assert(Hcon: consistent (m ++ [Read t (ct, x) v])).
    eapply consistent_app_SC. eauto.
  assert(Hcan_read1: can_read m (ct, x) v).
    unfold can_read, consistent, SC in *. setoid_rewrite lower_app in Hcon. rewrite lower_single in Hcon. unfold can_read, consistent, SC.  setoid_rewrite lower_app. rewrite lower_single.
    clarify. 
  assert(Hcan_read2: can_read m (ct, x) (vct x)).
    unfold can_read in Hmatch1. rewrite <- app_assoc in Hmatch1.
    setoid_rewrite reads_noops_SC in Hmatch1; auto.
  apply can_read_unique with (m:= m) (p:=(ct,x)); auto.
  eapply consistent_app_SC; eauto.
Qed.

Lemma clock_match_nomod: forall m1 m2 vct ct
  (Hmatch_m1: clock_match m1 vct ct) (Hcon: consistent (m1++m2) ) (Hprog: Forall prog_op m2)
   (Hnmods: Forall (fun c => match c with | Write _ (x,o) _ => ct <> x
     | ARW _ (x,o) _ _=> ct <> x | _ => True end)  m2),     clock_match (m1++m2) vct ct.
Proof.
  induction m2; intros; auto.
  -rewrite app_nil_r in *. auto.
  -unfold clock_match. intros.
   inversion Hnmods; clarify.
   assert(Hcon_a : consistent (m1++[a])).
   eapply consistent_app_SC. rewrite <- split_app. eauto.
   assert(Himpl: forall x,  (fun x0 : conc_op =>
          match x0 with
          | Write _ (p, _) _ => ct <> p
          | ARW _ (p, _) _ _ => ct <> p
          | _ => True
          end) x -> (forall t, (fun x0 : conc_op => 
          match x0 with
          | Write _ x _ => (ct, t) <> x
          | ARW _ x _ _ => (ct, t) <> x
          | _ => True
          end) x) ).
     intros x0 Himpl0. destruct x0; clarify; intro Heq; clarify.
     
   destruct (lt_dec t zt); clarify.
   unfold clock_match in Hmatch_m1. specialize(Hmatch_m1 t).  
   +split.
    *apply can_read_SC;clarify.
     apply Forall_cons.
       destruct a; clarify;
       intro Heq; clarify.
       eapply Forall_impl.
       {intros. apply Himpl. apply H.  }
       {auto. }
    *apply can_write_SC;clarify.
   +unfold clock_match in Hmatch_m1. specialize(Hmatch_m1 t).
    clarify.
Qed.

Print meta_loc.

Definition meta_loc'  (x : ptr) :=
C' <= fst x < C' + zt \/
L' <= fst x < L' + zl \/
R' <= fst x < R' + zv \/ W' <= fst x < W' + zv 
     .
Lemma clocks_sim_nonmeta:  forall m1 m2 s
  (Hsim1: clocks_sim m1 s) (Hcon: consistent (m1++m2) ) (Hprog: Forall prog_op m2)
  (Hloc: Forall (fun c => ~ meta_loc' (loc_of c))  m2),     clocks_sim (m1++m2) s.
Proof.
  unfold clocks_sim. clarify.
  split;[|split]; clarify; try split;
  apply clock_match_nomod; auto;try solve[ eapply Forall_impl; eauto; clarify; destruct a; clarify;
  destruct x; clarify; intro Heq; contradiction H0; unfold meta_loc'; clarify; omega];
  try specialize(Hsim122 v H); clarify.
Qed.


Lemma clocks_sim_allreads: forall m1 m2 s
   (Hsim1: clocks_sim m1 s) (Hcon: consistent (m1++m2)) (Hprog: Forall prog_op m2)
   (Hnmods: Forall (fun c => match c with | Read _ _ _ => True | _ => False end) m2),
                                   clocks_sim (m1++m2) s.
Proof.
  unfold clocks_sim. clarify. 
  split;[|split]; clarify; try split; 
  apply clock_match_nomod; auto; try solve [eapply Forall_impl; eauto; clarify; destruct a; clarify];
  try specialize(Hsim122 v H); clarify.
Qed.

Lemma can_read_written_SC: forall m t p v (Hcon: consistent (m++[Write t p v])),
                             can_read (m++[Write t p v]) p v.
Proof.
  intros.
  unfold can_read. rewrite <- app_assoc. unfold consistent, SC, seq_con in *. repeat rewrite lower_app in *. repeat rewrite lower_single in *. clarify. rewrite read_written; auto.
  rewrite lower_app, lower_single in Hcon. clarify.
Qed.



Lemma clock_match_mods: forall m vr r t t' v x (Hclock_match_m: clock_match m (vr x) (r+x))
                              (Hcon: consistent (m++[Write t' (r+x,t ) v])) (Ht: t < zt),
                          clock_match (m++[Write t' (r+x,t) v]) (upd vr x (upd (vr x) t v) x) (r+x).
Proof.
  intros.
  unfold clock_match in *. intros t0. specialize (Hclock_match_m t0).
  destruct (lt_dec t0 zt); clarify.
  -split.
   +destruct (eq_dec t t0) eqn: Heq; clarify.
    *unfold upd. clarify.
     apply can_read_written_SC; auto.
    *unfold upd. clarify.
     apply can_read_SC; eauto.
     { rewrite Forall_forall. intros c Hin. clarify. }
     { rewrite Forall_forall. intros c Hin. clarify.  intro Heq'.
       inversion Heq'; clarify. }
   +apply can_write_SC; auto.
    rewrite Forall_forall; intros x0 Hin; inversion Hin; clarify.
  -unfold upd; clarify.
Qed.

Lemma clocks_sim_writeR: forall c l r w m m' (s s': vstate) t t' v x
  (Hsim: clocks_sim m s) (Ht: t < zt) (Hcon: consistent m') (Hx: x < zv)
  (Hs: s= (c,l,r,w)) (Hs': s'=(c,l,upd r x (upd (r x) t v),w)) 
  (Hm': m'=(m++[Write t' (R'+x, t) v])) ,
                           clocks_sim m' s'.
Proof.
  unfold clocks_sim in *. clarify.
  assert (Forall prog_op [Write t' (R' + x, t) v]) as Hprog_op.
  { rewrite Forall_forall. clarify. }
  split;[|split;[|intros; split]];
  try solve [ intros; apply clock_match_nomod; clarify]; try specialize(Hsim22 v0 H); clarify.
  -destruct (eq_dec v0 x).
   +clarify. apply clock_match_mods; auto.
   +apply clock_match_nomod; auto.
    *assert(upd r x (upd (r x) t v) v0 = r v0) as Hrv0.
     { unfold upd. clarify. }
     rewrite Hrv0. auto.
    *rewrite Forall_forall.
     intros x0 Hin; destruct x0; clarify; destruct x0; inversion H0; clarify.
     omega.
  -apply clock_match_nomod; clarify.
Qed.

Lemma clocks_sim_writeW: forall c l r w m m' (s s': vstate) t t' v x
  (Hsim: clocks_sim m s) (Ht: t < zt) (Hcon: consistent m') (Hx: x < zv)
  (Hs: s= (c,l,r,w)) (Hs': s'=(c,l,r,upd w x (upd (w x) t v))) 
  (Hm': m'=(m++[Write t' (W'+x, t) v])) ,
                           clocks_sim m' s'.
Proof.
  unfold clocks_sim in *. clarify.
  assert (Forall prog_op [Write t' (W' + x, t) v]) as Hprog_op.
  { rewrite Forall_forall. clarify. }
  split;[|split;[|intros; split]];
  try solve [ intros; apply clock_match_nomod; clarify]; try specialize(Hsim22 v0 H); clarify.
  -apply clock_match_nomod; clarify.
   rewrite Forall_forall; intros x0 Hin; destruct x0; clarify. destruct x0; inversion H0; clarify. intro Heq. specialize(Hmetalocs_disjoint_WR Hx H). clarify.
  -destruct (eq_dec v0 x).
   +clarify. apply clock_match_mods; auto.
   +apply clock_match_nomod; auto.
    *assert(upd w x (upd (w x) t v) v0 = w v0) as Hwv0.
     { unfold upd. clarify. }
     rewrite Hwv0. auto.
    *rewrite Forall_forall.
     intros x0 Hin; destruct x0; clarify; destruct x0; inversion H0; clarify.
     omega.
Qed.


Lemma clocks_sim_writeC: forall c l r w m m' (s s': vstate) t t' v tx
  (Hsim: clocks_sim m s) (Ht: t < zt) (Hcon: consistent m') (Hx: tx < zt)
  (Hs: s= (c,l,r,w)) (Hs': s'=(upd c tx (upd (c tx) t v),l,r,w)) 
  (Hm': m'=(m++[Write t' (C'+tx, t) v])) ,
                           clocks_sim m' s'.
Proof.
  unfold clocks_sim in *. clarify.
  assert (Forall prog_op [Write t' (C' + tx, t) v]) as Hprog_op.
  { rewrite Forall_forall. clarify. }
  split;[|split;[|intros; split]];
  try solve [ intros; apply clock_match_nomod; clarify]; try specialize(Hsim22 v0 H); clarify.
  -destruct (eq_dec t0 tx).
   + clarify. apply clock_match_mods; auto.
   +apply clock_match_nomod; auto.
    *assert(upd c tx (upd (c tx) t v) t0 =  c t0) as Hwv0.
     { unfold upd. clarify. }
     rewrite Hwv0. auto.
    *rewrite Forall_forall.
     intros x0 Hin; destruct x0; clarify. destruct x; inversion H0; clarify.
     omega.
  -apply clock_match_nomod; clarify.
   rewrite Forall_forall; intros x0 Hin; destruct x0; clarify. destruct x; inversion H0; clarify. intro Heq. specialize(Hmetalocs_disjoint_CL H Hx). clarify.
  -apply clock_match_nomod; clarify. repeat constructor; clarify.
   specialize(Hmetalocs_disjoint_CR Hx H). clarify.
  -apply clock_match_nomod; clarify. repeat constructor; clarify.
   specialize(Hmetalocs_disjoint_CW Hx H). clarify.
Qed.

Definition clock_match_z m V x z:= forall t,
  if lt_dec t z then can_read m (x, t) (V t) /\ can_write m (x, t)
  else True.

   
Lemma clock_match_mods_z: forall m vr r t t' v x f z (Hclock_match_m: clock_match_z m (vr x) (r+x) z)
                              (Hcon: consistent (m++[Write t' (r+x,t ) v])) (Ht: t < z)
                           (Hf: forall y, y< z -> f y = (upd vr x (upd (vr x) t v) x) y),
                           clock_match_z (m++[Write t' (r+x,t) v]) f (r+x) z.
Proof.
  intros.
  unfold clock_match in *. intros t0. specialize (Hclock_match_m t0).
  destruct (lt_dec t0 z); clarify.
  -split.
   +destruct (eq_dec t t0) eqn: Heq; clarify.
    *rewrite Hf; auto.
     unfold upd. clarify.
     apply can_read_written_SC; auto.
    *rewrite Hf; auto.
     unfold upd. clarify.
     apply can_read_SC; eauto.
     { rewrite Forall_forall. intros c Hin. clarify. }
     { rewrite Forall_forall. intros c Hin. clarify.  intro Heq'.
       inversion Heq'; clarify. }
   +apply can_write_SC; auto.
    rewrite Forall_forall; intros x0 Hin; inversion Hin; clarify.
Qed.


Lemma clock_match_nomod_z: forall m1 m2 vct ct z
  (Hmatch_m1: clock_match_z m1 vct ct z) (Hcon: consistent (m1++m2) ) (Hprog: Forall prog_op m2) (Hz: z <> 0)
   (Hnmods: Forall (fun c => match c with | Write _ (x,o) _ => ct <> x
     | ARW _ (x,o) _ _=> ct <> x | _ => True end)  m2),     clock_match_z (m1++m2) vct ct z.
Proof.
  induction m2; intros; auto.
  -rewrite app_nil_r in *. auto.
  -unfold clock_match_z. intros.
   inversion Hnmods; clarify.
   assert(Hcon_a : consistent (m1++[a])).
   eapply consistent_app_SC. rewrite <- split_app. eauto.
   assert(Himpl: forall x,  (fun x0 : conc_op =>
          match x0 with
          | Write _ (p, _) _ => ct <> p
          | ARW _ (p, _) _ _ => ct <> p
          | _ => True
          end) x -> (forall t, (fun x0 : conc_op => 
          match x0 with
          | Write _ x _ => (ct, t) <> x
          | ARW _ x _ _ => (ct, t) <> x
          | _ => True
          end) x) ).
     intros x0 Himpl0. destruct x0; clarify; intro Heq; clarify.
     
   destruct (lt_dec t z); clarify.
   unfold clock_match_z in Hmatch_m1. specialize(Hmatch_m1 t).  
   +split.
    *apply can_read_SC;clarify.
     apply Forall_cons.
       destruct a; clarify;
       intro Heq; clarify.
       eapply Forall_impl.
       {intros. apply Himpl. apply H.  }
       {auto. }
    *apply can_write_SC;clarify.
Qed.

Lemma clock_match_Sz_z : forall m V x z, clock_match_z m V x (S z)-> clock_match_z m V x z.
Proof.
  unfold clock_match_z, bounded; intros.
  specialize (H t); clarify.
  assert(Hlt:= l). apply lt_S in Hlt. clarify.
Qed.

Lemma clock_match_z_Sz: forall m V x z, can_read m (x, z) (V z) -> can_write m (x, z)-> clock_match_z m V x z -> clock_match_z m V x (S z).
Proof.
  unfold clock_match_z. clarify.
  specialize(H1 t).
  destruct (lt_dec t z); clarify.
  assert(Htz: t=z).
    omega.
  rewrite Htz.
  split; auto.
Qed.

Lemma clock_match_decompose: forall m V x z, z <= zt-> clock_match m V x -> clock_match_z m V x z /\ bounded V zt.
Proof.
  unfold clock_match, clock_match_z, bounded. clarify.
  split; clarify;
  specialize(H0 t); clarify. assert(Hlt:=l). apply lt_le_trans with (p:=zt) in Hlt; clarify.
Qed.

Lemma bounded_z_le: forall V z1 z2, z1 <=z2 -> bounded V z1 -> bounded V z2.
Proof.
  unfold bounded. clarify.
  specialize(H0 t). destruct (lt_dec t z1); clarify.
  apply lt_le_trans with (p:=z2) in l; clarify.
Qed.

Lemma map_same_bounded : forall (X:Type) (f g: nat -> X ) z
  (Hsame_bounded : forall x, x < z -> f x = g x), map f (interval 0 z) = map g (interval 0 z ).                                
Proof.
  induction z; clarify.
  do 2 rewrite map_app. clarify.
  rewrite IHz, Hsame_bounded; auto.
Qed.

Lemma max_comm: forall  a b, Peano.max a b = Peano.max b a.
Proof.
  clarify. destruct (le_dec a b); clarify.
  rewrite max_r; auto. rewrite max_l; auto.
  apply not_le in n. rewrite max_l; try omega. rewrite max_r; omega.
Qed.

Lemma clock_match_iff_z : forall m v V ,
  clock_match m v V <-> clock_match_z m v V zt /\ bounded v zt.                           
Proof.
  clarify.
  split; clarify.
  -split; auto.
   +unfold clock_match_z, clock_match in *.
    clarify. specialize(H t). clarify.
   +eapply clock_match_bounded. eauto.
  -unfold clock_match, clock_match_z in *. clarify.
   specialize(H1 t). clarify.
Qed.


Lemma clock_match_z_max_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t z
  (Hmatch1: clock_match_z m (vc1 t1) (VC1+ t1) z)
  (Hmatch2: clock_match_z m (vc2 t2) (VC2 + t2) z)
  (Hdistinct:  VC1 + t1 <> VC2 + t2)
  (Hcon: consistent (m ++ mops_max_vc (VC1+t1) (VC2 + t2) (map (vc1 t1) (rev (interval 0 z))) (map (vc2 t2) (rev (interval 0 z ))) t z )) (* (Hz: z <> 0)  (Ht2: t2 < z)*),
                             clock_match_z (m ++ mops_max_vc (VC1+t1) (VC2+t2) (map (vc1 t1) (rev (interval 0 z))) (map (vc2 t2) (rev (interval 0 z))) t z) (upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) (VC2+t2) z.
Proof.
  intros. generalize dependent m. generalize dependent vc1. generalize dependent vc2. 
  induction z; clarify.
  rewrite rev_unit in *. clarify.
  do 3 rewrite split_app in *.
  assert( consistent (m ++ Read t (VC1 + t1, z) (vc1 t1 z)
            :: Read t (VC2 + t2, z) (vc2 t2 z)
            :: [Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))])) as Hcon1.
    apply consistent_app_SC in Hcon.
    do 2 rewrite <- app_assoc in Hcon. clarify.
  assert(  clock_match_z
     (((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
       [Read t (VC2 + t2, z) (vc2 t2 z)]) ++
      [Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))] )
     (vc1 t1) (VC1 + t1) 
     (S z)) as Hm1.
  {
    do 2 rewrite <-app_assoc.  simpl.
    eapply clock_match_nomod_z; eauto.
    rewrite Forall_forall. intros c Hin. destruct Hin as [?|[?|?]]; clarify.
  }
  assert(  clock_match_z
     (((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
       [Read t (VC2 + t2, z) (vc2 t2 z)]) ++
      [Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))] )
     (upd vc2 t2 (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2) (VC2 + t2) 
     (S z)) as Hm2.
  {
    eapply clock_match_mods_z; eauto.
    -rewrite <-app_assoc. simpl.
     apply clock_match_nomod_z; eauto.
     +eapply consistent_app_SC; eauto.
      instantiate(1:=[Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))]).
      rewrite <- app_assoc. clarify.
     +rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
    -do 2 rewrite <- app_assoc. clarify.
    
  }
  assert(Hm2z:=Hm2). assert(Hm1z:=Hm1).
  apply clock_match_Sz_z in Hm2z. apply clock_match_Sz_z in Hm1z.
 
  assert(  map (vc2 t2) (rev (interval 0 z)) = map
                (upd vc2 t2
                   (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2)
                (rev (interval 0 z))) as Hmap.
  {
    do 2 rewrite map_rev.
    rewrite map_same_bounded with (g:=(upd vc2 t2 (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2)); clarify.
    unfold upd. clarify. apply lt_irrefl in H. clarify.
  }
  rewrite Hmap in Hcon. 
  specialize(IHz _ _ _ Hm1z Hm2z Hcon). rewrite <- Hmap in IHz.
  assert((upd
             (upd vc2 t2 (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))))
             t2
             (vc_join
                (upd vc2 t2
                   (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2)
                (vc1 t1)) t2) = upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) as Hfun.
  {
    unfold upd, vc_join. clarify. apply functional_extensionality. clarify.
    destruct (le_dec (vc1 t1 x) (vc2 t2 x)); clarify.
    -rewrite max_r with (m:=(vc2 t2 x)); auto.
    -apply not_le in n. rewrite max_r; auto.
     +rewrite max_r; auto. omega.
     +rewrite max_l; auto. omega.
  }
  setoid_rewrite Hfun in IHz.
  apply clock_match_z_Sz; auto.
  -apply can_read_SC; auto.
   +unfold vc_join, upd. clarify.
    rewrite max_comm.
    apply can_read_written_SC; auto.
    rewrite max_comm. do 2 rewrite <- split_app. auto.
   +rewrite Hmap; auto.
   +rewrite Forall_forall. clarify. apply in_mops_max_vcn in H.
    destruct x; clarify.
    destruct x; clarify.
    intro Heq. inversion Heq; clarify. apply (lt_irrefl n). auto.
  -do 3 rewrite <- split_app.  
   apply can_write_SC; auto.
   +unfold clock_match_z in Hmatch2. specialize(Hmatch2 z). clarify.
    contradiction n. omega.
   +do 3 rewrite split_app.  rewrite Hmap . auto.
   +rewrite Forall_forall. intros c Hin. 
    destruct Hin as [Hin | [Hin|[Hin|Hin]]]; clarify.
    apply in_mops_max_vc in Hin. destruct c; clarify. auto.
Qed.



Lemma clock_match_max_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t 
  (Hmatch1: clock_match m (vc1 t1) (VC1+ t1) )
  (Hmatch2: clock_match m (vc2 t2) (VC2 + t2) )
  (Hdistinct:  VC1 + t1 <> VC2 + t2)
  (Hcon: consistent (m ++ mops_max_vc (VC1+t1) (VC2 + t2) (map (vc1 t1) (rev (interval 0 zt))) (map (vc2 t2) (rev (interval 0 zt ))) t zt )) ,
                             clock_match (m ++ mops_max_vc (VC1+t1) (VC2+t2) (map (vc1 t1) (rev (interval 0 zt))) (map (vc2 t2) (rev (interval 0 zt))) t zt) (upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) (VC2+t2).
Proof.
  clarify. rewrite clock_match_iff_z in *. split; clarify.
  -apply clock_match_z_max_vc; auto.
  -unfold bounded, upd, vc_join in *; clarify.
   rewrite Hmatch12, Hmatch22; auto.
Qed.

Lemma clocks_sim_max_vc_LC : forall m vc1 vc2 t1 t2 t s s' m2
  (Hclocks_sim: clocks_sim m s )
  (Hs_lock: lock_of s = vc1) (Hs_clock: clock_of s = vc2)
  (Ht1: t1 < zl) (Ht2: t2 < zt)
  (Hm2: m2=mops_max_vc (L'+t1) (C'+t2) (map (vc1 t1) (rev (interval 0 zt))) (map (vc2 t2) (rev (interval 0 zt))) t zt)
  (Hs': lock_of s = lock_of s' /\ read_of s = read_of s' /\ write_of s = write_of s'
       /\ clock_of s'= upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) )                                                                           
  (Hcon: consistent (m ++ m2 )) ,
                             clocks_sim (m ++ m2) s' .
Proof.
  unfold clocks_sim; clarify. 
  split;[|split]; clarify; try split.
  -rewrite Hs'222. destruct (eq_dec t0 t2); clarify.
   +eapply clock_match_max_vc; clarify. intro Heq.
    specialize(Hmetalocs_disjoint_CL Ht1 Ht2). clarify.
   +rewrite VectorClocks.upd_old; clarify. apply clock_match_nomod; auto.
    rewrite Forall_forall. intros x Hxin. apply in_mops_max_vc' in Hxin.
    destruct x; clarify; destruct x; clarify. omega.
  -rewrite <- Hs'1. apply clock_match_nomod; auto;rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_CL H Ht2). clarify.
  -rewrite <- Hs'21. specialize(Hclocks_sim22 v H). apply clock_match_nomod; clarify; rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_CR Ht2 H). clarify.
  -rewrite <- Hs'221. specialize(Hclocks_sim22 v H). apply clock_match_nomod; clarify; rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_CW Ht2 H). clarify.
Qed.

Lemma clocks_sim_max_vc_CL : forall m vc1 vc2 t1 t2 t s s' m2
  (Hclocks_sim: clocks_sim m s )
  (Hs_lock: lock_of s = vc2) (Hs_clock: clock_of s = vc1)
  (Ht1: t1 < zt) (Ht2: t2 < zl)
  (Hm2: m2=mops_max_vc  (C'+t1) (L'+t2) (map (vc1 t1) (rev (interval 0 zt))) (map (vc2 t2) (rev (interval 0 zt))) t zt)
  (Hs': lock_of s' = upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) /\ read_of s = read_of s' /\ write_of s = write_of s'
       /\ clock_of s'= clock_of s )                                                                           
  (Hcon: consistent (m ++ m2 )) ,
                             clocks_sim (m ++ m2) s' .
Proof.
  unfold clocks_sim; clarify. 
  split;[|split]; clarify; try split.
  -rewrite Hs'222. apply clock_match_nomod; auto;rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
  -rewrite Hs'1. destruct (eq_dec l t2); clarify.
   +eapply clock_match_max_vc; clarify. 
   +rewrite VectorClocks.upd_old; clarify. apply clock_match_nomod; auto.
    rewrite Forall_forall. intros x Hxin. apply in_mops_max_vc' in Hxin.
    destruct x; clarify; destruct x; clarify. omega.
  -rewrite <- Hs'21. specialize(Hclocks_sim22 v H). apply clock_match_nomod; clarify;
   rewrite    Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_LR Ht2 H). clarify.
  -rewrite <- Hs'221. specialize(Hclocks_sim22 v H).
   apply clock_match_nomod; clarify;
   rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_LW Ht2 H). clarify.
Qed.


Lemma clocks_sim_max_vc_CC : forall m vc t1 t2 t s s' m2
  (Hclocks_sim: clocks_sim m s )
  (Hs_clock: clock_of s = vc)
  (Ht1: t1 < zt) (Ht2: t2 < zt) (Ht12: t1<>t2)
  (Hm2: m2=mops_max_vc (C'+t1) (C'+t2) (map (vc t1) (rev (interval 0 zt))) (map (vc t2) (rev (interval 0 zt))) t zt)
  (Hs': lock_of s = lock_of s' /\ read_of s = read_of s' /\ write_of s = write_of s'
       /\ clock_of s'= upd vc t2 (vc_join (vc t2) (vc t1)) )                                                                           
  (Hcon: consistent (m ++ m2 )) ,
                             clocks_sim (m ++ m2) s' .
Proof.
  unfold clocks_sim; clarify. 
  split;[|split]; clarify; try split.
  -rewrite Hs'222. destruct (eq_dec t0 t2); clarify.
   +eapply clock_match_max_vc; clarify. omega.
   +rewrite VectorClocks.upd_old; clarify. apply clock_match_nomod; auto.
    rewrite Forall_forall. intros x Hxin. apply in_mops_max_vc' in Hxin.
    destruct x; clarify; destruct x; clarify. omega.
  -rewrite <- Hs'1. apply clock_match_nomod; auto;rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_CL H Ht2). clarify.
  -rewrite <- Hs'21. specialize(Hclocks_sim22 v H). apply clock_match_nomod; clarify; rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_CR Ht2 H). clarify.
  -rewrite <- Hs'221. specialize(Hclocks_sim22 v H). apply clock_match_nomod; clarify; rewrite Forall_forall; intros x Hxin; apply in_mops_max_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_CW Ht2 H). clarify.
Qed.




Lemma in_mops_set_vc': forall n c vc1 vc2 vs t
  (Hin: In c (mops_set_vc vc1 vc2 n t vs)) ,
match c with
    | Read _ _ _ => True
    | Write _ (x,o) _ => x=vc2 /\ o < n 
    | _ => False
  end.
Proof.
  induction n; intros; destruct vs; clarify; destruct c; clarify;
    try solve [exploit IHn; eauto].
  exploit IHn; eauto.
  destruct x; clarify.
Qed.

Lemma clock_match_inc_vc : forall m VC1 vc1 t1 t v
  (Hmatch: clock_match m (vc1 t1) (VC1 + t1)) (Hinit: initialized m (VC1+ t1,t))
  (Ht: t < zt)
  (Hcon: consistent (m ++ mops_inc_vc (VC1 + t1) v t )),
                               clock_match (m ++ mops_inc_vc (VC1 + t1) v t) (upd  vc1 t1 (vc_inc t (vc1 t1)) t1)  (VC1 + t1).
Proof.
  intros. unfold mops_inc_vc; clarify.
  rewrite split_app.
  assert( clock_match (m ++ [Read t (VC1 + t1, t) v]) (vc1 t1) (VC1 + t1)) as Hcmr.
  {
    apply clock_match_nomod; auto.
    -unfold mops_inc_vc in *; clarify.
     eapply consistent_app_SC; eauto. rewrite <- app_assoc. simpl. eapply Hcon.
    -rewrite Forall_forall. clarify.
  }
  assert( v= vc1 t1 t) as Hv.
  {
    eapply clock_match_value; eauto.
  } 
  assert( vc_inc t (vc1 t1) = upd (vc1 t1) t (v+1) ) as Hvc1.
  {
    unfold vc_inc, upd; clarify.
    apply functional_extensionality. clarify. destruct (eq_dec x t); clarify.
    omega.
  }
  rewrite Hvc1.
  apply clock_match_mods; auto.
  rewrite <- app_assoc. clarify.
Qed.
  


Lemma clock_match_inc_vc' : forall m VC1 vc1 t1 t t' v
  (Hmatch: clock_match m (vc1 t1) (VC1 + t1)) (Hinit: initialized m (VC1+ t1,t))
  (Ht: t < zt)
  (Hcon: consistent (m ++ mops_inc_vc' (VC1 + t1) v t' t )),
                               clock_match (m ++ mops_inc_vc' (VC1 + t1) v t' t) (upd  vc1 t1 (vc_inc t (vc1 t1)) t1)  (VC1 + t1).
Proof.
  intros. unfold mops_inc_vc'; clarify.
  rewrite split_app.
  assert( clock_match (m ++ [Read t' (VC1 + t1, t) v]) (vc1 t1) (VC1 + t1)) as Hcmr.
  {
    apply clock_match_nomod; auto.
    -unfold mops_inc_vc' in *; clarify.
     eapply consistent_app_SC; eauto. rewrite <- app_assoc. simpl. eapply Hcon.
    -rewrite Forall_forall. clarify.
  }
  assert( v= vc1 t1 t) as Hv.
  {
    eapply clock_match_value; eauto.
  } 
  assert( vc_inc t (vc1 t1) = upd (vc1 t1) t (v+1) ) as Hvc1.
  {
    unfold vc_inc, upd; clarify.
    apply functional_extensionality. clarify. destruct (eq_dec x t); clarify.
    omega.
  }
  rewrite Hvc1.
  apply clock_match_mods; auto.
  rewrite <- app_assoc. clarify.
Qed.

Lemma clock_match_z_set_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t z
  (Hmatch1: clock_match_z m (vc1 t1) (VC1+ t1) z)
  (Hmatch2: clock_match_z m (vc2 t2) (VC2+ t2) z)
  (Hcon: consistent (m ++ mops_set_vc (VC1+t1) (VC2 + t2) z t (map (vc1 t1) (rev (interval 0 z))) )) (Hdistinct: VC1 + t1 <> VC2 + t2),  
                             clock_match_z (m ++ mops_set_vc (VC1+t1) (VC2+t2) z t (map (vc1 t1) (rev (interval 0 z)))) (upd vc2 t2 (vc1 t1) t2) (VC2+t2) z.
Proof.
  intros. generalize dependent m. generalize dependent vc1. generalize dependent vc2. 
  induction z; clarify.
  rewrite rev_unit in *. clarify.
  do 2 rewrite split_app in *.
  assert( consistent (m ++ Read t (VC1 + t1, z) (vc1 t1 z)
            :: [Write t (VC2 + t2, z) (vc1 t1 z)])) as Hcon1.
    apply consistent_app_SC in Hcon.
    rewrite <- app_assoc in Hcon. clarify.
  assert(  clock_match_z
     ((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
      [Write t (VC2 + t2, z) (vc1 t1 z)] )
     (vc1 t1) (VC1 + t1) 
     (S z)) as Hm1.
  {
    rewrite <-app_assoc.  simpl.
    eapply clock_match_nomod_z; eauto.
    rewrite Forall_forall. intros c Hin. destruct Hin as [?|[?|?]]; clarify.
  }
  assert(  clock_match_z
     ((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
      [Write t (VC2 + t2, z) (vc1 t1 z) ] )
     (upd vc2 t2 (upd (vc2 t2) z (vc1 t1 z) ) t2) (VC2 + t2) 
     (S z)) as Hm2.
  {
    eapply clock_match_mods_z; eauto.
    -apply clock_match_nomod_z; eauto.
     +eapply consistent_app_SC; eauto.
      instantiate(1:=[Write t (VC2 + t2, z) (vc1 t1 z) ]).
      rewrite <- app_assoc. clarify.
     +rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
    -rewrite <- app_assoc. clarify.
    
  }
  assert(Hm2z:=Hm2). assert(Hm1z:=Hm1).
  apply clock_match_Sz_z in Hm2z. apply clock_match_Sz_z in Hm1z.
  specialize(IHz _ _ _ Hm1z Hm2z Hcon). unfold upd in *; clarify.

  apply clock_match_z_Sz; auto.
  -apply can_read_SC; auto.
   +apply can_read_written_SC; auto.
    rewrite <- split_app. auto.
   +rewrite Forall_forall. clarify. apply in_mops_set_vc' in H.
    destruct x; clarify.
    destruct x; clarify.
    intro Heq. inversion Heq; clarify. apply (lt_irrefl n). auto.
  -do 2 rewrite <- split_app.  
   apply can_write_SC; auto.
   +unfold clock_match_z in Hmatch2. specialize(Hmatch2 z). clarify.
    contradiction n. omega.
   +do 2 rewrite split_app.   auto.
   +rewrite Forall_forall. intros c Hin. 
    destruct Hin as [Hin | [Hin|Hin]]; clarify.
    apply in_mops_set_vc' in Hin. destruct c; clarify. 
Qed.


Lemma clock_match_set_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t 
  (Hmatch1: clock_match m (vc1 t1) (VC1+ t1) )
  (Hmatch2: clock_match m (vc2 t2) (VC2+ t2) )
  (Hcon: consistent (m ++ mops_set_vc (VC1+t1) (VC2 + t2) zt t (map (vc1 t1) (rev (interval 0 zt))) )) (Hdistinct: VC1 + t1 <> VC2 + t2),  
                             clock_match (m ++ mops_set_vc (VC1+t1) (VC2+t2) zt t (map (vc1 t1) (rev (interval 0 zt)))) (upd vc2 t2 (vc1 t1) t2) (VC2+t2).
Proof.
  clarify. rewrite clock_match_iff_z in *; split; clarify.
  -apply clock_match_z_set_vc; auto.
  -unfold bounded, upd in *; clarify.
Qed.


Lemma clocks_sim_set_vc_CL : forall m vc1 vc2 t1 t2 t s s' m2
  (Hclocks_sim: clocks_sim m s )
  (Hs_lock: lock_of s = vc2) (Hs_clock: clock_of s = vc1)
  (Ht1: t1 < zt) (Ht2: t2 < zl)
  (Hm2: m2=mops_set_vc  (C'+t1) (L'+t2) zt t (map (vc1 t1) (rev (interval 0 zt))))
  (Hs': lock_of s' = upd vc2 t2 (vc1 t1) /\ read_of s = read_of s' /\ write_of s = write_of s'
       /\ clock_of s'= clock_of s )                                                                           
  (Hcon: consistent (m ++ m2 )) ,
                             clocks_sim (m ++ m2) s' .
Proof.
  unfold clocks_sim; clarify. 
  split;[|split]; clarify; try split.
  -rewrite Hs'222. apply clock_match_nomod; auto;rewrite Forall_forall; intros x Hxin; apply in_mops_set_vc' in Hxin; destruct x; clarify; destruct x; clarify.
  -rewrite Hs'1. destruct (eq_dec l t2); clarify.
   +eapply clock_match_set_vc; clarify. 
   +rewrite VectorClocks.upd_old; clarify. apply clock_match_nomod; auto.
    rewrite Forall_forall. intros x Hxin. apply in_mops_set_vc' in Hxin.
    destruct x; clarify; destruct x; clarify. omega.
  -rewrite <- Hs'21. specialize(Hclocks_sim22 v H). apply clock_match_nomod; clarify;
   rewrite    Forall_forall; intros x Hxin; apply in_mops_set_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_LR Ht2 H). clarify.
  -rewrite <- Hs'221. specialize(Hclocks_sim22 v H).
   apply clock_match_nomod; clarify;
   rewrite Forall_forall; intros x Hxin; apply in_mops_set_vc' in Hxin; destruct x; clarify; destruct x; clarify.
   specialize(Hmetalocs_disjoint_LW Ht2 H). clarify.
Qed.

Lemma hb_check_vals1' : forall m C1 C2 z vs1 vs2 t V1 V2 v1 v2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t))
  (Hvs1 : length vs1 <= z) (Hvs2 : length vs2 <= z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hgt : first_gt  vs1 vs2 = Some (v1, v2)),
   ~ vc_le V1 V2        .
Proof.
  induction z; destruct vs1, vs2; clarify.
  inversion Hvs1.
  assert (consistent (m ++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert (consistent (m ++ [Read t (C2, z) n0])) as Hn0.
  { rewrite read_noop_SC in Hcon; auto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. } 
  destruct (leb n n0) eqn:Hle; clarify.
  -eapply (IHz vs1 vs2); eauto.
   { do 2 (rewrite read_noop_SC in Hcon; eauto). }
   { omega. }
   { omega. }
   { omega. }
  -assert(v2 = V2 z) as Hv2.
   {
     apply clock_match_value with (m:=m) (ct:=C2) (t:=t); auto.
     apply clock_match_nomod; auto.
     rewrite Forall_forall. clarify.
   }
   assert(v1 = V1 z) as Hv1.
   {
     apply clock_match_value with (m:=m) (ct:=C1) (t:=t); auto.
     apply clock_match_nomod; auto.
     rewrite Forall_forall. clarify.
   }
   intro Hvc_le. clarify.
   unfold vc_le in Hvc_le. specialize (Hvc_le z); clarify. rewrite <- leb_le in Hvc_le. clarify.
Qed.
     

Corollary hb_check_vals' : forall m C1 C2 vs1 vs2 t V1 V2 v1 v2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 zt t))
  (Hvs1 : length vs1 <= zt) (Hvs2 : length vs2 <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hle : first_gt vs1 vs2 = Some (v1, v2)),
  ~ vc_le V1 V2.
Proof.
  intros; eapply hb_check_vals1' with (C1 := C1); eauto.
Qed.

Lemma filter_split: forall (X:Type) l1 l2 l3 (f:X->bool)
  (Happ: filter f l3=l1++l2),
  exists l31 l32, l3=l31++l32 /\ filter f l31=l1 /\ filter f l32=l2.
Proof.
  intros ????; revert l1 l2; induction l3; clarify.
  - exploit app_eq_nil; eauto; clarify.
    exists [], []; auto.
  - destruct (f a) eqn: Ha.
    + destruct l1; clarify.
      * exists [], (a :: l3); clarify.
      * exploit IHl3; eauto; intros (l31 & l32 & ?).
        exists (x :: l31), l32; clarify.
    + exploit IHl3; eauto; intros (l31 & l32 & ?).
      exists (a :: l31), l32; clarify.
Qed.

Lemma mem_sim'_split': forall m1 m2 m3
  (Hsim12: mem_sim' (m1++m2) m3),
  exists m31 m32, m3=m31++m32 /\ mem_sim' m1 m31 /\ mem_sim' m2 m32.
Proof.
  intros.
  unfold mem_sim' in *. apply filter_split. auto.
Qed.

Lemma instrument_eq_inv: forall P1 P2 t
                             (Hinst: instrument P1 t=instrument P2 t),
                        P1=P2.
                                                                 
Proof.
  clarify.
  generalize dependent P2.
  induction P1; clarify.
  -destruct P2; clarify.
   assert(instrument_instr i t <> []) as Hnonnil by apply instrument_nonnil;
   contradiction Hnonnil.
   symmetry in Hinst. apply app_eq_nil in Hinst. clarify.
  -destruct P2; clarify.
   +assert(instrument_instr a t <> []) as Hnonnil by apply instrument_nonnil;
    contradiction Hnonnil.
    apply app_eq_nil in Hinst. clarify.
   +apply instrument_incom in Hinst. clarify.
    symmetry in Hinst2. specialize(IHP1 P2 Hinst2). clarify.
Qed.
  
Lemma state_sim_same: forall P1 P2 P3
  (Hsim12: state_sim P1 P2) (Hsim32: state_sim P3 P2),
                        P1=P3.
Proof.
  intros.
  unfold state_sim in *. 
  generalize dependent P3. generalize dependent P2.
  induction P1; clarify.
  -inversion Hsim12. clarify. inversion Hsim32. clarify.
  -destruct P3; clarify.
   +inversion Hsim32. clarify. inversion Hsim12. 
   +destruct P2; clarify.
    *inversion Hsim12; clarify.
    *inversion Hsim12. inversion Hsim32; clarify.
     rewrite <- H21 in H81. rewrite H81 in H82. rewrite H22 in H82.
     apply instrument_eq_inv in H82.
     destruct a,p; clarify.
     specialize(IHP1 P2 H4 P3 H10). clarify.
Qed.

Lemma state_sim_same': forall P1 P2 P3
  (Hsim12: state_sim P1 P2) (Hsim13: state_sim P1 P3),                            
                         P2=P3.
Proof.
  intros.
  unfold state_sim in *.
  generalize dependent P1. generalize dependent P3.
  induction P2; clarify.
  -inversion Hsim12. clarify. inversion Hsim13. clarify.
  -destruct P3; clarify.
   +inversion Hsim13; clarify. inversion Hsim12.
   +destruct P1; clarify.
    *inversion Hsim12.
    *inversion Hsim12; inversion Hsim13; clarify.
     rewrite <- H22 in H82. rewrite H81 in H21. destruct p,a; clarify.
     specialize(IHP2 P3 P1 H4 H10). clarify.
Qed.

Lemma init_can_write: forall m x (Hinit : initialized m x)
  (Hcon : consistent m), can_write m x.
Proof.
  unfold initialized, can_write; clarify.
  unfold consistent, SC in *; destruct Hinit as (i & Hlast & Hi).
  rewrite lower_app, lower_single; simpl.
  rewrite inth_nth_error in Hi; exploit nth_error_split'; eauto;
    intros (m1 & m2 & ? & Heq); rewrite Heq in *.
  rewrite <- app_assoc; simpl.
  rewrite split_app, not_mod_ops_write.
  - rewrite <- app_assoc; simpl.
    rewrite write_not_read_single; clarify.
    rewrite split_app in Hcon.
    generalize (consistent_app _ _ Hcon); intro Hcon'; clarify.
    rewrite write_any_value in Hcon'; eauto.
  - rewrite Forall_forall; intros a ?.
    exploit in_nth_error; eauto; intros (i' & ?).
    inversion Hlast.
    specialize (Hlast0 (length m1 + S i') a).
    rewrite inth_nth_error, nth_error_plus in Hlast0; clarify.
    destruct a; clarify; omega.
  - rewrite <- app_assoc; simpl; auto.
Qed.

Lemma consistent_mem_vals: forall m1 m2 c
     (Hinit: initialized m1 (loc_of c)) (Hcon: consistent (m2++[c])) (Hmem_vals: mem_vals m1 m2) (Hmeta: ~ meta_loc (loc_of c)) (Hprog: prog_op c),
                                     consistent (m1++[c]).
Proof.
  intros.
  unfold mem_vals in Hmem_vals.
  specialize (Hmem_vals (loc_of c) Hmeta Hinit).
  destruct c; clarify.
  -apply can_read_thread. rewrite Hmem_vals. eapply can_read_thread'. eauto.
  -apply can_write_thread. apply init_can_write. auto.
  -apply can_arw_SC.
   +apply ARW_can_read in Hcon. rewrite Hmem_vals. auto.
   +apply init_can_write. auto.
Qed.


Lemma consistent_mem_vals': forall m1 m2 c
     (Hinit1: initialized m1 (loc_of c)) (Hinit2: initialized m2 (loc_of c)) (Hcon: consistent (m1++[c])) (Hmem_vals: mem_vals m1 m2) (Hmeta: ~ meta_loc (loc_of c)) (Hprog: prog_op c),
                              consistent (m2++[c]).
Proof.
  intros.
  unfold mem_vals in *.
  specialize (Hmem_vals (loc_of c) Hmeta Hinit1).
  destruct c; clarify.
  -apply can_read_thread. rewrite <- Hmem_vals. eapply can_read_thread'. eauto.
  -apply can_write_thread. apply init_can_write. auto.
  -apply can_arw_SC.
   +apply ARW_can_read in Hcon. rewrite <- Hmem_vals. auto.
   +apply init_can_write. auto.
Qed.

Lemma clocks_sim_rel : forall m m' s x t
  (Hsim: clocks_sim m s) (Hm': m'=m++[Rel t x ]) (Hcon: consistent m')
  (HnotR: forall v, v < zv->  R'+v <> x)
  (HnotW: forall v, v< zv->  W'+v <> x)
  (HnotC: forall t, t< zt->  C'+t <> x)
  (HnotL: forall l, l< zl-> L'+l <> x),
  clocks_sim m' s.
Proof.
  unfold clocks_sim; clarify.
  assert (Forall prog_op [Rel t x]) as Hprog_rel.
  { rewrite Forall_forall. clarify. }
  split;[|split]; try split; clarify; apply clock_match_nomod; clarify; 
  try specialize(Hsim22 v H); clarify.
Qed.


Lemma ss_trans : forall (s : @VectorClocks.state tid var lock) tr s' tr' s''
  (Hsteps : step_star s tr s')
  (Hsteps' : step_star s' tr' s''), step_star s (tr ++ tr') s''.
Proof.
  intros; induction Hsteps; clarify.
  econstructor; eauto.
Qed.


Instance env_sim_trans : RelationClasses.Transitive env_sim.
Proof.
  intros ??? Hsim1 Hsim2 ????; rewrite Hsim1, Hsim2; auto.
Qed.

Instance env_sim_symm: RelationClasses.Symmetric env_sim.
Proof.
  intros ??? Hsim ???. unfold env_sim in H. symmetry. clarify.
Qed.


Lemma iexec_star_exec_star : forall P G lo lc P' G' (Hiexec : iexec_star P G lo lc P' G'),
  exec_star (Some P) G lo lc (Some P') G'.
Proof.
  intros.
  induction Hiexec.
  -apply exec_refl.
  -apply iexec_exec in Hexec; auto.
   eapply exec_star_trans;
   eauto.
Qed.


Lemma prog_steps' : forall P G lo lc P' G' (Hsteps : iexec_star P G lo lc P' G'),
  Forall prog_op lc.
Proof.
  intros. eapply prog_steps. eapply iexec_star_exec_star. eauto.
Qed.

Lemma exists_in_between: forall a b c, a <= c -> c < a+ b-> b<>0 ->
                                       exists d, c=a+d /\ d < b.
Proof.
    clarify. exists (c-a). split. apply le_plus_minus. auto.
    omega.
Qed.

Hypothesis zl_non_zero: zl <> 0.
Hypothesis zv_non_zero: zv <> 0.

Lemma notmeta_loc'_X : forall x y (Hx: x< zv), ~ meta_loc' (X'+x, y).
Proof.
  intros.
  unfold meta_loc'. intro Habsurd. destruct Habsurd as [Hsb|[Hsb|[Hsb|Hsb]]]; clarify.
  -exploit exists_in_between.
   { apply Hsb1. }
   { eauto. }
   { auto. }
   intro H. inversion H. clarify. 
   specialize(Hmetalocs_disjoint_CX H02 Hx). clarify.
  -exploit exists_in_between.
   { apply Hsb1. }
   { eauto. }
   { auto. }
   intro H. inversion H. clarify. 
   specialize(Hmetalocs_disjoint_LX H02 Hx). clarify.
  -exploit exists_in_between.
   { apply Hsb1. }
   { eauto. }
   { auto. }
   intro H. inversion H. clarify. 
   specialize(Hmetalocs_disjoint_RX H02 Hx). clarify.
  -exploit exists_in_between.
   { apply Hsb1. }
   { eauto. }
   { auto. }
   intro H. inversion H. clarify. 
   specialize(Hmetalocs_disjoint_WX H02 Hx). clarify.
Qed.

Lemma max_self: forall a,
                  Peano.max a a = a.
Proof.
  induction a; clarify.
Qed.

Lemma instrument_sim_safe2 : forall P1 P2 G1 G2 t
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1) (Hdistinct: distinct P2)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m0 (Hinit : forall p, initialized m0 p)
  o2 c2 P2' G2' (Hstep : iexec P2 G2 t o2 c2 P2' G2') m1 m2
  (Hprog_m1: Forall prog_op m1) (Hprog_m2: Forall prog_op m2)
  (Hmem_vals: mem_vals (m0++m1) (m0++m2)) (Hcon1: consistent (m0++m1))
  (Hcon2 : consistent ( (m0++m2) ++ c2)) s (Hs : clocks_sim (m0++m2) s),
  exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\
    state_sim P1' P2' /\ env_sim G1' G2' /\ consistent ((m0++m1) ++ opt_to_list c) /\
    mem_sim c c2 /\
        exists s', step_star s (opt_to_list o) s' /\
                   clocks_sim ((m0++m2) ++ c2) s'.
Proof.
  intros.
  destruct s as (((vc, vl), vr), vw);clarify.
  inversion Hs as [ Hs_c (Hs_l,Hs_rw)].
  assert (Hemc: exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\
                                    mem_sim c c2
                                    /\ consistent ((m0++m1) ++ opt_to_list c)
                                    /\ exists s',
                                         step_star (vc,vl,vr,vw) (opt_to_list o) s'
                                         /\clocks_sim ((m0++m2) ++ c2) s').
   inversion Hstep; clarify; exploit Forall2_app_inv_r; eauto;
   intros (P0' & P3' & HP0 & Hrest & HP1);
   inversion Hrest as [|(tx, [|i ?]) ? ? ? [? Hi] HP3]; clarify.
   - (*assign*)
     exploit (instrument_incom (Assign a e)); simpl; eauto; clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_assign. eauto.
     +unfold mem_sim. intros. simpl. split; clarify.
     +rewrite app_nil_r. auto.
     +exists (vc,vl,vr,vw). simpl. split.
      *apply ss_refl.
      *rewrite app_nil_r. unfold clocks_sim. clarify.
   -(*load*) 
     exploit (instrument_incom (Load a (x, o))).
     { simpl; rewrite <- app_assoc; simpl; eauto. }
     clarify.
     setoid_rewrite Forall_app in Hlocs. clarify.
     inversion Hlocs2; clarify. inversion H2; clarify. 
     do 4 eexists. split;[|split].
     +apply exec_load. eauto.
     +unfold mem_sim. intros. simpl. split; clarify.
      * right. rewrite in_app; right; simpl; eauto. 
      * left.
        rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        rewrite in_app in H1; simpl in H1.
        destruct H1 as [? | [? | [? | [? | [? | ?]]]]]; clarify; contradiction H4.
        { unfold meta_loc; simpl. repeat right. omega. }
        { eapply mops_hb_check_meta; eauto. }
        { unfold meta_loc. simpl. omega. }
        { unfold meta_loc. simpl. right; right; left; omega. }
        { unfold meta_loc. simpl. repeat right. omega. }
     +assert( consistent ((m0 ++ m1) ++ opt_to_list (Some (Read t (x, o) v)))) as Hcon.
      {
        assert(Hlist_silly1: forall (X:Type) (a b c d e: X) (l1 l2 l3 l4: list X), 
                               l1++a::l2++[b;c;d;e]=(l1++[a])++(l2++[b;c])++[d;e]).
        {  intros. simpl. do  2 rewrite app_assoc. clarify. 
           rewrite split_app. rewrite app_assoc. do 2 rewrite split_app. 
           repeat rewrite <- app_assoc. simpl. auto. }
        rewrite Hlist_silly1 in Hcon2; auto. rewrite loc_valid_ops_SC in Hcon2.
        {
          apply consistent_mem_vals with (m2:=m0++m2); auto.
          { apply init_steps; auto. }
          {
            inversion Hcon2; clarify. 
            rewrite loc_valid_ops2_SC in Hcon22.
            -inversion Hcon22; clarify. rewrite <- app_assoc in Hcon222. rewrite loc_valid_ops_SC in Hcon222.
             +inversion Hcon222; clarify.
             +rewrite Forall_forall; clarify.
              rewrite Forall_forall; clarify.
              intro Heq. 
              contradiction H41; repeat right.
              rewrite Heq; clarify; omega.
             + constructor; clarify.
             + constructor; clarify.
            -rewrite Forall_forall; clarify.
             intros Heq. 
             contradiction H41. rewrite <- Heq. repeat right; simpl.
             omega.
            - simpl; auto.
            - constructor; clarify.
          }
          { clarify. }
        }
        { rewrite Forall_forall; intros ? Hin; clarify.
          rewrite Forall_forall; intros ? Hin2; clarify. inversion H2; clarify.
          rewrite Forall_app in Ht. inversion Ht; clarify. inversion Ht2; clarify.
          destruct Hin2.
          - subst; simpl; intro; contradiction H41; rewrite H.
            rewrite in_app in Hin; destruct Hin as [? | [? | ?]]; clarify.
            + eapply mops_hb_check_meta; eauto.
            + left; simpl; omega.
            + right; right; left; simpl; omega.
          - subst; simpl; intro.
            rewrite in_app in Hin; destruct Hin as [? | [? | ?]]; clarify.
            + apply in_mops_hb_check in H1. destruct x0; clarify. 
              destruct H1.
              * exploit Hmetalocs_disjoint_WX; eauto.
              * exploit Hmetalocs_disjoint_CX; eauto.
            + exploit Hmetalocs_disjoint_CX; eauto.
            + exploit Hmetalocs_disjoint_RX; eauto. }
        { rewrite Forall_app; split; auto; repeat constructor; simpl; auto. }
        { repeat constructor; simpl; auto. } }
      split; clarify.
      rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
      inversion Ht; clarify.
       assert(Hsilly: ((m0++m2) ++
            Acq t (X' + x)
            :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
               [Read t (C' + t, t) vt; Write t (R' + x, t) vt;
               Read t (x, o) v; Rel t (X' + x)]) = ((m0++m2) ++
            Acq t (X' + x)
            :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
               [Read t (C' + t, t) vt; Write t (R' + x, t) vt;
                Read t (x, o) v])++ [Rel t (X' + x)] ).
       {
         symmetry. rewrite <- app_assoc. clarify. rewrite split_app. rewrite app_assoc. rewrite app_assoc.  symmetry.
         rewrite split_app; rewrite app_assoc. do 3 rewrite split_app. repeat rewrite <- app_assoc. clarify. }
       assert(Hhb : consistent ((m0++m2) ++ mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t)).
       {
         setoid_rewrite Hsilly in Hcon2. apply consistent_app_SC in Hcon2.
         rewrite loc_valid_ops2_SC in Hcon2; clarify.
         rewrite app_assoc in Hcon21; generalize (consistent_app_SC _ _ Hcon21); auto.
         rewrite Forall_app. split; rewrite Forall_forall; clarify.
         apply in_mops_hb_check in H. destruct x0; clarify. destruct x0; clarify.
         destruct H.
         rewrite H. intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_WX H42 H42). clarify.
         rewrite H. intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_CX H4 H42). clarify.
         destruct H as [?|[?|[?|?]]]; clarify.
         intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_CX H4 H42). clarify.
         intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_RX H42 H42). clarify.
         intro Hwrong. inversion Hwrong. clarify. contradiction H41. unfold meta_loc. clarify. rewrite H1. repeat right. omega.
         rewrite Forall_forall. intros. rewrite in_app in H. inversion H; clarify. 
         apply in_mops_hb_check in H1. destruct x0; clarify.
         destruct H1 as [? |[?|?]]; clarify.
       }
       assert(Hs_rw':= Hs_rw).
       specialize (Hs_rw x); clarify.
       assert(Hinit_m02: forall p, meta_loc p -> initialized (m0++m2) p).
       { intros. apply init_steps; auto. }
       exploit hb_check_vals; try apply Hhb; eauto.
       { intros; apply Hinit_m02; unfold meta_loc; simpl; omega. }
       { intros; apply Hinit_m02; unfold meta_loc; simpl; omega. }
       clarify; eexists; simpl; split. 
       * eapply ss_step; eauto.
         eapply read_upd; eauto.
         eapply first_gt_vc_le; eauto.
         apply ss_refl.
       * assert(Hseq: [Read t (C' + t, t) vt; Write t (R' + x, t) vt; 
         Read t (x, o) v; Rel t (X' + x)] =[Read t (C' + t, t) vt; Write t (R' + x, t) vt] 
                                             ++[Read t (x, o) v; Rel t (X' + x)]) by clarify.
         rewrite Hseq. rewrite split_app, app_assoc, app_assoc.
         assert(Hvt_vctt : vt= vc t t ).
         {
           apply clock_match_value with (m:= (m0++m2) ++
                                                      Acq t (X' + x)
                                                      :: mops_hb_check (W' + x) (C' + t)
                                                      (map (vw x) (rev (interval 0 zt)))
                                                      (map (vc t) (rev (interval 0 zt))) zt t) (ct:=C'+t) (t:=t).
           apply clock_match_nomod; auto.
           -apply clock_match_nomod; auto.
            +apply (consistent_app_SC _  ([Read t (C' + t, t) vt; Write t (R' + x, t) vt;
                                           Read t (x, o) v; Rel t (X' + x)])).
             rewrite <- app_assoc.  rewrite <- app_comm_cons. auto.
            +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
             apply in_mops_hb_check in H; destruct x0; clarify.
            +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
             apply in_mops_hb_check in Hin; destruct x0; clarify.
           -apply (consistent_app_SC _ ([Write t (R'+x,t) vt; Read t (x, o) v; Rel t (X'+x)])).
            rewrite <- split_app. rewrite <- app_assoc,  <- app_comm_cons. auto.
           -rewrite Forall_forall. intros x0 Hin. inversion Hin; clarify.
           -apply init_steps.
            +apply Hinit_m02. unfold meta_loc. clarify. left. omega.
            +rewrite Forall_forall. intros x0 Hin. inversion Hin; clarify.
             apply in_mops_hb_check in H. destruct x0; clarify.
           -auto.
         }
         apply clocks_sim_nonmeta; auto; clarify.
         { rewrite split_app. eapply clocks_sim_writeR; clarify.
           -rewrite <- app_assoc.
            apply clocks_sim_allreads; clarify.
            +apply clocks_sim_acq; clarify. eapply consistent_app_SC; eauto.
            +eapply consistent_app_SC. repeat rewrite <- app_assoc.
             simpl. rewrite app_assoc. eauto.
            +rewrite Forall_app.  split; clarify.
             repeat constructor; clarify.
            +rewrite Forall_app. split; clarify.
             apply mops_hb_check_read.
           -auto.
           -eapply consistent_app_SC. repeat rewrite <- app_assoc. simpl.
            simpl. rewrite app_assoc. eauto.
           -auto.
         }
         { repeat rewrite <- app_assoc. simpl.  rewrite app_assoc. clarify. }
         { repeat constructor; clarify. }
         { repeat constructor; clarify. unfold meta_loc', meta_loc in *; clarify.
           intro Habsurd. contradiction H41. clarify. do 3 right. left. clarify.
           apply notmeta_loc'_X; clarify. }
   -(*store*) (* see above *) 
    exploit (instrument_incom (Store (x, o) e)).
    { simpl; rewrite <- app_assoc; simpl. eauto. }
    clarify.
    do 4 eexists. split;[|split;[|split]].
    +apply exec_store. eauto.
    +unfold mem_sim. intros. simpl. split; clarify.
     { split.
       - right.
         rewrite in_app; right; simpl; eauto.
         rewrite in_app. right. simpl. do 2 right; left. clarify.
         exploit eval_sim.
         {instantiate(1:=G2 t). instantiate(1:=G1 t).  instantiate(1:=e). 
          intros. apply HGsim; intro Heq; clarify. }
         intro Heval. auto.
       - setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H2; clarify.
     }  
     { left.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
       inversion H4; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
       do 2 rewrite in_app in H1. simpl in H1.
       destruct H1 as [? | [? | [? | [? | [? | [? | ?]]]]]]; clarify.
       - contradiction H2. unfold meta_loc. simpl. repeat right. omega.
       - contradiction H2. eapply mops_hb_check_meta; eauto.
       - contradiction H2. eapply mops_hb_check_meta; eauto.
       - contradiction H2. unfold meta_loc. left. simpl. omega.
       - contradiction H2. unfold meta_loc. simpl. do 3 right. left. omega. 
       - exploit eval_sim.
         {instantiate(1:=G2 t). instantiate(1:=G1 t). instantiate(1:=e).
          intros. apply HGsim; intro Heq; clarify. }
         intro Heval. auto.
       - contradiction H2. unfold meta_loc. repeat right. simpl. omega.         
     }
    +assert(Hlist_silly1: forall (X:Type) (a b c d e: X) (l1 l2 l3 l4: list X), 
                             l1++a::l2++l3++[b;c;d;e]=(l1++[a])++(l2++l3++[b;c])++[d;e]).
     { intros. simpl. do  2 rewrite app_assoc. clarify. 
      rewrite split_app. rewrite app_assoc. do 2 rewrite split_app. 
      repeat rewrite <- app_assoc. simpl. auto. }
     rewrite Hlist_silly1 in Hcon2; auto. rewrite loc_valid_ops_SC in Hcon2.
     {
       apply consistent_mem_vals' with (m1:=m0++m2); auto; try apply init_steps; auto. 
       { inversion Hcon2; clarify. 
        rewrite loc_valid_ops2_SC in Hcon22.
        -inversion Hcon22; clarify. rewrite <- app_assoc in Hcon222. rewrite loc_valid_ops_SC in Hcon222.
         +inversion Hcon222; clarify.
          exploit eval_sim.
          {instantiate(1:=G2 t). instantiate(1:=G1 t). instantiate(1:=e). intros. apply HGsim; intro Heq; clarify. }
          intro Heval. rewrite Heval. auto.
         
         +rewrite Forall_forall; clarify.
          rewrite Forall_forall; clarify.
          intro Heq. setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H4; clarify.
          contradiction H81; repeat right.
          rewrite H1; clarify; omega.
         + constructor; clarify.
         + constructor; clarify.
         
        -rewrite Forall_forall; clarify.
         intros Heq. setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H4; clarify.
         contradiction H81; repeat right; simpl.
         rewrite <- H1; omega.
        - simpl; auto.
        - constructor; clarify.
       }
       { apply mem_vals_cond_symm; auto.
         intros. split; clarify; apply init_steps; auto. }
       { unfold safe_locs in Hlocs. 
         rewrite Forall_app in Hlocs. inversion Hlocs as (?&Hlocs2).
         inversion Hlocs2. inversion H3. clarify. }
       { clarify. }
      }
      { rewrite Forall_forall; intros ? Hin; clarify.
        rewrite Forall_forall; intros ? Hin2; clarify.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H2; clarify.
        rewrite Forall_app in Ht. inversion Ht; clarify. inversion Ht2; clarify.
        destruct Hin2.
        - subst; simpl; intro; contradiction H41; rewrite H.
          do 2 rewrite in_app in Hin. destruct Hin as [? | [? | [?|?]]]; clarify.
          + eapply mops_hb_check_meta; eauto.
          + eapply mops_hb_check_meta; eauto.  
          + left; simpl; omega.
          + rewrite <- H7. unfold meta_loc. do 3 right; left; simpl. omega.
        - subst; simpl; intro.
          do 2 rewrite in_app in Hin; destruct Hin as [? | [? | [?|?]]]; clarify.
          + apply in_mops_hb_check in H1. destruct x0; clarify. 
            destruct H1.
            * exploit Hmetalocs_disjoint_WX; eauto.
            * exploit Hmetalocs_disjoint_CX; eauto.
          + apply in_mops_hb_check in H1. destruct x0; clarify.
            destruct H1.
            * exploit Hmetalocs_disjoint_RX; eauto.
            * exploit Hmetalocs_disjoint_CX; eauto.
          + exploit Hmetalocs_disjoint_CX; eauto.
          + exploit Hmetalocs_disjoint_WX; eauto. }

      { do  2 rewrite Forall_app; split; auto; repeat constructor; simpl; auto. }
      { repeat constructor; simpl; auto. }
     +setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
      inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
      rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
      inversion Ht; clarify.
      assert(Hsilly: (
                        [Read t (C' + t, t) v; Write t (W' + x, t) v;
                         Write t (x, o) (eval (G2 t) e); Rel t (X' + x)]) = (
                                                                [Read t (C' + t, t) v; Write t (W' + x, t) v;
                                                                 Write t (x, o) (eval (G2 t) e)])++ [Rel t (X' + x)] ).
      { clarify. }
      
      assert(Hhbs : consistent ((m0++m2) ++ mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++ mops_hb_check (R' + x) (C' + t) vs3 vs2 zt t )).
      {
        rewrite app_comm_cons in Hcon2. do 2 rewrite app_assoc in Hcon2.
        apply consistent_app_SC in Hcon2.
        rewrite <- app_assoc in Hcon2. rewrite <- app_comm_cons in Hcon2. 
        rewrite loc_valid_ops2_SC in Hcon2; clarify.
        -rewrite Forall_forall.  intros c Hin. rewrite in_app in Hin.
         destruct Hin as [Hin | Hin]; clarify; apply in_mops_hb_check in Hin; destruct c; clarify; destruct x0 as (x0,off); intro Heq; inversion Heq; clarify.
         +specialize(Hmetalocs_disjoint_WX H52 H52). specialize (Hmetalocs_disjoint_CX H3 H52). destruct Hin; clarify.
         +specialize(Hmetalocs_disjoint_RX H52 H52). specialize (Hmetalocs_disjoint_CX H3 H52). destruct Hin; clarify.
        -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin.
         destruct Hin as [Hin | Hin]; clarify; apply in_mops_hb_check in Hin; destruct c; clarify.
      }
      assert(Hs_rw':= Hs_rw).
      specialize (Hs_rw x); clarify.
      assert(Hhb1: consistent ( (m0++m2)++ mops_hb_check (W'+x) (C'+t) vs1 vs2 zt t )).
      {  eapply consistent_app_SC; eauto. rewrite <- app_assoc. eauto. }
      assert(Hhb2: consistent ((m0++m2) ++ mops_hb_check (R'+x) (C'+t) vs3 vs2 zt t)).
      {  apply reads_noops_SC in Hhbs; auto. apply mops_hb_check_read. }
      exploit hb_check_vals; try apply Hhb1; eauto.
      { intros; apply init_steps; auto; apply Hinit; auto. }
      { intros; apply init_steps; auto; apply Hinit; auto. }
      exploit hb_check_vals; try apply Hhb2; eauto.
      { intros; apply init_steps; auto; apply Hinit; auto. }
      { intros; apply init_steps; auto; apply Hinit; auto. }
      clarify; eexists; simpl; split. 
      *eapply ss_step; eauto.
       eapply write_upd; eauto.
       eapply first_gt_vc_le; eauto.
       eapply first_gt_vc_le; eauto.
       apply ss_refl.
      *assert(Hvt_vctt : v= vc t t ).
       {
         apply clock_match_value with (m:= (m0++m2) ++
                                             Acq t (X' + x)
                                             :: mops_hb_check (W' + x) (C' + t)
                                             (map (vw x) (rev (interval 0 zt)))
                                             (map (vc t) (rev (interval 0 zt))) zt t ++
                                             mops_hb_check (R' + x) (C' + t)
                                             (map (vr x) (rev (interval 0 zt)))
                                             (map (vc t) (rev (interval 0 zt))) zt t) (ct:=C'+t) (t:=t); auto.
         apply clock_match_nomod; auto.
         -apply clock_match_nomod; auto.
          +apply (consistent_app_SC _  ([Read t (C' + t, t) v; Write t (W' + x, t) v;
                                         Write t (x, o) (eval (G2 t) e); Rel t (X' + x)])); auto.
           rewrite <- app_assoc.  rewrite <- app_comm_cons. repeat rewrite <- app_assoc.
           rewrite app_assoc. auto.
          +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify. 
           rewrite in_app in H; destruct H as [Hin2 | Hin2]; clarify;
           apply in_mops_hb_check in Hin2; destruct x0; clarify.
          +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
           rewrite in_app in Hin; destruct Hin as [Hin | Hin]; clarify;
           apply in_mops_hb_check in Hin; destruct x0; clarify.
         -apply (consistent_app_SC _ ([Write t (W'+x,t) v; Write t (x, o) (eval (G2 t) e); Rel t (X'+x)])); auto.
          rewrite <- split_app. rewrite <- app_assoc,  <- app_comm_cons.
          repeat rewrite <- app_assoc. rewrite app_assoc. auto. 
         -rewrite Forall_forall. intros x0 Hin. inversion Hin; clarify.
         -rewrite <- app_assoc. apply init_steps.
          +apply Hinit. 
          +rewrite Forall_app. clarify.
           rewrite Forall_forall. intros x0 Hin. inversion Hin; clarify.
           rewrite in_app in H; destruct H as [Hin2 | Hin2]; clarify;
           apply in_mops_hb_check in Hin2; destruct x0; clarify.
       }
        do 2 rewrite app_assoc, split_app. rewrite split_app.
       eapply clocks_sim_nonmeta; eauto.
       { eapply clocks_sim_writeW with (s:=(vc,vl,vr,vw)) .
         -instantiate (1:=((((m0 ++ m2) ++ [Acq t (X' + x)]) ++
         mops_hb_check (W' + x) (C' + t) (map (vw x) (rev (interval 0 zt)))
           (map (vc t) (rev (interval 0 zt))) zt t ++
         mops_hb_check (R' + x) (C' + t) (map (vr x) (rev (interval 0 zt)))
           (map (vc t) (rev (interval 0 zt))) zt t) ++ 
        [Read t (C' + t, t) v])).
          repeat rewrite <- app_assoc. do 2 rewrite app_assoc.
          eapply clocks_sim_allreads; eauto.
          +apply clocks_sim_acq; auto.
           eapply consistent_app_SC; eauto.
          +eapply consistent_app_SC; rewrite <- app_assoc; simpl.
           repeat rewrite <- app_assoc. simpl.
           rewrite app_assoc. eauto.
          +rewrite Forall_app; split; [|rewrite Forall_app; split];
           repeat constructor; clarify.
          +rewrite Forall_app; split; [|rewrite Forall_app; split];
           repeat constructor; clarify; apply mops_hb_check_read.
         -apply H3.
         -eapply consistent_app_SC; repeat rewrite <- app_assoc; simpl.
          rewrite app_assoc. eauto.
         -eauto.
         -eauto.
         -eauto.
         -rewrite <- Hvt_vctt. eauto.  
     }
     { do 3 rewrite <- app_assoc. simpl. rewrite <- split_app.
       do 2 rewrite <- app_assoc. rewrite app_assoc. auto. }
     { repeat constructor; clarify. }
     { repeat constructor; clarify.
       -intro Habsurd. contradiction H51. unfold meta_loc' in Habsurd. unfold meta_loc.
        clarify. omega.
       -apply notmeta_loc'_X; auto. }
   -(*lock*) 
     exploit (instrument_incom (Lock m)).
     { simpl;  eauto. }
     clarify.
     setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
     inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
     rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
     inversion Ht; clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_lock. eauto.
     +unfold mem_sim. intros. simpl.
      split; clarify.
      { contradiction H2. eapply mops_max_vc_meta; eauto. }
     +rewrite split_app in Hcon2.
      simpl. eapply consistent_app_SC; eauto.
      rewrite <- split_app. rewrite <- split_app in Hcon2.
      apply consistent_mem_vals with (m2:=m0++m2); clarify.
      *apply init_steps; auto.
      *eapply consistent_app_SC; rewrite <- split_app.  eauto.
     +assert(Hhbs : consistent ((m0++m2) ++ mops_max_vc (L' + m) (C' + t) vs1 vs2 t zt)).
      { rewrite loc_valid_ops2_SC in Hcon2; clarify.
        rewrite Forall_forall.  intros c Hin. apply in_mops_max_vc' in Hin.
        destruct c; clarify;
        intro Heq; contradiction H41; unfold meta_loc.
        -destruct Hin; clarify; try rewrite H; try omega.
        -rewrite <- Heq, Hin. left. omega. 
      }
      exploit max_vc_vals; try apply Hhbs; eauto.
      { intros; apply init_steps;auto; unfold meta_loc; simpl; omega. }
      { intros; apply init_steps;auto; unfold meta_loc; simpl; omega. }
      clarify; eexists; simpl; split. 
      *eapply ss_step; eauto.
       eapply acquire; eauto.
       apply ss_refl.
      *assert(Hcon_acq: consistent ((m0++m2) ++[Acq t m])).
       { eapply consistent_app_SC; eauto.
         instantiate (1:=mops_max_vc (L' + m) (C' + t)
                 (map (vl m) (rev (interval 0 zt)))
                 (map (vc t) (rev (interval 0 zt))) t zt).
         rewrite <- split_app. auto. }
       rewrite split_app. eapply clocks_sim_max_vc_LC; eauto.
       { instantiate(1:=(vc,vl,vr,vw)).
         eapply clocks_sim_nonmeta; clarify.
         -repeat constructor; clarify.
         -repeat constructor; clarify. intro Habsurd.
          unfold meta_loc', meta_loc in *. clarify.
          contradiction H41. omega. }
       { clarify.  }
       { clarify. }
       { rewrite <- split_app. auto. }
      
    -(*unlock-nil*) symmetry in Hi. apply app_cons_not_nil in Hi. clarify.
    -(*unlock*) 
      exploit (instrument_incom (Unlock m)).
      {simpl. rewrite <- split_app. eauto. }
      clarify.
      do 4 eexists. split; [|split].
      +apply exec_unlock. eauto.
      +unfold mem_sim. intros. simpl.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
       inversion H1; clarify.
       split; clarify.
       {rewrite in_app. simpl. auto. }
       {left. rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        rewrite in_app in H0. simpl in H0. destruct H0 as [? | [? | [?|?]]]; clarify.
        -contradiction H3. eapply mops_set_vc_meta_cl; eauto.
        -contradiction H3. unfold meta_loc. left. simpl. omega.
        -contradiction H3. unfold meta_loc. left. simpl. omega.
       }
      +setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify.
       inversion H1; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        assert(Hcon:  consistent ((m0 ++ m1) ++ opt_to_list (Some (Rel t m)))).
       { eapply consistent_mem_vals with (m2:=(m0++m2)); eauto.
         { apply init_steps; clarify. }
         do 2 rewrite split_app in Hcon2. 
         rewrite loc_valid_ops_SC in Hcon2; clarify. 
         { rewrite Forall_forall; intros ? Hin; clarify.
           rewrite Forall_forall; intros ? Hin2; clarify.
           repeat rewrite in_app in Hin. destruct Hin as [[?|?]|?]; clarify; intro Heq.
           -contradiction H31. setoid_rewrite Heq. eapply mops_set_vc_meta_cl; eauto.
           -contradiction H31. setoid_rewrite Heq. unfold meta_loc. left. simpl. omega.
           -contradiction H31. setoid_rewrite Heq. unfold meta_loc. left. simpl. omega.
         }
         { repeat rewrite Forall_app; split; auto; repeat constructor; simpl; auto. }
         { repeat constructor; simpl; auto. }
         { constructor. }
       }
       split; clarify.
      (* setoid_rewrite Forall_app in Hlocs. inversion Hlocs; clarify.
       inversion Hlocs2 as [| ?? Hloci ?]. clarify. inversion Hloci; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.*)
       assert(Hs_rw':= Hs_rw). 
       assert(Hhb:  consistent ((m0++m2) ++ mops_set_vc (C' + t) (L' + m) zt t vs)).
       { rewrite app_assoc in Hcon2.
         eapply consistent_app_SC; eauto.  }
       exploit set_vc_vals; try apply Hhb; eauto.
       { intros; apply init_steps; clarify. }
       clarify; eexists; simpl; split. 
       * eapply ss_step; eauto.
         eapply release; eauto.
         apply ss_refl.
       * assert( v= vc t t) as Hv.
         { apply clock_match_value with (m:=(m0++m2) ++
            mops_set_vc (C' + t) (L' + m) zt t (map (vc t) (rev (interval 0 zt)))) (ct:=C'+t) (t:=t).
           -unfold clocks_sim in *; clarify.
            rewrite <- app_assoc.
            apply clock_match_nomod; clarify.
            +eapply consistent_app_SC. do 3 rewrite <- app_assoc. simpl. rewrite app_assoc.
             eauto.
            +rewrite Forall_app. split; clarify. rewrite Forall_forall. clarify.
            +rewrite Forall_app. split; clarify. rewrite Forall_forall. intros c Hin; clarify.
             apply in_mops_set_vc' in Hin. destruct c; clarify. destruct x; clarify. 
           -rewrite <- app_assoc. apply init_steps; clarify.
            rewrite Forall_app; clarify.
           -auto.  
         }
         assert(Hseq:[Read t (C' + t, t) v; Write t (C' + t, t) (v + 1); Rel t m]=
                     [Read t (C' + t, t) v; Write t (C' + t, t) (v + 1)]++[ Rel t m]) by clarify.
         setoid_rewrite Hseq. do 2 rewrite app_assoc.
         apply clocks_sim_nonmeta; clarify.
         { rewrite split_app.  eapply clocks_sim_writeC; clarify.
           -apply clocks_sim_allreads; clarify.
            +eapply clocks_sim_set_vc_CL with (s:=(vc, vl, vr, vw)); clarify.
             *auto.
             *auto.
            +eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
             rewrite <- app_assoc. eauto.
            +repeat constructor; clarify.
           -auto.
           -rewrite <- app_assoc. eapply consistent_app_SC; rewrite <- app_assoc.
            rewrite <- split_app. simpl. eauto. rewrite <- app_assoc. eauto.
           -auto.
           -unfold upd, vc_inc; clarify. apply functional_extensionality.
            intros. destruct (eq_dec t x); clarify. apply functional_extensionality.
            intros y. destruct (eq_dec y x); clarify. omega.
         }
         { do 2 rewrite <- app_assoc. simpl. auto. }
         { repeat constructor; clarify. }
         { repeat constructor; clarify. simpl. intro Habsurd.
           contradiction H31. unfold meta_loc', meta_loc in *; clarify.
           do 3 right. left. clarify. }
    -(*spawn-nil*) symmetry in Hi. apply app_cons_not_nil in Hi. clarify.
    -(*spawn*) 
     destruct i; destruct zt; clarify.
     +destruct x; clarify.
     +destruct x; clarify.
     +destruct zt; clarify.
     +destruct zt eqn:Hzt; clarify.
      apply plus_minus in H1. rewrite minus_plus in H1. clarify.
      rewrite <-Hzt in *; clarify.
      do 4 eexists. split; [|split].
      *apply exec_spawn; eauto.
       intro Hin. 
       apply Forall2_impl with (Q:= (fun t1 t2: tid * prog => fst t1 = fst t2)) in HPsim. 
       setoid_rewrite (map_fst HPsim) in Hin. clarify.
       intros. clarify.
      *unfold mem_sim. intros. simpl.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
       inversion H1; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
       split; clarify.
       rewrite in_app in H0. contradiction H7.
       inversion H0.
       { 
        apply (mops_max_vc_meta_cc vs1 vs2 zt _  H31 H3); eauto. 
       } 
       {
        inversion H; clarify; unfold meta_loc; left; simpl; omega.
       }
      *simpl. rewrite app_nil_r.
       split; clarify.
       setoid_rewrite Forall_app in Hlocs. inversion Hlocs; clarify.
       inversion Hlocs2 as [| ?? Hloci ?]. clarify. inversion Hloci; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.
       assert(Hs_rw':= Hs_rw). 
       assert(Hhb:  consistent ((m0++m2) ++ mops_max_vc (C' + t) (C' + u) vs1 vs2 t zt)).
       { rewrite app_assoc in Hcon2. eapply consistent_app_SC; eauto. }
       exploit max_vc_vals; try apply Hhb; eauto.
       { intros; apply init_steps; clarify. }
       { intros; apply init_steps; clarify. }
       clarify; eexists; simpl. split. 
       { eapply ss_step; eauto.
         eapply fork_step; eauto.
         apply ss_refl. }
       assert(u <> t) as Hut.
       {
         intro Heq. clarify. contradiction Hnew.
         rewrite map_app, in_app. clarify.
       }
       { (*clocks_sim*)
         unfold mops_inc_vc. rewrite split_app.
         eapply clocks_sim_writeC with (s:=(upd vc u (vc_join (vc u) (vc t)),vl,vr,vw)); eauto.
         -instantiate(1:=((m0 ++ m2) ++
           mops_max_vc (C' + t) (C' + u) (map (vc t) (rev (interval 0 zt)))
             (map (vc u) (rev (interval 0 zt))) t zt) ++ [Read t (C' + t, t) v]).
          apply clocks_sim_allreads; clarify.
          +eapply clocks_sim_max_vc_CC.
           *instantiate(1:= (vc,vl,vr,vw)). clarify.
           *eauto.
           *apply H2.
           *apply H21.
           *clarify.
           *simpl. eauto.
           *simpl. auto.
           *auto.
          +eapply consistent_app_SC; rewrite <- split_app; rewrite <- app_assoc; eauto.
          +repeat constructor; clarify.
         -rewrite <- split_app. auto.
         -unfold upd, vc_join, vc_inc. clarify.
          apply functional_extensionality. intro x. destruct (eq_dec t x); clarify.
          apply functional_extensionality. intro y. destruct (eq_dec y x); clarify.
          destruct (eq_dec x y); clarify.
         -assert( v= vc t t) as Hv.
         { apply clock_match_value with (m:=(m0++m2) ++
             mops_max_vc (C' + t) (C' + u) (map (vc t) (rev (interval 0 zt)))
             (map (vc u) (rev (interval 0 zt))) t zt) (ct:=C'+t) (t:=t).
           -unfold clocks_sim in *; clarify.
            rewrite <- app_assoc.
            apply clock_match_nomod; clarify.
            +eapply consistent_app_SC. do 3 rewrite <- app_assoc. simpl. rewrite app_assoc.
             eauto.
            +rewrite Forall_app. split; clarify. rewrite Forall_forall. clarify.
            +rewrite Forall_app. split; clarify. rewrite Forall_forall. intros c Hin; clarify.
             apply in_mops_max_vc' in Hin. destruct c; clarify. destruct x; clarify.
             omega.
           -rewrite <- app_assoc. apply init_steps; clarify.
            rewrite Forall_app; clarify.
           -auto.  
         }
         instantiate(1:=t). repeat rewrite <- app_assoc; clarify.
         assert(vc t t + 1 = S (vc t t +0)) as Hsvctt by omega.
         rewrite Hsvctt. auto.  }
    -(*wait*)
     exploit (instrument_incom (Wait u)).
     { simpl;  eauto. }
     clarify.
     assert(u < zt) as Huzt.
     {
       apply in_split in Hdone. inversion Hdone; clarify.
       setoid_rewrite H in HPsim. unfold state_sim in HPsim. 
       apply Forall2_app_inv_r in HPsim. inversion HPsim. clarify.
       inversion H021; clarify.
       destruct x7. clarify. rewrite H022 in Ht.
       setoid_rewrite Forall_app in Ht; clarify. inversion Ht2; clarify.
     }
     assert (t < zt) as Htzt.
     {
       setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
       inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.
     }
     assert (u <> t) as Hut.
     {
       intros Heq.
       rewrite in_app in Hdone. destruct Hdone as [Huin | [Huin |Huin]]; clarify;
       unfold distinct in *;  apply in_split in Huin; inversion Huin; clarify.
       -do 2 rewrite map_app in Hdistinct; clarify; apply NoDup_remove_2 in Hdistinct;
        contradiction Hdistinct;
        rewrite in_app. left. rewrite in_app. right. clarify.
       -rewrite map_app in Hdistinct. clarify. rewrite map_app in Hdistinct. clarify.
        apply NoDup_remove_2 in Hdistinct. contradiction Hdistinct.
        rewrite in_app. right. rewrite in_app. clarify.
     }
     do 4 eexists. split;[|split].
     +apply exec_wait. eauto. auto. Print state_sim. 
      apply in_split in Hdone. inversion Hdone; clarify.
      setoid_rewrite H in HPsim. unfold state_sim in HPsim. 
      apply Forall2_app_inv_r in HPsim. inversion HPsim. clarify.
      inversion H021; clarify.
      destruct x7. clarify. inversion H021. clarify.
      apply Forall2_cons_inv in H021. inversion H021; clarify.
      destruct p; clarify.
      *rewrite H022. rewrite in_app_iff. clarify. 
      *exploit instrument_nonnil.
       { instantiate(1:=t0). instantiate(1:=i).
         symmetry in H32. apply app_eq_nil in H32. inversion H32. clarify.  }
       intros. clarify.
     +unfold mem_sim. intros. simpl. 
      split; clarify.
      { contradiction H2. apply in_app in H1. inversion H1; clarify.
        -eapply (mops_max_vc_meta_cc _ _ _ _ Huzt Htzt) ; eauto.
        -destruct H; unfold meta_loc; clarify; left; omega. }
     +simpl. rewrite app_nil_r. split; clarify.
      exploit max_vc_vals.
      { instantiate(1:=C'+u). intros. instantiate(1:=(m0++m2)). apply init_steps; clarify. }
      { instantiate(1:=C'+t). intros. apply init_steps; clarify. }
      { eapply consistent_app_SC; rewrite <- app_assoc. eauto. }
      { auto. }
      { auto. }
      { instantiate (1:=vc u). apply Hs_c; auto. }
      { instantiate (1:=vc t). apply Hs_c; auto. }
      clarify; eexists; simpl; split. 
      *eapply ss_step; eauto.
       eapply join_step; eauto.
       apply ss_refl.
      *unfold mops_inc_vc' in *. 
       rewrite split_app.
       eapply clocks_sim_writeC with(s:=((upd vc t (vc_join (vc t) (vc u))),vl,vr,vw)).
       { instantiate(1:= ((m0 ++ m2) ++
             mops_max_vc (C' + u) (C' + t) (map (vc u) (rev (interval 0 zt)))
               (map (vc t) (rev (interval 0 zt))) t zt ++
             [Read t (C' + u, u) v])).
         rewrite app_assoc. eapply clocks_sim_allreads; clarify.
         - eapply clocks_sim_max_vc_CC with (s:=(vc,vl,vr,vw)).
           + auto.
           + eauto.
           + apply Huzt.
           + apply Htzt.
           + auto.
           + clarify.
           + clarify.
           + eapply consistent_app_SC. rewrite <- app_assoc. eauto.
         - eapply consistent_app_SC. rewrite <- app_assoc. simpl. eauto.
           rewrite <- app_assoc. eauto.
         - repeat constructor; clarify.
       }
       { apply Huzt. }
       { rewrite <- split_app.  auto. }
       { apply Huzt. }
       { eauto. }
       { unfold upd, vc_join, vc_inc; clarify.
         apply functional_extensionality; clarify.
         apply functional_extensionality; clarify.
         destruct (eq_dec x0 x); clarify. }
       repeat rewrite <- app_assoc; simpl; destruct (eq_dec u u); clarify.
         assert(Hv: v= vc u u).
         { eapply clock_match_value with (m:=(m0++m2)++mops_max_vc (C' + u) (C' + t) (map (vc u) (rev (interval 0 zt)))
               (map (vc t) (rev (interval 0 zt))) t zt); clarify.
           -instantiate(1:=C'+u). instantiate(1:= t).
            rewrite <- app_assoc.
            apply clock_match_nomod; clarify.
            + eapply consistent_app_SC. rewrite <- app_assoc; simpl; eauto.
              rewrite <- split_app. eauto.
            + rewrite Forall_app; clarify.
              repeat constructor; clarify.
            + rewrite Forall_app; clarify.
              rewrite Forall_forall; intros c Hin. apply in_mops_max_vc'  in Hin.
              destruct c; clarify.
              destruct x; clarify. intro Haburd.
              contradiction Hut. apply plus_reg_l in Haburd.  auto.
           -rewrite <- app_assoc; apply init_steps; clarify.
            rewrite Forall_app; clarify.
         }
         rewrite Hv. instantiate(1:=t).
         assert(S (vc u u + 0) = vc u u +1) as Hvcu by omega.
         rewrite Hvcu. auto.       
   -(*assert_le*)
     exploit (instrument_incom (Assert_le e1 e2)).
     { simpl;  eauto. }
     clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_assert_pass with (e1:=e1) (e2:=e2). eauto.
      rewrite eval_sim with (G2:=G2' t);  try rewrite eval_sim with (G1:=G1 t) (G2:=G2' t);
      auto;  intros; apply HGsim; intro Heq; clarify;unfold fresh_tmps in Hfresh; rewrite Forall_app in Hfresh;
      inversion Hfresh; clarify; inversion Hfresh2; clarify; inversion H2; clarify.
     +unfold mem_sim. intros. clarify. split; clarify.
     +simpl. rewrite app_nil_r. auto.
     +exists (vc, vl, vr, vw). simpl. split; clarify.
      *apply ss_refl.
      *rewrite app_nil_r. unfold clocks_sim; clarify.
    -inversion Hemc; clarify.
     clarify; do 5 eexists; [eauto|];
     exploit sim_step; eauto; clarify.
     eexists. split; eauto. 
Qed. 


 

Corollary instrument_sim_safe2' : forall  P1 P2 G1 G2 
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : legal_tids P1) (Hdistinct: distinct P2)
  
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m0 
  (Hinit : forall p, initialized m0 p)
  lo2 lc2 P2' G2' (Hstep : iexec_star P2 G2 lo2 lc2 P2' G2') m1 m2
  (Hmem_vals: mem_vals (m0++m1) (m0++m2)) (Hcon1: consistent (m0++m1))
  (Hcon2 : consistent ((m0++m2) ++ lc2)) s (Hs : clocks_sim (m0++m2) s)
  (Hprog_m1: Forall prog_op m1) (Hprog_m2: Forall prog_op m2)                                 ,
  exists lo lc P1' G1', exec_star (Some P1) G1 lo lc (Some P1') G1' /\
    state_sim P1' P2' /\ env_sim G1' G2' /\ consistent ((m0++m1) ++ lc) /\
    mem_vals ((m0++m1)++lc) ((m0++m2)++lc2) /\
        exists s', step_star s lo s' /\
                   clocks_sim ((m0++m2) ++ lc2) s'.
Proof.
  
  intros.
  generalize dependent m1. generalize dependent m2. generalize dependent P1. generalize dependent G1.
  generalize dependent s.
  induction Hstep; clarify.
  -exists [],[],P1,G1.
   split;[|split;[|split;[|split;[|split]]]]; auto.
   +apply exec_refl.
   +rewrite app_nil_r. auto.
   +do 2 rewrite app_nil_r. auto.
   +exists s. split. apply ss_refl. rewrite app_nil_r. auto. 
  -rename P into P2, P' into P2', P'' into P2'', G' into G2', G'' into G2''.
   rename c into c2, o into o2, lo into lo2, lc into lc2.
    exploit instrument_sim_safe2.
   { apply Hfresh. }
   { apply Hlocs. }
   { apply Ht. }
   { apply Hdistinct. }
   { apply HPsim. }
   { apply HGsim. }
   { clarify.  }
   { apply Hexec. }
   { eauto. }
   { apply Hprog_m2. }
   { apply Hmem_vals. }
   { apply Hcon1. }
   { eapply consistent_app_SC; rewrite <- app_assoc. eauto. }
   { apply Hs. }
   intros (o1 & c1 & P1' & G1' & Hexec_P1 & Hstate_sim_P1'_P2' & Henv_sim_G1'_G2' &
           Hcon_m_c0 & Hmem_sim_c0_c & (s' & Hss' & Hclock_sim_s')).
   assert(distinct P2') as HdP2'.
   { eapply distinct_steps; eauto.
     eapply iexec_exec; eauto. }
   assert(consistent (((m0++m2) ++ c2)++ lc2)) as Hcon_mlc2.
   { rewrite <-app_assoc. auto. }
   assert( forall p : ptr, meta_loc p -> initialized ((m0++m2)++c2) p) as Hinit_P2'.
   { clarify. rewrite <- app_assoc. apply init_steps; auto.
     apply iexec_exec in Hexec; auto. rewrite Forall_app. split; auto.
     apply prog_steps in Hexec; auto. }
   assert(fresh_tmps P1') as Hfresh_P1'.
   { apply fresh_tmps_step in Hexec_P1; clarify. }
   assert(safe_locs P1') as Hsafe_P1'.
   { apply safe_locs_step in Hexec_P1; auto. }
   assert(legal_tids P1') as Ht_P1'.
   { eapply legal_tids_steps with (P':=P1') in Ht; clarify.
     eapply exec_step; eauto. eapply exec_refl. }
   specialize(IHHstep HdP2' s' G1' Henv_sim_G1'_G2' P1' Hfresh_P1' Hsafe_P1' Ht_P1').
   assert(Hcon_mlc2': consistent ((m0 ++ m2++c2) ++ lc2)).
   { do 2 rewrite <-app_assoc. rewrite <- app_assoc in Hcon2. auto. }
   rewrite <- app_assoc in Hclock_sim_s'.
   assert(Hprog_m1c1: Forall prog_op (m1++opt_to_list c1)).
   { rewrite Forall_app; clarify. eapply prog_step; eauto. }
   assert(Hprog_m2c2: Forall prog_op (m2++c2)).
   { rewrite Forall_app. split; auto. eapply prog_steps. eapply iexec_exec; eauto. }
    assert(Hmem_vals_m1c1m2c2: mem_vals (m0 ++ m1 ++ opt_to_list c1) (m0 ++ m2 ++ c2)).
   { do 2 rewrite app_assoc. apply mem_vals_sim_app; auto. eapply prog_steps; eauto.
     instantiate(1:=G1'). instantiate(1:=(Some P1')). instantiate(1:= opt_to_list o1).
     assert(opt_to_list o1=opt_to_list o1 ++[]) as Hnilr1.
     { rewrite app_nil_r; auto. }
     assert(opt_to_list c1=opt_to_list c1 ++[]) as Hnilr2.
     { rewrite app_nil_r; auto. }
     rewrite Hnilr1,Hnilr2. eapply exec_step; eauto. constructor.
   }
   rewrite <- app_assoc in Hcon_m_c0. 
   specialize(IHHstep Hstate_sim_P1'_P2' (m2++c2) Hcon_mlc2' Hclock_sim_s' Hprog_m2c2).
   specialize(IHHstep (m1++opt_to_list c1) Hmem_vals_m1c1m2c2 Hcon_m_c0 Hprog_m1c1).
   inversion IHHstep as (lo1 & lc1 & P1''&G1''& Hexec_star_P1'_P1''&Hstate_sime_P1''_P2''
                             & Henv_sim_G1''_G2'' & Hcon_mc2_lc1 & Hmem_vals_lc1_lc2
                             & (s'' & Hs'_s'' & Hclocks_sim_s'')).
   exists (opt_to_list o1++lo1), (opt_to_list c1 ++ lc1), P1'', G1''.
   split;[|split;[|split;[|split;[|split]]]]; auto.
   +eapply exec_step. apply Hexec_P1. auto.
   +rewrite <- app_assoc. do 2 rewrite <- app_assoc in Hcon_mc2_lc1. auto.
   +do 2 rewrite <- app_assoc. do 4 rewrite <- app_assoc in Hmem_vals_lc1_lc2. auto.
   +exists s''. split.
    * apply ss_trans with (s':=s'); auto.
    *rewrite <- app_assoc. do 2 rewrite <- app_assoc in Hclocks_sim_s''. auto.
Qed.


Lemma state_sim_final : forall P1 P2
  (Hstate_sim : state_sim P1 P2), 
  final_state (Some P2)<->final_state (Some P1).
Proof.
  split.
  -intro Hfinal_P2.
   induction Hstate_sim; clarify.
   inversion Hfinal_P2. clarify.
   apply Forall_cons; clarify.
   setoid_rewrite H3 in H2. 
   destruct x; clarify.
   destruct p; clarify.
   symmetry in H2.
   apply app_eq_nil in H2. destruct H2 as [Hinstrument_nil ??].
   exploit instrument_nonnil; clarify.
   eapply Hinstrument_nil.
  -intro Hfinal_P2.
   induction Hstate_sim; clarify.
   inversion Hfinal_P2. clarify.
   apply Forall_cons; clarify.
   setoid_rewrite H3 in H2. 
   destruct x; clarify.
Qed.

   
Lemma instrument_sim_safe : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1) (Hdistinct : distinct P2)
  (Ht : Forall (fun e => fst e < zt) P1) 
  (Ht_spawn: Forall (fun p =>  match p with
                                 | (t0,Spawn u li::rest) => u <> t0
                                 | (t0,Wait u ::rest) => u <> t0
                                 | _ => True
                               end) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m0 (Hinit: forall p: ptr, initialized m0 p)
  m1 (Hroot : exec_star (Some (init_state P)) init_env h m1 (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 t o c (Some P1') G1')
  (Hcon : consistent ((m0 ++m1)++ opt_to_list c))
  (Hprog_m1: Forall prog_op m1) m2 (Hprog_m2: Forall prog_op m2)
   (Hcon2: consistent (m0++m2)) (Hmem_vals: mem_vals (m0++m1) (m0++m2))
  s (Hs : clocks_sim (m0++m2) s) s' (Hsafe : step_star s (opt_to_list o) s'),
  exists lo lc P2' G2', exec_star (Some P2) G2 lo lc (Some P2') G2' /\
    consistent ( (m0++m2) ++ lc) /\ state_sim P1' P2' /\ env_sim G1' G2' /\
    mem_sim c lc /\ clocks_sim (m0++m2++lc) s'.
Proof.
  
  intros.
  inversion Hs as [ Hs_c (Hs_l,Hs_rw)]; clarify.
  assert (exists lo lc P2' G2', iexec P2 G2 t lo lc P2' G2' /\
    consistent ((m0 ++ m2) ++ lc) /\ mem_sim c lc /\ clocks_sim ((m0++m2)++lc) s').
  inversion Hstep; clarify; exploit Forall2_app_inv_l; eauto 2;
  intros (P0' & P3' & HP0 & Hrest & ?);
  inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - do 5 eexists; [|split;[|split]].
    + apply iexec_assign; eauto.
    + rewrite app_nil_r. auto.
    + unfold mem_sim; split; clarify.
    + inversion Hsafe.
      rewrite app_nil_r; clarify.
  -(*load*) 
   destruct x as (x, o).
    inversion Hsafe; clarify.
    inversion Hstep0; clarify.
    rewrite <- app_assoc; simpl; do 5 eexists.
    + apply iexec_load; eauto.
      * clarify.
      * instantiate (1 := map (W x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length; omega.
      * instantiate (1 := map (C t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length; omega.
      * apply vc_le_first_gt; auto.
    + instantiate (1 := v).
      instantiate (1 := C t0 t0).
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi as [|?? Hx ?]; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      rewrite app_comm_cons.
      rewrite split_app.
      simpl.
      rewrite app_comm_cons. rewrite app_comm_cons. 
      do 2 rewrite app_assoc. 
      rewrite <- (app_assoc _ [Read t0 (C'+t0, t0) (C t0 t0)]). 
      exploit acq_con.
      {instantiate (1:=m0++m2). auto. }
      {instantiate (1:=x).  auto. }
      instantiate (1:= t0). intro Hacq_con.
      assert(Hs_acq: clocks_sim ((m0++m2) ++ [Acq t0 (X+x)]) (C,L,R,W)).
      { apply clocks_sim_acq; auto. }
      
      assert(Hcon0: consistent ((m0++m2) ++
                                         Acq t0 (X + x)
                                         :: mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
                                         (map (C t0) (rev (interval 0 zt))) zt t0)).
      { rewrite split_app.
        apply (mops_hb_check_con Hs_acq); auto. }
      specialize(Hs_rw x Hx2). inversion Hs_rw as [Hs_rw1 Hs_rw2].
      unfold clock_match in Hs_rw1, Hs_rw2. specialize(Hs_rw1 t0). specialize(Hs_rw2 t0).

      assert(Hcon1:  consistent (((m0++m2) ++
         Acq t0 (X' + x)
         :: mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
              (map (C t0) (rev (interval 0 zt))) zt t0) ++[Write t0 (R'+x, t0) (C t0 t0)])).
      { apply can_write_thread. apply can_write_SC;auto. clarify.
        clear; constructor; clarify. }
      assert(Hcon_m02lc:   consistent ((m0 ++ m2) ++
      Acq t0 (X' + x)
      :: mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
           (map (C t0) (rev (interval 0 zt))) zt t0 ++
         mops_move (C' + t0, t0) (R' + x, t0) t0 (C t0 t0) ++
         [Read t0 (x, o) v; Rel t0 (X' + x)])).
      { rewrite split_app. unfold mops_move. 
        rewrite reads_noops_SC.
        -rewrite loc_valid_ops_SC; auto.
         +split.
          *rewrite read_noop_SC.
           { apply can_write_thread. apply can_write_SC; auto; clarify.
             clear; constructor; clarify. }
           { unfold clocks_sim in Hs_acq;
             destruct Hs_acq as (Hs_acq_c & Hs_acq_l & Hs_acq_rw).
             specialize(Hs_acq_c t0 H3 t0). clarify.
             apply can_read_thread. auto. }
          *rewrite read_noop_SC.
           { apply can_release_SC; auto.
             apply init_can_write. apply init_steps;auto.     
           }
           { rewrite <- app_assoc.
             rewrite loc_valid_ops1_SC; clarify.
             -apply can_read_thread. 
              apply can_read_thread' with (t:=t0).
              apply consistent_mem_vals' with (m1:=(m0++m1)); auto.
              { eapply init_steps; eauto. }
              { eapply init_steps; eauto. }
              { clarify. }
             - constructor; clarify.
               intro Heq.  contradiction Hx1. setoid_rewrite <- Heq. 
               unfold meta_loc; simpl. repeat right. omega.
             -constructor; clarify.
           }
         +repeat constructor; clarify; intro Heq; try solve [ contradiction Hx1; setoid_rewrite Heq;
          unfold meta_loc; simpl; omega].
          *inversion Heq. specialize(Hmetalocs_disjoint_CX l Hx2).  clarify.
          *inversion Heq. specialize(Hmetalocs_disjoint_RX Hx2 Hx2). clarify.
         +repeat constructor; clarify.
         +repeat constructor; clarify.
        -rewrite <- app_assoc. simpl. auto.
        -rewrite Forall_forall. intros c Hcin. apply in_mops_hb_check in Hcin.
         destruct c; clarify.
    }
    split;[|split].
    *unfold mops_move  in Hcon_m02lc. simpl in *. rewrite <- app_assoc. auto. 
    *(*mem_sim*)
     unfold mem_sim in *. split; clarify; repeat rewrite in_app in *; clarify.
     destruct H2 as [?| [ [Hcin| [? | ?]] | [? | [? | [? | ?]]]]]; clarify;
     try solve [contradiction H5; unfold meta_loc; simpl; omega].
     contradiction H5.  
     eapply mops_hb_check_meta; eauto.
    *(*clocks_sim*)inversion Hsteps. destruct s'; clarify.
     assert([Read t0 (C' + t0, t0) (C t0 t0); Write t0 (R' + x, t0) (C t0 t0);
         Read t0 (x, o) v; Rel t0 (X' + x)] = ([Read t0 (C' + t0, t0) (C t0 t0)]++ [Write t0 (R' + x, t0) (C t0 t0)])++[Read t0 (x, o) v; Rel t0 (X' + x)]) as Hsilly by clarify.
     setoid_rewrite Hsilly. do 2 rewrite app_assoc.
     apply clocks_sim_nonmeta; clarify.
     { Check clocks_sim_writeR. eapply clocks_sim_writeR with (s:=(C,L,R,v0)) .
       -instantiate(1:=(((m0 ++ m2) ++
      Acq t0 (X' + x)
      :: mops_hb_check (W' + x) (C' + t0) (map (v0 x) (rev (interval 0 zt)))
           (map (C t0) (rev (interval 0 zt))) zt t0) ++
                                                     [Read t0 (C' + t0, t0) (C t0 t0)])).
        rewrite <- app_assoc. rewrite <- app_comm_cons. rewrite split_app.
        apply clocks_sim_allreads; auto.
        +rewrite <- app_assoc. simpl. eapply consistent_app_SC; eauto.
         rewrite <- app_assoc. rewrite <- app_comm_cons. do  2 rewrite <- app_assoc.
         rewrite app_assoc. instantiate (1:=[Write t0 (R' + x, t0) (C t0 t0); 
                                              Read t0 (x, o) v; Rel t0 (X' + x)]).
         clarify.
        +rewrite Forall_forall. intros c Hcin. rewrite in_app in Hcin.
         destruct Hcin as [Hcin | Hc]; clarify.
         apply in_mops_hb_check in Hcin. destruct c; clarify.
        +rewrite Forall_forall. intros c Hcin. rewrite in_app in Hcin.
         destruct Hcin as [Hcin | Hc]; clarify.
         apply in_mops_hb_check in Hcin. destruct c; clarify.
       -apply l.
       -eapply consistent_app_SC.
        do 3 rewrite <- app_assoc. simpl. eauto.
       -apply Hx2.
       -eauto.
       -eauto.
       -auto.
     }
     { do 3 rewrite <- app_assoc. simpl. auto. }
     { repeat constructor; clarify. }
     { repeat constructor; clarify.
       -intro Habsurd. contradiction Hx1. unfold meta_loc' in Habsurd. unfold meta_loc.
        clarify. omega.
       -apply notmeta_loc'_X; auto. } 
  -destruct x as (x,o). (* store *)
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   exploit store_tmps_fresh.
   { eauto. }
   intro Hfresh_tmps.
   rewrite <- app_assoc; clarify; do 5 eexists.
   + apply iexec_store; eauto.  (*exec_star*)
     clarify; eauto.
    { instantiate (1 := map (W x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { instantiate (1 := map (C t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { instantiate (1 := map (R x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { apply vc_le_first_gt; auto. }
    { apply vc_le_first_gt; auto. }
   +instantiate (1 := C t0 t0). (*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi as [|?? Hx ?]; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2. clarify.
    assert( forall (X:Type) (a b c d:X), [a;b;c;d]=[a]++[b;c;d]) as Hlist_silly.
    intros. auto.
    assert ( consistent ((m0++m2)++[Acq t0 (X + x)])) as Hcan_acq.
    { apply can_arw_SC; specialize(Hs_x (m0++m2) Hx2);
      inversion Hx2; clarify. }
    assert(Hs_acq: clocks_sim ((m0++m2) ++ [Acq t0 (X+x)]) (C,L,R,W)).
    { apply clocks_sim_acq; auto. }
    assert ( consistent (((m0++m2) ++ [Acq t0 (X + x)]) ++
             mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
             (map (C t0) (rev (interval 0 zt))) zt t0)) as Hcon_checkW.
    { apply (mops_hb_check_con Hs_acq); auto. }
    assert (consistent (((m0++m2)++ [Acq t0 (X+x)])++
            mops_hb_check (R' + x) (C' + t0) (map (R x) (rev (interval 0 zt)))
            (map (C t0) (rev (interval 0 zt))) zt t0)) as Hcon_checkR.
    { apply (mops_hb_check_conR Hs_acq); auto. }
    assert (consistent (((m0++m2)++ [Acq t0 (X+x)])++
           mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
           (map (C t0) (rev (interval 0 zt))) zt t0 ++
           mops_hb_check (R' + x) (C' + t0) (map (R x) (rev (interval 0 zt)))
           (map (C t0) (rev (interval 0 zt))) zt t0)) as Hcon_checks.
    { setoid_rewrite reads_noops_SC; auto.
      apply mops_hb_check_read. }
    assert(forall (X:Type) (a b c :X), [a;b;c]=[a;b]++[c]) as Hlist_silly2.
    { simpl. auto. }
    assert (forall (X:Type) (l1 l2 l3 l4 l5:list X), l1++l2++l3++l4++l5=l1++(l2++l3++l4)++l5) as Hlist_silly3.
    { intros. repeat rewrite app_assoc. auto. }
    assert(Hcon_m02lc:    consistent ((m0 ++ m2) ++
           Acq t0 (X' + x)
           :: mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
           (map (C t0) (rev (interval 0 zt))) zt t0 ++
           mops_hb_check (R' + x) (C' + t0) (map (R x) (rev (interval 0 zt)))
           (map (C t0) (rev (interval 0 zt))) zt t0 ++
           [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (W' + x, t0) (C t0 t0);
            Write t0 (x, o) (eval (G2 t0) e); Rel t0 (X' + x)])).
    { rewrite app_assoc. 
      setoid_rewrite Hlist_silly. rewrite split_app. rewrite app_assoc.
      setoid_rewrite reads_noops_SC.
      *setoid_rewrite Hlist_silly2.
       apply loc_valid_ops1_SC.
       { rewrite Forall_forall. intros x0 Hx0. inversion Hx0; clarify. intro Heq.
         specialize(Hmetalocs_disjoint t0 x x x x). inversion Hmetalocs_disjoint;clarify. simpl. intro Heq. contradiction Hx1. setoid_rewrite Heq.
         unfold meta_loc. simpl. repeat right. omega. }
       { clarify. }
       { repeat constructor; clarify. }
       { split; clarify.
         -rewrite split_app. repeat rewrite <- app_assoc. do 2 rewrite app_assoc. 
          setoid_rewrite Hlist_silly3.
          apply loc_valid_ops_SC.
          +rewrite Forall_forall. intros. rewrite Forall_forall.
           intros x1 Hx1_in. inversion Hx1_in. 
           clarify;repeat rewrite in_app in H;
           destruct H as [?|[?|?]]; clarify; intro Heq.
           *contradiction Hx1. setoid_rewrite Heq. eapply mops_hb_check_meta; eauto.
           *contradiction Hx1. setoid_rewrite Heq. eapply mops_hb_check_meta; eauto.
           *contradiction Hx1. setoid_rewrite Heq. unfold meta_loc; simpl. right. right. right. left. omega.
           *inversion H2; clarify.
          + repeat rewrite Forall_app; repeat split; auto.
            constructor; clarify.
          + constructor; clarify.
          +split.
           *{ (*checks& updates to VC's are consistent*)
               repeat rewrite app_assoc.
               apply can_write_thread. apply can_write_SC; auto.
               -apply can_write_SC; auto.
                +apply can_write_SC; auto.
                 specialize(Hs_rw x Hx2). inversion Hs_rw; clarify. 
                 unfold clock_match in Hs_rw2. specialize(Hs_rw2 t0). clarify. 
                 constructor; clarify.
               -rewrite <- app_assoc. eauto. }
           *{ (*can release after acquire*)
               apply can_write_thread.
               apply can_write_SC; auto.
               eapply write_any_SC. eauto.
               apply init_can_write. apply init_steps; auto.
               constructor; simpl; auto. }  
         -rewrite <- app_assoc. apply loc_valid_ops1_SC.
          +rewrite Forall_forall.  intros x0 Hx0. rewrite in_app in Hx0. clarify.
           intro Heq. symmetry in Heq. destruct Hx0; clarify;
           specialize(Hmetalocs_disjoint t0 x x x x).
           inversion Hmetalocs_disjoint; clarify. auto.
           apply in_mops_hb_check in H; destruct x0; clarify; inversion H; clarify. 
           apply in_mops_hb_check in H.  destruct x0; clarify; inversion H; clarify.
          +simpl; auto.
          +rewrite Forall_app; auto.
          +split; clarify.
           apply can_release_SC. auto.
           specialize(Hs_x (m0++m2) Hx2). inversion Hs_x; clarify. }
      *apply can_read_thread. apply can_read_SC.
       { apply can_read_SC.
        - specialize(Hs_c t0 H3).
          unfold clock_match in Hs_c. 
          specialize(Hs_c t0). clarify.
        -apply can_arw_SC; specialize(Hs_x (m0++m2) Hx2);
          inversion Hx2; clarify.
        -constructor; simpl; auto.
        -rewrite Forall_forall; intros; clarify.
         specialize(Hmetalocs_disjoint t0 x x x x ). inversion Hmetalocs_disjoint; clarify.
         intro Heq. inversion Heq. clarify. }
       { auto. }
       { rewrite Forall_app; auto. }
       { rewrite Forall_app. split; rewrite Forall_forall; intros; destruct x0; clarify;
         apply in_mops_hb_check in H; clarify. }
      *rewrite Forall_forall; intros. destruct x0; clarify.
    }
    split;[|split]; clarify.
    * erewrite eval_sim; [|intros; apply HGsim; intro; clarify].
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      { do 5 right;left. auto. }
      { left.
        destruct H2 as [? | [? | [? | [?|[?|[?|?]]]]]]; clarify;simpl;contradiction H5.
        -unfold meta_loc; clarify. repeat right. omega.
        -eapply mops_hb_check_meta; eauto. 
        -eapply mops_hb_check_meta; eauto. 
        -unfold meta_loc; clarify.  omega.        
        -unfold meta_loc; clarify. omega.
        -unfold meta_loc; clarify. omega. } 
    * (*clocks_sim*)inversion Hsteps. destruct s'; clarify.
     assert([Read t0 (C' + t0, t0) (C t0 t0); Write t0 (W' + x, t0) (C t0 t0);
             Write t0 (x, o) (eval (G2 t0) e); Rel t0 (X' + x)] =
            [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (W' + x, t0) (C t0 t0)]++
         [Write t0 (x, o) (eval (G2 t0) e); Rel t0 (X' + x)]) as Hsilly by clarify.
     rewrite split_app.
     setoid_rewrite Hsilly. do 3 rewrite app_assoc.
     apply clocks_sim_nonmeta; clarify.
     { eapply clocks_sim_writeW with (s:=(C,L,R,W)) .
       -instantiate(1:= ((m0 ++ m2) ++ [Acq t0 (X' + x)]) ++
                   mops_hb_check (W' + x) (C' + t0)
                     (map (W x) (rev (interval 0 zt)))
                     (map (C t0) (rev (interval 0 zt))) zt t0 ++
                   mops_hb_check (R' + x) (C' + t0)
                     (map (R x) (rev (interval 0 zt)))
                     (map (C t0) (rev (interval 0 zt))) zt t0++
                     [Read t0 (C' + t0, t0) (C t0 t0)]).
        apply clocks_sim_allreads; auto.
        +eapply consistent_app_SC; eauto.
         rewrite <- app_assoc. rewrite <- split_app.
         do 3 rewrite <- app_assoc. simpl. rewrite app_assoc.
         apply Hcon_m02lc.
        +rewrite Forall_app. split;[ | rewrite Forall_app; split]; auto.
         constructor; clarify.
        +rewrite Forall_app; split;[ | rewrite Forall_app; split];
         try apply mops_hb_check_read; clarify. 
       -apply H3.
       -eapply consistent_app_SC.
        do 3 rewrite <- app_assoc. simpl. rewrite <- split_app. eauto.
       -apply Hx2.
       -eauto.
       -eauto.
       -repeat rewrite <- app_assoc. clarify.
     }
     { do 3 rewrite <- app_assoc. simpl. rewrite <- split_app. auto. }
     { repeat constructor; clarify. }
     { repeat constructor; clarify.
       -intro Habsurd. contradiction Hx1. unfold meta_loc' in Habsurd. unfold meta_loc.
        clarify. omega.
       -apply notmeta_loc'_X; auto. } 
  -(*lock*) 
  inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   do 5 eexists.
   + apply iexec_lock; eauto.
     { instantiate(1 := map (L m) (rev (interval 0 zt))). 
       rewrite map_length, rev_length, interval_length; omega. }
     { instantiate(1:= map (C t0) (rev (interval 0 zt))).
       rewrite map_length, rev_length, interval_length.
       omega.  }
     { rewrite Forall_app in Ht. clarify. inversion Ht2; clarify. }
   +(*consistent*)
     setoid_rewrite Forall_app in Hlocs; clarify.
     inversion Hlocs2 as [|?? Hi ?]; clarify.
     inversion Hi as [|?? Hm ?]; clarify.
     rewrite Forall_app in Ht; clarify.
     inversion Ht2; clarify.
     assert( Hcon_m02lc: consistent ((m0 ++ m2) ++
                                                Acq t0 m :: mops_max_vc (L' + m) (C' + t0) (map (L m) (rev (interval 0 zt)))
                                                (map (C t0) (rev (interval 0 zt))) t0 zt)).
     { rewrite loc_valid_ops2_SC; clarify.
       -split.
        +eapply (mops_max_vc_con_lc Hs); eauto.
        +apply consistent_mem_vals' with (m1:=m0++m1); clarify;
         apply init_steps; clarify.
       -rewrite Forall_forall. intros c Hcin. apply in_mops_max_vc' in Hcin.
        intro Habsurd. destruct c; inversion Habsurd; clarify;
                       contradiction Hm1; [destruct Hcin as [Hm|Hm]; rewrite Hm|];
                       unfold meta_loc; simpl; omega.
     }
     split;[|split]; clarify.
     *(*mem_sim*)
       simpl.
       unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
       contradiction H5.
       eapply mops_max_vc_meta; eauto.
     *(*clocks_sim*)
       inversion Hsteps; clarify.
       rewrite split_app.
       eapply clocks_sim_max_vc_LC; eauto.
       { apply clocks_sim_nonmeta; eauto.
         -apply consistent_mem_vals' with (m1:=m0++m1); clarify; apply init_steps; clarify.
         -constructor; clarify.
         -constructor; clarify. intro Habsurd.
          contradiction Hm1.  unfold meta_loc' in Habsurd.
          destruct Habsurd as [? |[?|[?|?]]]; unfold meta_loc; clarify; omega. }
       { simpl. auto. }
       { simpl. auto. }
       { rewrite <- split_app.  auto. }
 -(*unlock*) 
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   do 5 eexists.
   +(*iexec*)
    apply iexec_unlock; eauto.
    { rewrite <- split_app. eauto. }
    { instantiate(1:= map (C t0) (rev (interval 0 zt))). 
      rewrite map_length, rev_length, interval_length; omega. }
   +(*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi ; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    instantiate (1:=(C t0 t0)).
    unfold mops_inc_vc. clarify.
    assert((m0++m2) ++ mops_set_vc (C' + t0) (L' + m) zt t0
             (map (C t0) (rev (interval 0 zt))) ++
             [Read t0 (C' + t0, t0) (C t0 t0);
               Write t0 (C' + t0, t0) (C t0 t0 + 1); Rel t0 m] =
           (m0++m2) ++ (mops_set_vc (C' + t0) (L' + m) zt t0
             (map (C t0) (rev (interval 0 zt))) ++
             [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (C' + t0, t0) (C t0 t0 + 1)])++
             [Rel t0 m]) as Hsilly.
    { rewrite <-app_assoc. clarsimp. }
    assert(Hcon_m02lc:   consistent ((m0 ++ m2) ++
      mops_set_vc (C' + t0) (L' + m) zt t0 (map (C t0) (rev (interval 0 zt))) ++
      [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (C' + t0, t0) (C t0 t0 + 1);Rel t0 m]) ).
    { setoid_rewrite Hsilly.
      rewrite loc_valid_ops_SC.
      -split; auto.
       rewrite split_app. rewrite app_assoc.
       apply can_write_thread.
       specialize(Hs_c t0 H2). unfold clock_match in Hs_c. 
       specialize(Hs_c t0).
       apply can_write_SC;clarify.
       rewrite app_assoc. apply can_read_thread. 
       apply can_read_SC; auto.
       + simpl. apply (mops_set_vc_con_cl Hs); eauto.
       + rewrite Forall_forall. intros x Hin. apply in_mops_set_vc in Hin.
         destruct x; clarify. apply Hmetalocs_disjoint_CL; auto.
       +rewrite Forall_app; split; auto; constructor; simpl; auto. 
       +apply consistent_mem_vals' with (m1:=m0++m1); clarify; apply init_steps; clarify. 
      -rewrite Forall_app; split; rewrite Forall_forall; clarify;
       rewrite Forall_forall; clarify.
       +apply mops_set_vc_meta_cl in H; auto.
        intro Heq. rewrite <- Heq in H. clarify. 
       +destruct H as [Hx | Hx]; clarify; intro Heq; contradiction H21;
        rewrite Heq; unfold meta_loc; simpl; omega. 
      -rewrite Forall_app; split; auto; repeat constructor; simpl; auto. 
      -constructor; simpl; auto.
    }
    split; [|split]; clarify.
   *(*mem_sim*)
     
     unfold mem_sim in *; clarify.
     split; clarify; repeat rewrite in_app in *; simpl in *.
     do 3 right. left. auto.
     destruct H1 as [? | [? | [? | ?]]]; clarify; contradiction H5;
     try solve [left; simpl; abstract omega].
     apply (mops_set_vc_meta_cl (map (C t0) (rev (interval 0 zt))) zt c H22 H2). auto.
   *(*clocks_sim *)
     inversion Hsteps; clarify.
     assert(Hobvious:
              [Read t0 (C' + t0, t0) (C t0 t0);
                Write t0 (C' + t0, t0) (C t0 t0 + 1);Rel t0 m]=
              [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (C' + t0, t0) (C t0 t0 + 1)]
                ++[Rel t0 m]) by clarify.
     setoid_rewrite Hobvious. rewrite app_assoc. rewrite app_assoc.
     apply clocks_sim_nonmeta; try solve [repeat constructor; clarify].
     eapply clocks_sim_writeC.
     { instantiate(1:=(C,upd L m (C t0), R ,W)).
       instantiate(1:=(m0 ++ m2) ++
           mops_set_vc (C' + t0) (L' + m) zt t0
             (map (C t0) (rev (interval 0 zt))) ++
             [Read t0 (C' + t0, t0) (C t0 t0)]).
       rewrite app_assoc.
       apply clocks_sim_allreads; clarify.
       -eapply clocks_sim_set_vc_CL; eauto.
        eapply consistent_app_SC; rewrite <- app_assoc; eauto.
       -eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto.
       -repeat constructor; clarify.
     }
     { apply H2. }
     { eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
     { apply H2. }
     { eauto. }
     { instantiate (1:=C t0 t0 +1 ).
       unfold vc_inc, upd. clarify. apply functional_extensionality.
       intros. destruct(eq_dec t0 x); clarify.
       apply functional_extensionality. intros. destruct (eq_dec x0 x); clarify.
       omega. }
     { repeat rewrite <- app_assoc. clarify. }
     { rewrite <- app_assoc. simpl. rewrite <-app_assoc. auto. }
     { repeat constructor; clarify. intro Habsurd. contradiction H21.
       unfold meta_loc', meta_loc in *; clarify.
       do 3 right. left. split; auto. } 
 -(*spawn*) 
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   rewrite <- app_assoc; simpl; do 5 eexists.
   +apply iexec_spawn; eauto.
    { inversion Hstep.  
      intro Hin. 
      unfold state_sim in HPsim. clarify.
      contradiction Hnew. 
      assert(forall (X Y: Type) l1 l2, Forall2 (fun (x y: X*Y) => fst x =fst y) l1 l2 -> map fst l1 = map fst l2) as Hmap_fst.
      {
        intros A B l1.
        induction l1; clarify.
        -inversion H0; clarify. 
        -destruct l2; clarify.
         +inversion H0; clarify.
         +inversion H0; clarify.
          specialize(IHl1 l2 H6). clarify.
          rewrite IHl1, H4.
          auto.
      }
      assert (forall a b, (fun t1 t2 : tid * prog =>
                             fst t1 = fst t2 /\ snd t2 = instrument (snd t1) (fst t1)) a b -> (fun t1 t2: tid * prog => fst t1 = fst t2) a b) as Htrivial.
      {
        intros ? ? H0. inversion H0; clarify.
      }  
      apply Forall2_impl with (Q:= (fun t1 t2: tid * prog => fst t1 = fst t2)) in HPsim.
      specialize(Hmap_fst _ _ _ _ HPsim).
      clarify.
      setoid_rewrite Hmap_fst. auto. rewrite <- app_assoc. apply Hin.
      intros ? ? H0. inversion H0; clarify.
    }
    { instantiate(1:=map (C t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      omega.
    }
    { instantiate(1:=map (C u) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      omega.
    }
   +(*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    instantiate(1:=C t0 t0).
    assert(Hcon_m02lc: consistent  ((m0 ++ m2) ++
      mops_max_vc (C' + t0) (C' + u) (map (C t0) (rev (interval 0 zt)))
        (map (C u) (rev (interval 0 zt))) t0 zt ++
        mops_inc_vc (C' + t0) (C t0 t0) t0)).
    {
      unfold mops_inc_vc. clarify.
      rewrite split_app. rewrite app_assoc.
      apply can_write_thread.
      apply can_write_SC.
      -specialize(Hs_c t0 H2). unfold clock_match in Hs_c. 
       specialize(Hs_c t0). clarify.
      -rewrite app_assoc. apply can_read_thread. 
       apply can_read_SC; auto.
       + specialize(Hs_c t0 H2). unfold clock_match in Hs_c;
         specialize(Hs_c t0). clarify.
       + simpl.
         apply (mops_max_vc_con_cc' Hs); eauto.
       + rewrite Forall_forall. intros x Hin. apply in_mops_max_vc' in Hin.
         destruct x; clarify.
         destruct x; clarify.
         intro Heq. inversion Heq; clarify.
         assert(Hnu : n = u).
         rewrite <- minus_plus with (n:=C').
         rewrite <- H1. rewrite minus_plus. auto.
         rewrite Forall_app in Ht_spawn. 
         inversion Ht_spawn; clarify. apply Forall_inv in Ht_spawn2. 
         clarify.
      - rewrite Forall_app; split; auto; constructor; simpl; auto.
    }
    split;[|split]; clarify.
    *(*mem_sim*)
     unfold mem_sim in *; clarify.
     split; clarify; repeat rewrite in_app in *; simpl in *.
     contradiction H5; destruct H1 as [? | [? | ?]]; clarify.
     { apply (mops_max_vc_meta_cc (map (C t0) (rev (interval 0 zt))) (map (C u) (rev (interval 0 zt))) zt c H21 H2). auto. }
     { left; simpl; abstract omega. }
     { left; simpl; abstract omega. }
    *(*clocks_sim*)
      unfold mops_inc_vc. rewrite app_assoc, split_app.
      eapply clocks_sim_writeC; clarify.
      { instantiate(1:=W). instantiate(1:=R). instantiate(1:=L).
        instantiate (1:=upd C u (vc_join (C u) (C t0))).
        eapply clocks_sim_allreads; clarify.
        -eapply clocks_sim_max_vc_CC.
         +instantiate(1:=(C,L,R,W)). auto.
         +eauto.
         +apply H2.
         +apply H21.
         +rewrite Forall_app in Ht_spawn. inversion Ht_spawn; clarify.
          apply Forall_inv in Ht_spawn2. clarify.
         +eauto.
         +clarify.
         +eapply consistent_app_SC; rewrite <- app_assoc; eauto.
        -eapply consistent_app_SC; rewrite <- app_assoc; simpl; rewrite <- app_assoc; eauto.
        -repeat constructor; clarify.
      }
      { auto. }
      { rewrite <- app_assoc; simpl; rewrite <-app_assoc; auto. }
      { auto. }
      { inversion Hsteps; clarify. unfold upd, vc_join, vc_inc; clarify.
        apply functional_extensionality. intro tx.
        destruct (eq_dec t0 tx); clarify.  apply functional_extensionality.
        intro tx'. destruct (eq_dec tx' tx); clarify.
        -omega.
        -destruct (eq_dec tx tx'); clarify. rewrite max_self. auto.
      }
 -(*wait*) 
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   apply in_split in Hdone. inversion Hdone; clarify.

   assert( u < zt ) as Hu.
     rewrite H in Ht. rewrite Forall_app in Ht; clarify.
     inversion Ht2; clarify.
   do 5 eexists.
   +(*iexec*)
    apply iexec_wait; eauto.
    { 
      unfold state_sim in HPsim.
      rewrite H in HPsim. Check Forall2_app_inv_l.
      apply Forall2_app_inv_l in HPsim.
      inversion HPsim; clarify.
      inversion HPsim21; clarify.
      rewrite HPsim22.
      rewrite HPsim22 in Hdistinct.
      rewrite in_app.
      right.
      destruct y; clarify.
    }
    { instantiate(1 := map (C u) (rev (interval 0 zt))). 
       rewrite map_length, rev_length, interval_length; omega. }
    { instantiate(1:= map (C t0) (rev (interval 0 zt))).
       rewrite map_length, rev_length, interval_length.
       omega.  }
   +(*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi ; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    instantiate(1:=(C u u)).
    assert(Hcon_m02lc:  consistent ((m0 ++ m2) ++
      mops_max_vc (C' + u) (C' + t0) (map (C u) (rev (interval 0 zt)))
        (map (C t0) (rev (interval 0 zt))) t0 zt ++
        mops_inc_vc' (C' + u) (C u u) t0 u)).
    {
      unfold clock_match in Hs_c. specialize (Hs_c u Hu u). clarify.
      eapply mops_inc_vc'_con; eauto.
      apply can_read_SC; eauto.
      -eapply (mops_max_vc_con_cc Hs); eauto.
      -rewrite Forall_forall. intros c Hin. apply in_mops_max_vc' in Hin. destruct c; clarify.
       destruct x3; clarify.
       intro Heq. inversion Heq; clarify. apply plus_reg_l in H2.
       rewrite Forall_app in Ht_spawn. inversion Ht_spawn; clarify. apply Forall_inv in Ht_spawn2. clarify. }
    split; [|split]; clarify.
    *(*mem_sim*) 
     unfold mem_sim. intros. clarify. split; intros; clarify.
     contradiction H02.
     rewrite in_app in H01. destruct H01 as [Hin1| Hin2]; clarify.
     { apply (mops_max_vc_meta_cc (map (C u) (rev (interval 0 zt)))
                                (map (C t0) (rev (interval 0 zt)))
                                zt c Hu H3); eauto. }
     { inversion Hin2; unfold meta_loc; clarify; omega. }
    *(*clocks_sim*)
      inversion Hsteps; clarify.
      unfold mops_inc_vc' in *. rewrite app_assoc, split_app.
      eapply clocks_sim_writeC.
      { instantiate(1:=((upd C t0 (vc_join (C t0) (C u))),L,R,W)).
        instantiate(1:= ((m0 ++ m2) ++
                  mops_max_vc (C' + u) (C' + t0)
                    (map (C u) (rev (interval 0 zt)))
                    (map (C t0) (rev (interval 0 zt))) t0 zt ++
                    [Read t0 (C' + u, u) (C u u)])).
        rewrite app_assoc.
        eapply clocks_sim_allreads; clarify.
        -eapply clocks_sim_max_vc_CC.
         { instantiate(1:=(C,L,R,W)). auto. }
         { eauto. }
         { apply Hu. }
         { apply H3. }
         { rewrite Forall_app in Ht_spawn. inversion Ht_spawn; clarify.
           apply Forall_inv in Ht_spawn2. clarify. }
         { auto. }
         { auto. }
         { eapply consistent_app_SC; rewrite <- app_assoc; eauto. }
        -eapply consistent_app_SC; rewrite <- app_assoc; simpl; rewrite <- app_assoc; eauto.
        -repeat constructor; clarify.
      }
      { apply Hu. }
      { rewrite <-app_assoc. simpl. rewrite <-app_assoc. auto. }
      { apply Hu. }
      { eauto. }
      { instantiate(1:= C u u +1).
        unfold upd, vc_join, vc_inc; clarify.
        apply functional_extensionality. intro tx.
        destruct (eq_dec u tx); clarify.
        apply functional_extensionality.  intro tx'.
        destruct (eq_dec tx' tx),(eq_dec tx tx'); clarify.
        - omega.
        - rewrite max_self. auto.
      }
      { repeat rewrite <- app_assoc. clarify. } 
 -(*assert_le*) 
   clarify. do 5 eexists.
   +eapply iexec_assert; eauto.
    Check eval_sim.
    unfold fresh_tmps in Hfresh. rewrite Forall_app in Hfresh.
    inversion Hfresh; clarify. rewrite Forall_forall in Hfresh2.
    specialize(Hfresh2 (t0, Assert_le e1 e2 :: rest)). clarify.
    inversion Hfresh2. clarify.
    assert( eval (G2 t0) e1= eval (G1' t0) e1) as Heval_e1.
      symmetry. apply eval_sim. intros. eapply HGsim; eauto; intro Heq;
      clarify.
    assert( eval (G2 t0) e2= eval (G1' t0) e2) as Heval_e2.
      symmetry. apply eval_sim. intros. eapply HGsim; eauto; intro Heq;
      clarify.
    rewrite Heval_e1, Heval_e2. auto.
   +(*consistent & mem_sim*)
     rewrite app_nil_r.
     clarify. split.
     *unfold mem_sim. intros. clarify. split; intros; clarify.
     * inversion Hsafe ; clarify.
 -clarify; do 5 eexists; [eapply iexec_exec; eauto|];
  exploit sim_step; eauto; clarify.
  rewrite app_assoc. auto.
Qed.


Lemma instrument_sim_race2 : forall P P1 P2 G1 G2 t ops2
  (HfreshP: fresh_tmps (init_state P)) (Hsafe_locsP: safe_locs (init_state P))                  (Hlegal_tidsP: legal_tids (init_state P))              
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1) (Hdistinct: distinct P2)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2) 
  m0 m2 (Hroot : iexec_star (init_state (instrument P 0)) init_env ops2 m2 P2 G2)
  (Hinit : forall p, initialized m0 p)
  o2 c2 (Hstep : fail_iexec P2 t o2 c2) 
  (Hcon2 : consistent (m0++m2 ++ c2)) s (Hs : clocks_sim m0 s) ,               
  exists o1 ops1 m1 c1 P1' G1s G1', exec_star (Some (init_state P)) init_env ops1 m1 (Some P1) G1s/\ env_sim G1s G1 /\ exec P1 G1s t o1 c1 (Some P1') G1' /\ consistent (m0++m1(* the load/store hasn't been executed in m2*) (* ++(opt_to_list c1) *)) /\ mem_vals (m0++m1) (m0++m2) /\
   ( exists s', step_star s ops1 s' /\ (forall s'', ~step_star s' (opt_to_list o1) s'')).
Proof.
  
  clarify.
  exploit instrument_sim_safe2'.
  { instantiate (1:=init_state P). clarify. }
  { auto. }
  { auto. }
  { instantiate (1:=init_state (instrument P 0)). apply distinct_init. }
  { unfold state_sim, init_state. clarify. }
  { do 2 instantiate (1:=init_env). unfold env_sim. clarify. }
  { eauto. }
  { apply Hroot. }
  { instantiate (1:=[]). instantiate(1:=[]). setoid_rewrite app_nil_r. apply mem_vals_refl. }
  { rewrite app_nil_r. eapply consistent_app_SC;  eauto. }
  { rewrite app_nil_r. eapply consistent_app_SC; rewrite <-app_assoc; eauto. }
  { rewrite app_nil_r. apply Hs. }
  { auto. }
  { clarify. }
  intros (ops1 & m1 & P1_good & G1_good & Hexec_star_P1good & Hstate_simP1good
               & Henv_simG1good & Hcon_m01 & Hmem_vals_m012 & s_good & Hss_sgood
               & Hcs_m02sgood).
  rewrite app_nil_r in *.
  assert(env_sim G1_good G1) as Henv_simG1s.
  { eapply env_sim_trans; eauto. apply env_sim_symm. auto. }
  assert( P1_good= P1) as HP1_good by (eapply state_sim_same; eauto).
  unfold clocks_sim in Hcs_m02sgood; clarify.
  assert(Hinit_m02: forall p, meta_loc p -> initialized (m0++m2) p).
  { intros. apply init_steps; auto. eapply prog_steps'. apply Hroot. }
  clarify.
  inversion Hstep; clarify; exploit Forall2_app_inv_r; eauto;
  intros (P0' & P3' & HP0 & Hrest & HP1);
  inversion Hrest as [|(tx, [|i ?]) ? ? ? [? Hi] HP3]; clarify.
  -exploit (instrument_incom (Load a (x,o))).
   { instantiate(1:= instrument l t). instantiate (1:= t). instantiate (1:= i). instantiate (1:=rest).  simpl. rewrite <- app_assoc. clarify. }
   clarify.
   do 7 eexists.  split;[|split;[|split;[|split;[|split]]]]; eauto.
   +(*we must instantiate v here*) 
     eapply exec_load with (v:=0). eauto.
   +exists s_good. split; eauto.
    intros s'' Hss. inversion Hss; 
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    inversion Hstep0; clarify. 
    specialize (Hcs_m02sgood22 x H32). destruct Hcs_m02sgood22 as (Hcs_sgoodr & Hcs_sgoodw).
    exploit hb_check_vals'.
    { intros. specialize (Hinit_m02 (W'+x, z)).  apply Hinit_m02.
      unfold meta_loc. simpl. omega. }
    { intros. specialize (Hinit_m02 (C'+t, z)).  apply Hinit_m02.
      unfold meta_loc. simpl. omega. }
    {
      exploit loc_valid_ops_SC.
      {instantiate (1:=[Acq t (X'+x)]). instantiate(1:=mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t).
       rewrite Forall_forall. clarify. rewrite Forall_forall. intros c Hin.
       apply in_mops_hb_check in Hin. intro Heq; destruct c; clarify.
       destruct Hin as [Hin | Hin]; clarify.
       +specialize(Hmetalocs_disjoint_WX H32 H32); clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32); clarify.
      }
      {rewrite Forall_forall. clarify. }
      {clarify. }
      intro Hcon_iff.
      instantiate (1:=m0++m2) in Hcon_iff. rewrite <- app_assoc in Hcon_iff.
      simpl in Hcon_iff. rewrite Hcon_iff in Hcon2.
      clarify. eapply Hcon22.
    }
    { eauto. }
    { eauto.  }
    { apply Hcs_sgoodw. }
    { specialize (Hcs_m02sgood1 t H3). apply Hcs_m02sgood1. }
    { eauto. }
    { auto. }
    clarify. 
   -exploit (instrument_incom (Store (x,o) e)).
   { instantiate(1:= instrument l t). instantiate (1:= t). instantiate (1:= i). instantiate (1:=rest).  simpl. rewrite <- app_assoc. clarify. }
   clarify.
   do 7 eexists. split;[|split;[|split;[|split;[|split]]]]; eauto.
   +apply exec_store; auto.
   +exists s_good. split; auto.
    clarify. intro Hss. inversion Hss; 
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    inversion Hstep0; clarify. 
    specialize (Hcs_m02sgood22 x H32).
    destruct Hcs_m02sgood22 as (Hcs_sgood22r & Hcs_sgood22w).
    exploit hb_check_vals'.
    { intros. specialize (Hinit_m02 (W'+x, z)).  apply Hinit_m02.
      unfold meta_loc. simpl. omega. }
    { intros. specialize (Hinit_m02 (C'+t, z)).  apply Hinit_m02.
      unfold meta_loc. simpl. omega. }
    { exploit loc_valid_ops_SC.
      {instantiate (1:=[Acq t (X'+x)]). instantiate(1:=mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t).
       rewrite Forall_forall. clarify. rewrite Forall_forall. intros c Hin.
       apply in_mops_hb_check in Hin. intro Heq; destruct c; clarify.
       destruct Hin as [Hin | Hin]; clarify.
       +specialize(Hmetalocs_disjoint_WX H32 H32); clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32); clarify.
      }
      {rewrite Forall_forall. clarify. }
      {clarify. }
      intro Hcon_iff.
      instantiate (1:=(m0++m2)) in Hcon_iff. simpl in Hcon_iff.
      rewrite <- app_assoc in Hcon_iff. rewrite Hcon_iff in Hcon2. clarify. eapply Hcon22.  }
    { eauto. }
    { eauto.  }
    { apply Hcs_sgood22w. }
    { specialize (Hcs_m02sgood1 t H3). apply Hcs_m02sgood1. }
    { eauto. }
    { auto. }
    clarify.
   -exploit (instrument_incom (Store (x,o) e)).
   { instantiate(1:= instrument l t). instantiate (1:= t). instantiate (1:= i). instantiate (1:=rest).  simpl. rewrite <- app_assoc. clarify. }
   clarify.
   do 7 eexists. split;[|split;[|split;[|split;[|split]]]]; eauto.
   +eapply exec_store; eauto.
   +exists s_good. split; auto.
    clarify. intro Hss. inversion Hss; 
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    inversion Hstep0; clarify.
    specialize (Hcs_m02sgood22 x H32). clarify.
    exploit hb_check_vals'.
    { intros. specialize (Hinit_m02 (R'+x, z)).  apply Hinit_m02.
      unfold meta_loc. simpl. omega. }
    { intros. specialize (Hinit_m02 (C'+t, z)).  apply Hinit_m02.
      unfold meta_loc. simpl. omega. }
    { rewrite split_app, <- app_assoc in Hcon2.
      rewrite app_assoc in Hcon2.
      apply loc_valid_ops_SC in Hcon2; clarify.
      -eapply reads_noops_SC.
       { instantiate (1:=mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t).
         eapply consistent_app_SC;rewrite <- app_assoc; eauto. }
       { rewrite Forall_forall. intros c Hin. apply in_mops_hb_check in Hin.
         destruct c; clarify. }
       { eauto. }
      -rewrite Forall_forall. intros c Hin. inversion Hin. clarify.
       rewrite Forall_forall. intros c Hin. rewrite in_app in Hin.
       intro Heq. destruct Hin as [Hin | Hin]; apply in_mops_hb_check in Hin; destruct c; clarify;
       destruct Hin as [Hin | Hin]; clarify.
       +specialize(Hmetalocs_disjoint_WX H32 H32). clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
       +specialize(Hmetalocs_disjoint_RX H32 H32). clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
       +inversion H; clarify.
      -rewrite Forall_forall. clarify.
      -rewrite Forall_app. clarify.
    } 
    { auto. omega. }
    { auto. omega. }
    { apply Hcs_m02sgood221. }
    { specialize (Hcs_m02sgood1 t H3). apply Hcs_m02sgood1. }
    { eauto. }
    { auto. }
    clarify. 
Qed.




Lemma filter_minimal: forall (X:Type) l1 l2 (f: X->bool)
 (Hfilter_eq: filter f l1 = l2), 
filter f l2=l2.
Proof.
  intros.
  rewrite <- Hfilter_eq.
  rewrite filter_idem.
  auto.
Qed.

Lemma mem_sim'_app : forall m1 m2 m3 m4
  (Hsim12: mem_sim' m1 m2) (Hsim34: mem_sim' m3 m4),
  mem_sim' (m1++m3) (m2++m4).
Proof.
  intros. unfold mem_sim' in *.
  rewrite filter_app. clarify.
Qed.

Lemma mem_sim'_split: forall m1 m2 m3
  (Hsim12: mem_sim' m3 (m1++m2)),
  exists m31 m32, m3=m31++m32 /\ mem_sim' m31 m1 /\ mem_sim' m32 m2.
Proof.
  intros.
  unfold mem_sim' in Hsim12. rewrite filter_app in Hsim12.
  do 2 eexists. split;[|split].
  -eauto.
  -unfold mem_sim'. clarify.
  -unfold mem_sim'. clarify.
Qed.


Lemma step_star_inv : forall s1 s2 lo,
  step_star s1 lo s2 -> exists lo1 lo2 s', step_star s1 lo1 s' /\ step_star s' lo2 s2.
Proof.
  intros s1 s2 lo Hstep_star. 
  destruct lo;clarify.
  -inversion Hstep_star. 
   exists [], [], s1. clarify. 
  -inversion Hstep_star.
   exists [o], lo, s'. split.
   +apply ss_step with (s':=s'); auto.
    apply ss_refl.
   +auto.
Qed.

Lemma step_star_app_inv: forall (s1 : @VectorClocks.state tid var lock) s2 lo1 lo2
 (Hstep_star: step_star s1 (lo1++lo2) s2), exists s', step_star s1 lo1 s' /\ step_star s' lo2 s2.
Proof.
  intros. generalize dependent s1.
  induction lo1; clarify.
  -exists s1. split; clarify. apply ss_refl.
  -inversion Hstep_star; clarify.
   specialize (IHlo1 s' Hsteps).
   inversion IHlo1 as (s'' & Hss_s's'' & Hss_s''_s2).
   exists s''. split; clarify.
   eapply ss_step; eauto.
Qed.


Lemma spawn_wait_other_prog_nb : forall P
  (Hspawn_wait_other_prog: spawn_wait_other_prog P),                             
  Forall
     (fun p : tid * list instr =>
      let (t0, y) := p in
      match y with
      | [] => True
      | Assign _ _ :: _ => True
      | Load _ _ :: _ => True
      | Store _ _ :: _ => True
      | Lock _ :: _ => True
      | Unlock _ :: _ => True
      | Spawn u _ :: _ => u <> t0
      | Wait u :: _ => u <> t0
      | Assert_le _ _ :: _ => True
      end) P.
Proof.
  clarify.
  unfold spawn_wait_other_prog in *.
  rewrite Forall_forall in *. clarify.
  specialize(Hspawn_wait_other_prog x H).
  destruct x; unfold spawn_wait_other in *; clarify.
  destruct l; clarify. destruct i; clarify.
Qed.

Corollary instrument_sim_safe' : forall P P1 P2 G1 G2 h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1) (Hdistinct : distinct P2)
  (Ht : legal_tids P1) 
  (Ht_spawn: spawn_wait_other_prog P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m0 (Hinit: forall p: ptr, initialized m0 p)
  m1 (Hroot : exec_star (Some (init_state P)) init_env h m1 (Some P1) G1)
  lo lc P1' G1' (Hstep : exec_star (Some P1) G1 lo lc (Some P1') G1')
  (Hcon : consistent ((m0 ++m1)++ lc)) (Hprog_m1: Forall prog_op m1)
  m2 (Hprog_m2: Forall prog_op m2)
   (Hcon2: consistent (m0++m2)) (Hmem_vals: mem_vals (m0++m1) (m0++m2))
  s (Hs : clocks_sim (m0++m2) s) s' (Hsafe : step_star s lo s'),
  exists lo2 lc2 P2' G2', exec_star (Some P2) G2 lo2 lc2 (Some P2') G2' /\
    consistent ( (m0++m2) ++ lc2) /\ state_sim P1' P2' /\ env_sim G1' G2' /\
    mem_vals ((m0++m1)++lc) ((m0++m2)++lc2) /\ clocks_sim (m0++m2++lc2) s'.
Proof. 
  intros. remember (Some P1) as Pa; remember (Some P1') as Pb;
  generalize dependent P1; generalize dependent P2;
  generalize dependent G2; generalize dependent m1; generalize dependent m2;
  generalize dependent s; generalize dependent h;
  induction Hstep; clarify.
  -exists []. exists []. exists P2. exists G2. 
   split;[|split;[|split;[|split;[|split]]]]; clarify.
   +apply exec_refl.
   +rewrite app_nil_r. auto.
   +do 2 rewrite app_nil_r. auto.
   +rewrite app_nil_r.
    inversion Hsafe. clarify.
  -destruct P'.
   +rename s0 into P1i.
    apply step_star_app_inv in Hsafe. inversion Hsafe as (si & Hss_s_si & Hss_si_s').
    exploit instrument_sim_safe.
    { instantiate(1:=P1). auto. }
    { auto. }
    { instantiate(1:=P2). auto. }
    { unfold legal_tids in Ht. clarify. }
    { apply spawn_wait_other_prog_nb. auto. }
    { auto. }
    { instantiate(1:=G2). instantiate(1:=G). auto. }
    { intros. apply Hinit; clarify. }
    { apply Hroot. }
    { apply Hexec. }
    { eapply consistent_app_SC. rewrite <- app_assoc. eauto. }
    { clarify. }
    { apply Hprog_m2. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    intros (lo2i & lc2i & P2i&G2' & Hexec_star_P2i & Hcon_lc2i & Hstate_sim_P2i & Henv_sim_G2'
                 & Hmem_sim_lc2i & Hclocks_sim_lc2i).
    rewrite <- app_assoc in Hcon_lc2i.
    assert (Hprog_m2lc2i: Forall prog_op (m2++lc2i)).
    { rewrite Forall_app. split; clarify.
      eapply prog_steps. eauto. }
    specialize(IHHstep (h++(opt_to_list o)) si Hss_si_s' (m2++lc2i) Hprog_m2lc2i Hcon_lc2i
                       Hclocks_sim_lc2i (m1++opt_to_list c)).
    assert(Hexec_starP1i: exec_star (Some (init_state P)) init_env (h++opt_to_list o) (m1 ++ opt_to_list c) (Some P1i) G').
    { eapply exec_star_trans; eauto. rewrite <- (app_nil_r (opt_to_list o)).
      rewrite <- (app_nil_r (opt_to_list c)). eapply exec_step; eauto. constructor. }
    assert(Hmem_vals_m1c_m2lc2i: mem_vals (m0++m1++opt_to_list c) (m0++m2++lc2i)).
    { do 2 rewrite app_assoc. 
      eapply mem_vals_sim_app; eauto. eapply prog_steps.
      rewrite <- (app_nil_r (opt_to_list c)). eapply exec_step. eauto. constructor. } 
    assert(Hcon1':  consistent ((m0 ++ m1 ++ opt_to_list c) ++ lc)).
    { do 2 rewrite <- app_assoc. rewrite <- app_assoc in Hcon. auto. }
    assert(Hdistinct_P2i: distinct P2i).
    { eapply distinct_steps; eauto. }
    assert(Hfresh_tmps_P1i: fresh_tmps P1i).
    { exploit fresh_tmps_step; eauto.  }
    assert(Hsafe_locs_P1i: safe_locs P1i).
    { exploit safe_locs_step; eauto. }
    assert(Hlegal_tids_P1i: legal_tids P1i).
    { eapply legal_tids_step; eauto. }


    assert(Hspawn_wait_otherP1i:  spawn_wait_other_prog P1i).
    { eapply spawn_wait_other_prog_step; eauto. }
    assert(HP1i: Some P1i=Some P1i) by auto.
    assert(Hprog_m1c: Forall prog_op (m1++ opt_to_list c)).
    {  rewrite Forall_app. split; clarify.
       eapply prog_step; eauto. }
    specialize(IHHstep Hexec_starP1i Hcon1' Hprog_m1c Hmem_vals_m1c_m2lc2i G2' Henv_sim_G2' P2i Hdistinct_P2i P1i).
    specialize(IHHstep Hfresh_tmps_P1i Hsafe_locs_P1i Hlegal_tids_P1i Hspawn_wait_otherP1i Hstate_sim_P2i HP1i).
    inversion IHHstep as (lo2 & lc2 & P2' & G2'' & Hexec_star_P2'
                              & Hcon_mlc2 & Hstate_sim_P2' & Henv_sim_G2'' & Hmem_vals_lc2
                              & Hclocks_sim_mlc2).
    exists (lo2i++lo2), (lc2i++lc2), P2', G2''. rewrite <- app_assoc in *.
    split;[|split;[|split;[|split;[|split]]]]; clarify.
    *eapply exec_star_trans; eauto.
    *rewrite <- app_assoc in Hcon_mlc2. auto.
    *repeat rewrite <- app_assoc in *. auto.
   +inversion Hstep. 
Qed.         
  
Lemma instrument_sim_race : forall P P1 P2 G1 G2 t ops1
  (HfreshP: fresh_tmps (init_state P)) (HlocsP: safe_locs (init_state P))                       (HtP: legal_tids (init_state P))          
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : legal_tids P1)  (Hdistinct : distinct P2)
  (Hspawn_wait_other: spawn_wait_other_prog (init_state P))
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m1 (Hroot : exec_star (Some (init_state P)) init_env ops1 m1 (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 t o c (Some P1') G1') m0
  (Hinit : forall p, initialized m0 p) 
  (Hcon : consistent (m0 ++ m1 (*++ opt_to_list c*))) s (Hs : clocks_sim m0 s)
   s_good (Hsafe:  step_star s ops1 s_good)   
  (Hrace : forall s', ~step_star s_good (opt_to_list o) s'),
                            exists  lo2 m2 lo lc G2s G2', exec_star (Some (init_state (instrument P 0))) init_env lo2 m2 (Some P2) G2s /\exec_star (Some P2) G2s lo lc None G2'
                                                   /\ consistent (m0 ++ m2 ++ lc) /\ mem_vals (m0++m1) (m0++m2) /\ env_sim G1 G2s.
Proof.
  intros. 
  exploit instrument_sim_safe'.
  { instantiate(1:=init_state P).  auto. }
  { auto. }
  { instantiate(1:=init_state (instrument P 0)). unfold distinct, init_state. clarify.
    constructor; auto. }
  { auto. }
  { auto. }
  { unfold state_sim, init_state. clarify. }
  { do 2 instantiate(1:=init_env). apply env_sim_refl. }
  { instantiate(1:=m0). clarify. }
  { constructor. }
  { apply Hroot. }
  { rewrite app_nil_r. eauto. }
  { constructor. }
  { instantiate(1:=[]). constructor. }
  { rewrite app_nil_r. eapply consistent_app_SC;  eauto. }
  {  apply mem_vals_refl. }
  { rewrite app_nil_r. apply Hs. }
  { apply Hsafe. }
  rewrite app_nil_r.
  intros (ops2 & m2 & P2_good & G2_good & Hexec_starP2good & Hcon_m02 &
               Hstate_simP2good & Henv_simG2sgood & Hmem_vals_m012 & Hclocks_simm02).
  rewrite app_assoc, app_nil_r in Hclocks_simm02.
  assert(P2=P2_good) as HP2same.
  { eapply state_sim_same'; eauto. } 
  inversion Hstep; clarify; exploit Forall2_app_inv_l; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - specialize (Hrace s_good); contradiction Hrace; apply ss_refl.
  -(*load*)
    destruct x as (x, o).
    assert(Hclocks_m02:=Hclocks_simm02).
    destruct Hclocks_simm02 as (HC & HL & HRW).
    generalize (HRW x); intro HRWx.
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    generalize (clock_match_bounded HRWx2); intro Hbound.
    destruct (bounded_le_dec (clock_of s_good t0) Hbound) as [? | (t & Hgt)].
    { destruct s_good as (((?, ?), ?), ?); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].  }
    { 
      exploit load_handler_race_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s_good t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s_good x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { rewrite first_gt_spec.
        destruct Hgt as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (write_of s_good x) (interval 0 zt)) - t - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (write_of s_good x) (interval 0 zt)) =
                  length (map (clock_of s_good t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      
      rewrite plus_0_r; intro Hload.
      instantiate(1:=t0) in Hload.
      instantiate(1:=G2_good) in Hload. instantiate(1:=x) in Hload. 
      instantiate(1:= l') in Hload.
      instantiate(1:=[Load a (x, o); Unlock (X' + x)] ++ instrument rest t0) in Hload.
      instantiate(1:=P0') in Hload.
      rewrite <- app_assoc. unfold load_handler in Hload.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hload.
      simpl in Hload. simpl. remember  (upd_env (upd_env G2_good t0 tmp1 (write_of s_good x t)) t0 tmp2
                                                (clock_of s_good t0 t)) as G2race.
      do 6 eexists. split;[|split;[|split;[|split]]]; clarify.
      -rewrite <- app_assoc in Hexec_starP2good. clarify. eauto.
      -apply Hload.
      -rewrite app_assoc. rewrite split_app. apply mops_hb_check_con; clarify.
       +apply clocks_sim_acq; clarify.
       +inversion Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
        inversion Ht2 as (HtP0 & Hirest).  inversion Hirest. clarify.
       +apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify.
      -auto.
      -auto.
    }
    -(*store*)
     destruct x as (x, o). 
     inversion Hclocks_simm02 as (HC & HL & HRW).
     generalize (HRW x); intro HRWx.
     setoid_rewrite Forall_app in Hlocs; clarify.
     inversion Hlocs2 as [|?? Hi ?]; clarify.
     inversion Hi; clarify.
     generalize (clock_match_bounded HRWx1); intro HboundR.
     generalize (clock_match_bounded HRWx2); intro HboundW.
     destruct (bounded_le_dec (clock_of s_good t0) HboundW) as [? | (tW & HgtW)];
     destruct (bounded_le_dec (clock_of s_good t0) HboundR) as [? | (tR & HgtR)].
     { (*RF*)
       destruct s_good as (((?, ?), ?), ?); exploit Hrace; [|clarify].
       econstructor; [constructor; auto | apply ss_refl]. }
     { (*WAR*)
      exploit store_handler_race_war_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s_good t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s_good x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      {   instantiate (1 := map (read_of s_good x) (rev (interval 0 zt))).
        repeat rewrite map_length, rev_length, interval_length. 
        rewrite <- minus_n_O, plus_0_r; eauto.  }
      { apply vc_le_first_gt; auto. }
      { rewrite first_gt_spec.
        destruct HgtR as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (read_of s_good x) (interval 0 zt)) - tR - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (read_of s_good x) (interval 0 zt)) =
                  length (map (clock_of s_good t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hstore.
      instantiate(1:=t0) in Hstore.
      instantiate(1:=G2_good) in Hstore. instantiate(1:=x) in Hstore. 
      instantiate(1:= l') in Hstore.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hstore.
      instantiate(1:=P0') in Hstore.
      rewrite <- app_assoc. unfold store_handler in Hstore.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hstore.
      simpl in Hstore. simpl.
      rewrite <- app_assoc in Hexec_starP2good.
      do 6 eexists. split;[|split;[|split;[|split]]]; eauto.
      rewrite app_assoc, split_app, app_assoc.
      destruct Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
      inversion Ht2 as (Ht21  & Ht22). inversion Ht22.
      assert (Hcon_hb:   consistent
     (((m0 ++ m2) ++ [Acq t0 (X' + x)]) ++
      mops_hb_check (W' + x) (C' + t0)
        (map (write_of s_good x) (rev (interval 0 zt)))
        (map (clock_of s_good t0) (rev (interval 0 zt))) zt t0)).
      { apply mops_hb_check_con; clarify.
        - apply clocks_sim_acq; clarify.
        - apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify. }
      apply mops_hb_check_conR; clarify.
      apply clocks_sim_allreads; clarify.
        -apply clocks_sim_acq; clarify.
        -apply mops_hb_check_read.
      
    }
    {(*WAW*)
      exploit store_handler_race_waw_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s_good t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s_good x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { rewrite first_gt_spec.
        destruct HgtW as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (write_of s_good x) (interval 0 zt)) - tW - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (write_of s_good x) (interval 0 zt)) =
                  length (map (clock_of s_good t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hstore.
      instantiate(1:=t0) in Hstore.
      instantiate(1:=G2_good) in Hstore. instantiate(1:=x) in Hstore. 
      instantiate(1:= l') in Hstore.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hstore.
      instantiate(1:=P0') in Hstore.
      rewrite <- app_assoc. unfold store_handler in Hstore.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hstore.
      simpl in Hstore. simpl.
      rewrite <- app_assoc in Hexec_starP2good.
      do 6 eexists. split;[|split;[|split;[|split]]]; eauto.
      destruct Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
      inversion Ht2 as (Ht21  & Ht22). inversion Ht22.
      rewrite app_assoc, split_app.
     apply mops_hb_check_con; clarify.
        - apply clocks_sim_acq; clarify.
        - apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify. 
     }
    {(*both WAW&WAR, equilvalent to WAW*)
      exploit store_handler_race_waw_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s_good t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s_good x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { rewrite first_gt_spec.
        destruct HgtW as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (write_of s_good x) (interval 0 zt)) - tW - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (write_of s_good x) (interval 0 zt)) =
                  length (map (clock_of s_good t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hstore.
      instantiate(1:=t0) in Hstore.
      instantiate(1:=G2_good) in Hstore. instantiate(1:=x) in Hstore. 
      instantiate(1:= l') in Hstore.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hstore.
      instantiate(1:=P0') in Hstore.
      rewrite <- app_assoc. unfold store_handler in Hstore.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hstore.
      simpl in Hstore. simpl.
      rewrite <- app_assoc in Hexec_starP2good.
      do 6 eexists. split;[|split;[|split;[|split]]]; eauto.
      destruct Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
      inversion Ht2 as (Ht21  & Ht22). inversion Ht22.
      rewrite app_assoc, split_app.
      apply mops_hb_check_con; clarify.
      - apply clocks_sim_acq; clarify.
      - apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify. 
     }
    - destruct s_good as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -destruct s_good as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -destruct s_good as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -destruct s_good as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -specialize(Hrace s_good). contradiction Hrace; apply ss_refl. 
Qed.

Theorem instrument_correct : forall P (Hsafe_locs: safe_locs (init_state P))
  (Hfresh: fresh_tmps (init_state P)) m0 (Hcon0 : consistent m0)
  (Ht: legal_tids (init_state P))
  (Hvinit : forall v : nat, v < zv -> initialized m0 (X' + v, 0) )
  (Hcinit: forall t o : nat, t < zt -> o < zt -> initialized m0 (C' + t, o))
(Hlinit :    forall l : nat, l < zl -> initialized m0 (l, 0))
(Hsafe_waits:    safe_waits (init_state (instrument P 0)))
(Hsafe_spawns:    safe_spawns (init_state (instrument P 0)) )
(Hgood_var: forall v : nat, v < zv -> good_var v (init_state (instrument P 0)))
(Hgood_lock: forall v : nat,
   v < zv -> good_lock (X' + v, 0) (init_state (instrument P 0)))
(Hwell_locked: forall l : nat, l < zl -> well_locked l (init_state (instrument P 0)))
(Hlgood_lock:  forall l : lock,
   locks l (init_state (instrument P 0)) ->
   good_lock (l, 0) (init_state (instrument P 0)))
  (Hspawn_wait_other: spawn_wait_other_prog (init_state P))
  (Hinit: forall p : ptr, initialized m0 p)
  (Hclocks_sim: clocks_sim m0 s0) G1' m1' (Hprog_m1': Forall prog_op m1'),
  (exists ops2 m2 P2' G2', exec_star (Some (init_state (instrument P 0)))
     init_env ops2 m2 (Some P2') G2' /\ final_state (Some P2') /\
     consistent (m0 ++ m2) /\ mem_vals (m0++m2) (m0++m1') /\ env_sim G1' G2') <->
  (exists ops m1 P' G',
     exec_star (Some (init_state P)) init_env ops m1 (Some P') G' /\
     final_state (Some P') /\ consistent (m0 ++ m1) /\ mem_vals (m0++m1) (m0++m1') /\
     env_sim G' G1' /\ exists s, step_star s0 ops s).
Proof.
  intros. split.
  -(*completeness*) (* i.e., instrumented execution -> race-free *)
   intros (ops2 & m2 & P2' & G2' & Hexec_star_inst & Hfinal_P2' & Hcon_inst & Hmem_vals_m2m1' & Henv_sim_G1'G2').
   exploit exec_iexec'; eauto. 
   { rewrite instrumented_iff; clarify. }
   { unfold distinct; simpl.
     constructor; auto. }
   { repeat constructor; simpl; omega. }
   intros (? & lc' & Histeps & Hmem_ext).
   inversion Hmem_ext as (Hicon & Hinit_iff).
   assert(consistent (m0++lc')) as Hcon_m0lc'.
   {  unfold mem_ext in Hicon. specialize (Hicon []). do 2 rewrite app_nil_r in Hicon. rewrite Hicon. clarify. }
   exploit instrument_sim_safe2'. 
   { instantiate(1:=init_state P). clarify. }
   { clarify. }
   { clarify. }
   { instantiate(1:=init_state (instrument P 0) ). unfold init_state, distinct. clarify. constructor; clarify. }
   { unfold init_state, state_sim. constructor; clarify. }
   { instantiate (1:=init_env). instantiate(1:=init_env). unfold env_sim. clarify. }
   { clarify. }
   { apply Histeps. }
   { do 2 instantiate(1:=[]). rewrite app_nil_r. apply mem_vals_refl. }
   { rewrite app_nil_r. eapply consistent_app_SC; eauto.  } 
   { rewrite app_nil_r. auto. }
   { rewrite app_nil_r. apply Hclocks_sim. }
   { auto. }
   { clarify. }
   intros (lo & lc & P1' & G1 & Hexec_star_orig & Hstate_simP1'_P2'
              & Henv_simG1_G2' & Hcon_m0lc & Hmem_vals_lc_lc' & (s' & Hstep_star & Hclock_sim)).
   rewrite app_nil_r in *.
   do 4 eexists. split;[|split;[|split;[|split;[|split]]]]; eauto.
   +rewrite <- state_sim_final; eauto. 
   +apply mem_vals_ext with (m1:=(m0++m1')) in Hmem_ext.
    rewrite <- Hmem_ext in Hmem_vals_m2m1'.
    eapply mem_vals_cond_trans; eauto.
    clarify. split; intros; eapply init_steps; eauto;
    eapply prog_steps; eauto; try eapply iexec_star_exec_star; eauto.
   +apply env_sim_symm.  apply env_sim_symm in Henv_simG1_G2'. eapply env_sim_trans; eauto.
  - (*soundness*) 
   intros (ops & m1 & P' & G' & Hexec_star_orig & Hfinal_P' & Hcon & Hmem_vals & Henv_sim & Hsafe).
   destruct Hsafe as (s & Hsafe).  
   exploit instrument_sim_safe'.
   { eauto. }
   { auto. }
   { instantiate (1:=init_state (instrument P 0)).
     unfold init_state, distinct. clarify. constructor; clarify. }
   { auto. }
   { auto. }
   { unfold init_state, state_sim. clarify. }
   { instantiate (1:=init_env). unfold env_sim. clarify. }
   { clarify. }
   { constructor. }
   { apply Hexec_star_orig. }
   { rewrite app_nil_r. auto. }
   { constructor. }
   { instantiate (1:=[]). constructor. }
   { rewrite app_nil_r. eapply consistent_app_SC; eauto. }
   { apply mem_vals_refl. }
   { instantiate(1:=s0). rewrite app_nil_r. auto. }
   { instantiate(1:=s). auto. }
   intros (lo2 & lc2 & P2' & G2' & Hexec_star_instr & Hcon2 & Hstate_sim_P'_P2' 
               & Henv_sim_G'_G2' & Hmem_vals_m_lc2  & Hclocks_sim_mlc2).
   rewrite app_assoc, app_nil_r in *.
   do 4 eexists. split;[|split;[|split;[|split]]]; eauto.
   +apply state_sim_final with (P1:=P'); auto.
   +assert( forall x : block_model.ptr var,
              initialized (m0 ++ m1') x <-> initialized (m0 ++ m1) x) as Hinit_m1'm1.
    { clarify. split; clarify; apply init_steps; auto; eapply prog_steps; eauto. }
     apply mem_vals_cond_symm in Hmem_vals; auto.
    apply mem_vals_cond_symm; auto.
    clarify. split; clarify; apply init_steps; auto; eapply prog_steps; eauto.
    eapply mem_vals_cond_trans; eauto.
    clarify. symmetry. auto.
   +apply env_sim_symm. apply env_sim_symm in Henv_sim_G'_G2'.
    eapply env_sim_trans; eauto.
Qed.

Lemma step_star_det : forall s (ops : list operation) s1 (Hstep : step_star s ops s1)
  s2 (Hstep2 : step_star s ops s2), s1 = s2.
Proof.
  intros ????; induction Hstep; clarify.
  { inversion Hstep2; auto. }
  inversion Hstep2; subst.
  assert (s'0 = s'); [|clarify].
  inversion Hstep; subst; inversion Hstep1; clarify.
Qed.

Lemma safe_locs_steps : forall P G o c P' G' (Hlocs : safe_locs P)
  (Hsteps : exec_star (Some P) G o c (Some P') G'),
                          safe_locs P'.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb;
  generalize dependent P; generalize dependent P'; induction Hsteps; clarify.
  apply (safe_locs_step Hlocs) in Hexec. destruct P'; clarify.
  -eapply IHHsteps; eauto.
  -inversion Hsteps.
Qed.


Lemma fresh_tmps_steps:
  forall (meta : metadata) (P : state) (G : tid -> local -> nat) 
     o c 
    (P' : state) (G' : env),
  fresh_tmps P ->
  exec_star (Some P) G o c (Some P') G' ->
  fresh_tmps P'.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb;
  generalize dependent P; generalize dependent P'; induction H0; clarify.
  apply (fresh_tmps_step H) in Hexec. destruct P'; clarify.
  -eapply IHexec_star; clarify. auto.
  -inversion H0.
Qed.
  
Theorem instrument_correct_race : forall P
  (Hsafe_locs: safe_locs (init_state P))
  (Hfresh: fresh_tmps (init_state P)) m0 (Hcon0 : consistent m0)
  (Ht: legal_tids (init_state P))
  (Hno_asserts: no_asserts (init_state P))
(Hsafe_waits:    safe_waits (init_state (instrument P 0)))
(Hsafe_spawns:    safe_spawns (init_state (instrument P 0)) )
(Hgood_var: forall v : nat, v < zv -> good_var v (init_state (instrument P 0)))
(Hgood_lock: forall v : nat,
   v < zv -> good_lock (X' + v, 0) (init_state (instrument P 0)))
(Hwell_locked: forall l : nat, l < zl -> well_locked l (init_state (instrument P 0)))
(Hlgood_lock:  forall l : lock,
   locks l (init_state (instrument P 0)) ->
   good_lock (l, 0) (init_state (instrument P 0)))
  (Hspawn_wait_other: spawn_wait_other_prog (init_state P))
  (Hinit: forall p : ptr, initialized m0 p)
  (Hclocks_sim: clocks_sim m0 s0),
  (exists ops2 m2 G2',
    exec_star (Some (init_state (instrument P 0))) init_env ops2 m2 None G2' /\
    consistent (m0 ++ m2)) <->
  (exists ops m1 P' G' s' t o c P'' G'',
     exec_star (Some (init_state P)) init_env ops m1 (Some P') G' /\
     step_star s0 ops s' /\ exec P' G' t (Some o) c (Some P'') G'' /\
     consistent (m0 ++ m1 (*++ opt_to_list c*)) /\ forall s'', ~step s' o s'').
Proof.
  intros. split.
  - intros (ops2 & m2 & G2' &Hexec_star_inst&  Hcon_m02).
   rewrite exec_rev in Hexec_star_inst. inversion Hexec_star_inst; clarify.
   rewrite <- exec_rev in *; clear Hexec_star_inst. 
   inversion Hexec'; clarify.
   exploit exec_fail_iexec; eauto.
   { unfold init_state; constructor; auto. }
   { constructor; auto. }
   { unfold init_state; constructor; auto. }
   { constructor; auto; simpl; omega. }
   { apply exec_refl. } Check exec_fail_iexec.
   intro X; exploit X; clear X; eauto.
   clarify.
   exploit state_sim_steps'. 
   { instantiate(1:=(init_state (instrument P 0))).
     unfold distinct, init_state; constructor; clarify. }
   { instantiate(1:= init_state P).
     unfold state_sim, init_state; clarify. }
   { auto. }
   { auto. }
   { eauto. }
   { auto. }
   intros (P1' & Hstate_simP1'2' & Hsafe_locsP1' & Hfresh_tmpsP1' & Hlegal_tidsP1').
   exploit distinct_steps.
   { instantiate (1:= init_state (instrument P 0)).
     unfold distinct, init_state; constructor; clarify. }
   { apply iexec_star_exec_star; eauto. }
   intro HdistinctP2'.
   exploit instrument_sim_race2.
   { instantiate (1:=P). auto. }
   { auto. }
   { auto. }
   { instantiate(1:=P1'). auto. }
   { auto. }
   { unfold legal_tids in Hlegal_tidsP1'. clarify. }
   { eauto. }
   { auto. }
   { apply env_sim_refl. }
   { eauto. }
   { eauto. }
   { eauto. }
   { auto. }
   { eauto. }
   intros (o1' & ops1 & m1 & c1' & P1'' & G1s' & G1''  & Hmon).
   destruct Hmon as (Hexec_starP1' & Henv_simG1' & HexecP1'' & Hcon_m01
                     & Hmem_valsm012 & s' & Hss_s' & Hrace); clarify.
   destruct o1'.
   do 11 eexists; eauto.
   repeat (split; eauto).
   simpl in *; repeat intro.
   eapply Hrace; econstructor; eauto; constructor.
   { exfalso; eapply Hrace; constructor. }
  -intros (ops1 & m1 & P1_good & G1_good & s & t & o & c & P'' & G'' &
     Hexec & Hops & Hexec_race & Hcon_m01 & Hnostep).
   exploit instrument_sim_race; try apply Hexec_race; eauto.
   { eapply fresh_tmps_steps; eauto. }
   { eapply safe_locs_steps; eauto. }
   { eapply legal_tids_steps in Ht; eauto.  }
   { rewrite <- distinct_suffix; [|apply sim_suffix, instrumented].
     eapply distinct_steps; eauto.
     constructor; auto. }
   { apply instrumented. }
   { apply env_sim_refl. }
   { simpl; repeat intro.
     inversion H; clarify.
     eapply Hnostep; eauto. }
   intros (ops2' & m2s & lo & lc & G2s & G2' & Hexec_starP2good & Hexec_race2 &
           Hcon_m02s & Hmem_vals_m12s & Henv_sim_G12s ).
   do 4 eexists; [eapply exec_star_trans; eauto | auto].
Qed.

End Sim_Proofs.
