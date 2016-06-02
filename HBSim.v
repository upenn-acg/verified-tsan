Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import FunctionalExtensionality.
Require Import HBRaceDetector.
Require Import SCFacts.
Require Import ExecFacts.
Require Import HBReorder.
Set Implicit Arguments.

Section Sim_Proofs.

Context (ML : @Memory_Layout var nat _).

Context (meta : metadata).

Notation C' := C.
Notation L' := L.
Notation R' := R.
Notation W' := W.
Notation X' := X.

(* can be replaced with init *)
Hypothesis Hs_x : forall (x0 : nat) m ,
         x0 < zv -> can_read m (X + x0, 0) 0 /\ can_write m (X + x0, 0).


Hint Resolve Htmp.

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
    { constructor; clarify.  specialize(Hmetalocs_disjoint_CX H Hx2).
      repeat intro; clarify. }
   +apply can_write_SC; auto.
    { constructor; clarify. }
  -unfold clock_match. intros.
   destruct (lt_dec t zt); simpl.
   specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t).
   split; auto.
   +apply can_read_SC; clarify.
    apply acq_con; auto.
    { constructor; clarify. }
    { constructor; clarify. specialize(Hmetalocs_disjoint_LX H Hx2).
      repeat intro; clarify. }
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
     { constructor; clarify. specialize(Hmetalocs_disjoint_RX H Hx2).
       repeat intro; clarify. }
     
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
     { constructor; clarify. specialize (Hmetalocs_disjoint_WX H Hx2).
       repeat intro; clarify. }
     
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
  (Htmps : fresh_tmps P1) (Hiexec : iexec P2 G2 t lo lc P2' G2'),
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
    rewrite (safe_instrs(meta := meta)) in *.
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
    assert (Forall safe_instr x) by (rewrite <- safe_instrs; auto).
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


Lemma upd_three : forall G t a1 a2 v1 v2 v1' (Hdiff : a1 <> a2),
  upd_env (upd_env (upd_env G t a1 v1) t a2 v2) t a1 v1' =
  upd_env (upd_env G t a1 v1') t a2 v2.
Proof.
  intros; rewrite upd_assoc, upd_overwrite; auto.
Qed.

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
    exists (v1 :: vs1), (v2 :: vs2), (S k).
  rewrite <- leb_le in l.  
  rewrite last_cons, last_cons. do 2 rewrite last_cons'; auto.
  try (intro; clarify; omega).
  clarify.
  split; [omega | clarify].
  rewrite upd_overwrite, upd_same.
  rewrite upd_three, upd_old, upd_same, upd_assoc; auto.
  (* do 2 rewrite last_cons'; auto. *)
  split; auto.
  rewrite leb_le in cond; destruct i; clarify.
  eapply Hle; eauto; omega.
  intro Habsurd. rewrite Habsurd in H8. simpl in H8. clarify.
  setoid_rewrite <- H8 in H61. inversion H61.
  intro Habsurd. rewrite Habsurd in *.   rewrite <- H7 in H6. simpl in H6.
  inversion H6. inversion H10.
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
 (* { eapply consistent_app_SC; eauto. } *)
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
  o c G4(* i li (Hin0 : In (t, i :: li) P')
  (Hin : In (t, last (instrument_instr i t) (Lock 0) :: instrument li t) P3)*)
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


Lemma suffix_threads : forall P P1 P2 (Hsuffix1 : state_suffix P P1)
  (Hsuffix2 : state_suffix P P2), map fst P1 = map fst P2.
Proof.
  induction P; clarify; inversion Hsuffix1; inversion Hsuffix2; clarify.
  destruct a; clarify.
  erewrite IHP; eauto; clarsimp.
Qed.

Lemma state_suffix_inv2 : forall P1a P1b P2a P2b t li li'
  (Hsuffix : state_suffix (P1a ++ (t, li) :: P1b) (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  state_suffix P1a P2a /\ state_suffix P1b P2b /\
  exists n, n < length (instrument_instr (hd (Assign 0 (I 0)) li) t) /\
      li' = skipn n (instrument li t).
Proof.
  induction P1a; clarify.
  - destruct P2a; clarify.
    + inversion Hsuffix; clarify.
      split; [constructor | clarify; eauto].
    + inversion Hsuffix; clarify.
      generalize (NoDup_inj(x := fst p) 0 (S (length (map fst P2a))) Hdistinct);
        clarify.
      rewrite map_app in *; simpl in *; rewrite nth_error_split in *; clarify.
  - destruct P2a; clarify.
    + inversion Hsuffix; clarify.
      assert (nth_error (a :: P1a ++ (fst a, li) :: P1b) (S (length P1a)) =
        Some (fst a, li)) by (simpl; apply nth_error_split).
      exploit Forall2_nth; eauto.
      { destruct a; clarify; eauto. }
      intros (? & Hnth & ?).
      generalize (NoDup_inj(x := fst a) 0 (S (length P1a)) Hdistinct);
        clarify.
      erewrite map_nth_error in *; eauto; clarify.
      destruct a; clarify.
    + inversion Hsuffix; clarify.
      inversion Hdistinct; clarify.
      exploit IHP1a; eauto; clarify.
      split; [constructor; auto | clarify; eauto].
Qed.  

(* up? *)
Lemma instr_access : forall i i0 t n
  (Hin : nth_error (instrument_instr i0 t) n = Some i)
  p (Haccess : accesses i = Some p) (Hmeta : ~meta_loc p)
  (Hsafe : safe_instr i0) (Ht : t < zt)
  (Hwait : match i0 with Wait u => u < zt | _ => True end), i = i0 /\
  match i0 with Load _ p' | Store p' _ => p = p' /\
    n = length (instrument_instr i0 t) - 2
  | Lock l => p = (l, 0) /\ n = 0
  | Unlock l => p = (l, 0) /\ n = length (instrument_instr i0 t) - 1
  | _ => False end.
Proof.
  destruct i0; try destruct x; clarify.
  - rewrite nth_error_single in *; clarify.
  - destruct n0; clarify.
    { contradiction Hmeta; apply X_meta; auto. }
    exploit nth_error_app'; eauto; intros [? | ?]; clarify.
    { contradiction Hmeta; exploit nth_error_in; eauto; rewrite in_app;
        intros [? | ?].
      + exploit hb_check_instrs; eauto; clarify.
        destruct H02; clarify; [apply W_meta | apply C_meta]; auto.
      + destruct H; clarify; [apply C_meta | apply R_meta]; auto. }
    rewrite nth_error_two in H2; destruct H2; clarify.
    rewrite app_length; simpl.
    repeat rewrite <- plus_n_Sm; simpl.
    destruct (le_lt_eq_dec _ _ H1); [omega | clarify].
    { contradiction Hmeta; apply X_meta; auto. }
  - destruct n0; clarify.
    { contradiction Hmeta; apply X_meta; auto. }
    exploit nth_error_app'; eauto; intros [? | ?]; clarify.
    { contradiction Hmeta; exploit nth_error_in; eauto; repeat rewrite in_app;
        intros [? | [? | ?]].
      + exploit hb_check_instrs; eauto; clarify.
        destruct H02; clarify; [apply W_meta | apply C_meta]; auto.
      + exploit hb_check_instrs; eauto; clarify.
        destruct H02; clarify; [apply R_meta | apply C_meta]; auto.
      + destruct H; clarify; [apply C_meta | apply W_meta]; auto. }
    rewrite nth_error_two in H2; destruct H2; clarify.
    rewrite app_length; simpl.
    repeat rewrite <- plus_n_Sm; simpl.
    destruct (le_lt_eq_dec _ _ H1); [omega | clarify].
    { contradiction Hmeta; apply X_meta; auto. }
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
    contradiction Hmeta; destruct H02 as [? | [? | ?]]; clarify.
    + apply L_meta; auto.
    + apply C_meta; auto.
    + apply C_meta; auto.
  - exploit nth_error_app'; eauto; intros [? | ?].
    { contradiction Hmeta; unfold unlock_handler in H; clarify.
      exploit nth_error_in; eauto; rewrite in_app; intros [? | ?].
      + exploit set_vc_instrs; eauto; clarify.
        destruct H02; clarify; [apply C_meta | apply L_meta]; auto.
      + destruct H; clarify; apply C_meta; auto. }
    rewrite nth_error_single in *; clarify.
    rewrite app_length; simpl; omega.
  - exploit nth_error_in; eauto; unfold spawn_handler; repeat rewrite in_app;
      intros [[? | ?] | ?]; clarify; contradiction Hmeta.
    + exploit max_vc_instrs; eauto; clarify.
      destruct H02 as [? | [? | ?]]; clarify; apply C_meta; auto.
    + destruct H; clarify; apply C_meta; auto.
  - destruct n; clarify.
    exploit nth_error_in; eauto; setoid_rewrite in_app; intros [? | ?];
      contradiction Hmeta.
    + exploit max_vc_instrs; eauto; clarify.
      destruct H02 as [? | [? | ?]]; clarify; apply C_meta; auto.
    + destruct H; clarify; apply C_meta; auto.
  - rewrite nth_error_single in Hin; clarify.
Qed.

Lemma iexec_step_inv : forall P G lo lc P' G' t o c P'' G''
  (Hsteps : iexec_star P G lo lc P' G') (Hstep : iexec P' G' t o c P'' G''),
  iexec_star P G (lo ++ o) (lc ++ c) P'' G''.
Proof.
  intros until G''; intro; induction Hsteps; clarify.
  - eapply iexec_step'; eauto; try apply iexec_refl; clarsimp.
  - repeat rewrite <- app_assoc; eapply iexec_step; eauto.
Qed.

Corollary instrument_indep_n' : forall P0 G0 t o c P G lo lc P1 G1 P2 G2 i rest
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
  m (Hcon : consistent (m ++ lc0 ++ opt_to_list c ++ lc))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t) (opt_to_list c ++ lc)))
         (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros; rewrite exec_rev in Hsteps; inversion Hsteps; clarify.
  rewrite <- exec_rev in Hexec; generalize (exec_step Hstep1 Hexec); intro HP.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; eauto; intros (n' & Hin1).
  destruct (eq_dec t0 t).
  - rewrite skipn_app in Hin1.
    destruct (le_lt_dec (length (instrument_instr i t)) n').
    { rewrite skipn_all in Hin1; auto.
      exploit distinct_steps; eauto; intro.
      subst; exploit step_thread; eauto; intros (? & ? & Heq & ?).
      exploit distinct_step; eauto; intro.
      exploit distinct_in; [eauto | eauto | apply Hin' | clarify].
      rewrite <- (firstn_skipn (n' - length (instrument_instr i t)) rest) in Heq
        at 2.
      rewrite app_assoc in Heq; exploit cons_app_neq; eauto; contradiction. }
    rewrite le_minus_0 in Hin1; [|omega].
    eapply instrument_indep_n; try apply Hsim; eauto.
  - eapply instrument_indep_n; try apply Hsim; eauto.
    exploit distinct_steps; eauto; intro.
    exploit exec_other_thread'; try apply Hexec'; eauto; intro Heq.
    rewrite Heq in *; auto.
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
(*  (Hinit_l : forall l, l < zl -> initialized m0 (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m0 (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m0 (C + t, o))*)
  (Hinit : forall p, initialized m0 p),
  exists lo1' lc1' P1' G1' lo2' lc2', iexec_star P G lo1' lc1' P1' G1' /\
    fail_iexec P1' t lo2' lc2' /\ consistent (m0 ++ lc0 ++ lc1' ++ lc2') /\ 
    mem_vals (m0 ++ lc0 ++ lc) (m0 ++ lc0 ++ lc1') /\ env_sim G' G1'.
Proof.
  intros.
  exploit exec_iexec1'; try apply Hexec; try apply Hroot; eauto.
  { eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto. }
  intros (? & lc'1 & ? & P2 & ? & lc'2 & ? & ? & ? & ? & Hiexec & Hrest & Hext);
    clarify.
  exploit fail_safe; try apply Hrest; eauto.
  { apply instrumented. }
  { eapply exec_star_trans; eauto.
    apply iexec_execs; eauto. }
  intro X; exploit X; clear X; eauto.
  { inversion Hfail; subst; rewrite app_nil_r in *.
    destruct Hext as (Hext & _).
    specialize (Hext []); repeat rewrite app_nil_r in *.
    rewrite <- Hext in *; repeat rewrite app_assoc in *; eauto. }
  clarify; repeat rewrite <- app_assoc in *.
  exploit iexec_trans; try apply Hiexec; eauto; intro.
  do 7 eexists; eauto; split; eauto.
  split; [rewrite <- app_assoc; auto | split; auto].
  rewrite <- (mem_vals_ext _ Hext); auto.
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
  {
    eapply consistent_app_SC. rewrite <- app_assoc; simpl; eauto. }

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
    exploit consistent_app_SC; eauto; intro.
    eapply can_read_unique; eauto.
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



Definition clock_match_z m V x z:= forall t,
  if lt_dec t z then can_read m (x, t) (V t) /\ can_write m (x, t)
  else True.

   
Lemma clock_match_mods_z: forall m vr r t t' v x f z (Hclock_match_m: clock_match_z m (vr x) (r+x) z)
                              (Hcon: consistent (m++[Write t' (r+x,t ) v])) (Ht: t < z)
                          (* (Hbounded: bounded f z)*)
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
  (*(Hbounded1: bounded (vc1 t1) z) (Hbounded2: bounded (vc2 t2) z)*)
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



Lemma hb_check_vals1' : forall m C1 C2 z vs1 vs2 t V1 V2 v1 v2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t))
  (Hvs1 : length vs1 <= z) (Hvs2 : length vs2 <= z) (*(Hlens: length vs1 = length vs2)*) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hgt : first_gt  vs1 vs2 = Some (v1, v2)),
   ~ vc_le V1 V2 .
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


Lemma consistent_mem_vals: forall m1 m2 c
     (Hinit: initialized m1 (loc_of c)) (Hm1: consistent m1) (Hcon: consistent (m2++[c])) (Hmem_vals: mem_vals m1 m2) (Hmeta: ~ meta_loc (loc_of c)) (Hprog: prog_op c),
                                     consistent (m1++[c]).
Proof.
  intros.
  unfold mem_vals in Hmem_vals.
  specialize (Hmem_vals (loc_of c) Hmeta Hinit).
  destruct c; clarify.
  -apply can_read_thread. rewrite Hmem_vals. eapply can_read_thread'. eauto.
  -apply can_write_thread. apply init_can_write; auto.
  -apply can_arw_SC.
   +apply ARW_can_read in Hcon. rewrite Hmem_vals. auto.
   +apply init_can_write; auto.
Qed.

Lemma consistent_mem_vals': forall m1 m2 c
     (Hinit1: initialized m1 (loc_of c)) (Hinit2: initialized m2 (loc_of c)) (Hm2: consistent m2) (Hcon: consistent (m1++[c])) (Hmem_vals: mem_vals m1 m2) (Hmeta: ~ meta_loc (loc_of c)) (Hprog: prog_op c),
                              consistent (m2++[c]).
Proof.
  intros.
  unfold mem_vals in *.
  specialize (Hmem_vals (loc_of c) Hmeta Hinit1).
  destruct c; clarify.
  -apply can_read_thread. rewrite <- Hmem_vals. eapply can_read_thread'. eauto.
  -apply can_write_thread. apply init_can_write; auto.
  -apply can_arw_SC.
   +apply ARW_can_read in Hcon. rewrite <- Hmem_vals. auto.
   +apply init_can_write; auto.
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

Hint Resolve Hmetalocs_disjoint_CL.
Hint Resolve Hmetalocs_disjoint_CX.

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



Lemma clocks_sim_writeR: forall c l r w m m' (s s': vstate) t t' v x
  (Hsim: clocks_sim m s) (Ht: t < zt) (Hcon: consistent m') (Hx: x < zv)
  (Hs: s= (c,l,r,w)) (Hs': s'=(c,l,upd r x (upd (r x) t v),w)) 
  (Hm': m'=(m++[Write t' (R'+x, t) v])) ,
                           clocks_sim m' s'.
Proof.
  unfold clocks_sim in *. clarify.
  assert (Forall prog_op [Write t' (R' + x, t) v]) as Hprog_op.
  { rewrite Forall_forall. clarify. }
  split;[|split;[|intros; split]]; intros.
  -apply clock_match_nomod; clarify. repeat constructor. apply Hmetalocs_disjoint_CR; auto.
  -apply clock_match_nomod; auto. repeat constructor. apply Hmetalocs_disjoint_LR; auto.
  -try specialize(Hsim22 v0 H); clarify.
   destruct (eq_dec v0 x).
   +clarify. apply clock_match_mods; auto.
   +apply clock_match_nomod; auto.
    *assert(upd r x (upd (r x) t v) v0 = r v0) as Hrv0.
     { unfold upd. clarify. }
     rewrite Hrv0. auto.
    *rewrite Forall_forall.
     intros x0 Hin; destruct x0; clarify; destruct x0; inversion H0; clarify.
     omega.
  -try specialize(Hsim22 v0 H); clarify. apply clock_match_nomod; clarify.
   repeat constructor. apply Hmetalocs_disjoint_WR; auto.
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
   rewrite Forall_forall; intros x0 Hin; destruct x0; clarify. destruct x0; inversion H0; clarify. apply Hmetalocs_disjoint_CW; auto. 
  -apply clock_match_nomod; clarify. repeat constructor. apply Hmetalocs_disjoint_LW; auto.
  -apply clock_match_nomod; auto. repeat constructor.  intro Habsurd. symmetry in Habsurd.
   eapply Hmetalocs_disjoint_WR.
   { apply Hx. } { apply H.  } { auto. }
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

Hint Resolve Hmetalocs_disjoint_CX.
Hint Resolve Hmetalocs_disjoint_WX.
Hint Resolve Hmetalocs_disjoint_RX.

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
           apply in_mops_hb_check in Hin;destruct x0; clarify. 
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
   { do 2 rewrite app_assoc. apply mem_vals_sim_app; auto.
     -eapply prog_steps; eauto.
      instantiate(1:=G1'). instantiate(1:=(Some P1')). instantiate(1:= opt_to_list o1).
      assert(opt_to_list o1=opt_to_list o1 ++[]) as Hnilr1.
      { rewrite app_nil_r; auto. }
      assert(opt_to_list c1=opt_to_list c1 ++[]) as Hnilr2.
      { rewrite app_nil_r; auto. }
      rewrite Hnilr1,Hnilr2. eapply exec_step; eauto. constructor.
     -apply Forall_app in Hprog_m2c2. clarify.
     -rewrite <-app_assoc. eapply consistent_app_SC; eauto.
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
Hint Resolve Hmetalocs_disjoint_WX.
   
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
           { apply can_release_SC; auto.  }
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
       { rewrite Forall_forall. intros x0 Hx0. inversion Hx0; clarify.
         intro Habsurd. inversion Habsurd; clarify. specialize(Hmetalocs_disjoint_WX Hx2 Hx2). clarify. intro Habsurd. contradiction Hx1. setoid_rewrite Habsurd. 
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
               apply init_can_write. apply init_steps; auto.
               eapply consistent_app_SC; eauto.
               constructor; simpl; auto. }  
         -rewrite <- app_assoc. apply loc_valid_ops1_SC.
          +rewrite Forall_forall.  intros x0 Hx0. rewrite in_app in Hx0. clarify.
           intro Heq.
           symmetry in Heq;destruct Hx0; clarify;
           apply in_mops_hb_check in H; destruct x0; clarify; inversion H; clarify.
           *specialize(Hmetalocs_disjoint_WX Hx2 Hx2); clarify.
           *specialize(Hmetalocs_disjoint_CX H3 Hx2); clarify.
           *specialize(Hmetalocs_disjoint_RX Hx2 Hx2); clarify.
           *specialize(Hmetalocs_disjoint_CX H3 Hx2); clarify.
          +simpl; auto.
          +rewrite Forall_app; auto.
          +split; clarify.
           apply can_release_SC. auto. }
      *apply can_read_thread. apply can_read_SC.
       { apply can_read_SC.
        - specialize(Hs_c t0 H3).
          unfold clock_match in Hs_c. 
          specialize(Hs_c t0). clarify.
        -apply can_arw_SC; specialize(Hs_x (m0++m2) Hx2);
          inversion Hx2; clarify.
        -constructor; simpl; auto.
        -rewrite Forall_forall; intros; clarify.
         intro Habsurd. inversion Habsurd.
         exploit (Hmetalocs_disjoint_CX H3 Hx2); eauto. }
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
  intros s1 s2 lo Hstep_star. (*generalize dependent s1.*)
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

Lemma first_gt_decompose: forall vs1 vs2 v1 v2 ,first_gt vs1 vs2 = Some (v1, v2) ->
                                                exists pre_vs1 pre_vs2 suf_vs1 suf_vs2,
                                                  vs1=pre_vs1++v1::suf_vs1 /\
                                                  vs2=pre_vs2++v2::suf_vs2 /\
                                                  length pre_vs1 = length pre_vs2 /\
                                                  first_gt pre_vs1 pre_vs2 = None.
Proof.
  clarify.
  generalize dependent vs2.
  induction vs1; clarify.
  destruct vs2; clarify.
  destruct (a <=? n) eqn: Hle; clarify.
  -specialize(IHvs1 vs2 H).
   destruct IHvs1 as (pre_vs1 & pre_vs2 & suf_vs1 & suf_vs2 & Hnb).
   destruct Hnb as (Hvs1 & Hvs2 & Hlen & Hfg_pre).
   exists (a::pre_vs1), (n::pre_vs2), suf_vs1, suf_vs2. clarify.
  -exists [],[],vs1, vs2. clarify.
Qed.

Lemma first_gt_ignore: forall vs1 vs2 pre_vs1 pre_vs2 suf_vs1 suf_vs2
                              (Hvs1: vs1=pre_vs1++suf_vs1) (Hvs2: vs2=pre_vs2 ++ suf_vs2)
                              (Hlen: length pre_vs1 = length pre_vs2)
                              (Hfirst_gt: first_gt pre_vs1 pre_vs2 = None),
                         first_gt vs1 vs2 = first_gt suf_vs1 suf_vs2.
Proof.
  clarify.
  generalize dependent pre_vs2. 
  induction pre_vs1; destruct pre_vs2; clarify.
Qed.

Lemma events_hb_check_app: forall C1 C2 vs1 vs2 t pre_vs1 pre_vs2 suf_vs1 suf_vs2
                              (Hvs1: vs1=pre_vs1++suf_vs1) (Hvs2: vs2=pre_vs2 ++ suf_vs2)
                              (Hlen: length pre_vs1 = length pre_vs2)
                              (Hpre: first_gt pre_vs1 pre_vs2=None),
                             events_hb_check C1 C2 vs1 vs2 t = events_hb_check C1 C2 pre_vs1 pre_vs2 t ++
                                                                               events_hb_check C1 C2 suf_vs1 suf_vs2 t.
Proof.
  intros.
  generalize dependent pre_vs2. generalize dependent vs1. generalize dependent vs2.
  induction pre_vs1; destruct pre_vs2; clarify.
  specialize (IHpre_vs1 (pre_vs2++suf_vs2) (pre_vs1++suf_vs1)). clarify.
  specialize (IHpre_vs1 pre_vs2). clarify.
  setoid_rewrite IHpre_vs1. auto.
Qed.
  
Lemma events_hb_check_decompose: forall C1 C2 vs1 vs2 t pre_vs1 pre_vs2 v1 v2 suf_vs1 suf_vs2
                                        (Hvs1: vs1=pre_vs1++v1::suf_vs1)
                                        (Hvs2: vs2=pre_vs2++v2::suf_vs2)
                                        (Hlen: length pre_vs1 = length pre_vs2)
                                        (Hpre: first_gt pre_vs1 pre_vs2=None)
                                        (Hv1v2: v1 > v2),         

                                   events_hb_check C1 C2 vs1 vs2 t =
                                   events_hb_check C1 C2 pre_vs1 pre_vs2 t++
                                                   events_hb_check C1 C2 [v1] [v2] t.
Proof.
  intros.
  rewrite events_hb_check_app with (suf_vs1:=v1::suf_vs1) (suf_vs2:=v2::suf_vs2)
                                                          (pre_vs1:=pre_vs1) (pre_vs2:=pre_vs2); clarify.
  apply leb_le in cond. apply le_not_gt in cond. clarify.
Qed.
  
Print mops_hb_check.

Fixpoint mops_hb_check2 (C1 C2: var) (vs1 vs2: list nat) (z m:nat) (t:tid) : list conc_op :=
match (z,m, vs1,vs2) with
| (S n, S c, v1::vss1, v2::vss2) => mops_assert_le (C1,n) (C2,n) v1 v2 t ++ 
                               (if leb v1 v2 then mops_hb_check2 C1 C2 vss1 vss2 n c t
                               else [])
| _ => []
end.


Lemma assert_le_fail_spec': forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
                                   Pgood Ggood
  (HPgood: Pgood=P1++(t,Assert_le (V tmp1) (V tmp2)::rest)::P2)
  (HGgood: Ggood=(upd_env (upd_env G t tmp1 v1) t tmp2 v2)) 
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: ~ v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t) (Some Pgood) Ggood /\
   exec Pgood Ggood t None None None Ggood.
Proof.
  intros.
  rewrite Hassert_le_spec.
  rewrite HPgood, HGgood; clarify.
  split.
  -eapply exec_step'.
   +eapply exec_load; eauto.
   +eapply exec_step'; eauto.
    *eapply exec_load; eauto.
    *eapply exec_refl.
   +unfold events_assert_le; clarify.
   +unfold mops_assert_le; clarify.
  -eapply exec_assert_fail; eauto.
   simpl. rewrite upd_same, upd_assoc; auto.
   rewrite upd_same. auto.
Qed.



Lemma hb_check_fail_spec_n': forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)) Ggood
 (HGgood: Ggood=(upd_env (upd_env G t tmp1 v1) t tmp2 v2)),
                               exists c Pgood, c< S n /\
                                 Pgood=P1++(t,Assert_le (V tmp1) (V tmp2)::hb_check C1 C2 (S n -c-1) tmp1 tmp2 ++rest)::P2  /\
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
 (mops_hb_check C1 C2 vs1 vs2 (S n) t) (Some Pgood) Ggood
 /\ exec Pgood Ggood t None
           None None Ggood. 
Proof.
  intros.
  exploit first_gt_decompose; eauto.
  intros (pre_vs1 & pre_vs2 & suf_vs1 & suf_vs2 & Hfvs1 & Hfvs2& Hlen & Hfgt_pre).
  exists (length pre_vs1),  (P1 ++ (t,Assert_le (V tmp1) (V tmp2)
                                                :: hb_check C1 C2 (S n - (length pre_vs1)-1) tmp1 tmp2 ++ rest) :: P2).
  clarify.
  generalize dependent n. generalize dependent pre_vs2.
  generalize dependent G.
  induction pre_vs1;intros.
  -rewrite app_length in *. symmetry in Hlen.  apply empty_list in Hlen. 
   subst. repeat rewrite app_nil_l in *. apply first_gt_spec in Hfirst_gt. inversion Hfirst_gt. clarify.
   destruct (leb v1 v2) eqn: Hleb; clarify.
   +rewrite leb_le in Hleb. apply le_not_gt in Hleb. clarify.
   + split; clarify.
    *eapply exec_step'; eauto.
     { Check exec_load.
       apply exec_load with (v:=v1); eauto. }
     { eapply exec_step'; eauto.
       -apply exec_load with (v:=v2); eauto.
       -rewrite <- minus_n_O. eapply exec_refl; eauto. }
     { simpl. eauto. }
     { eauto. }
    *Check assert_le_fail_spec'. eapply assert_le_fail_spec' with (a:=C1) (b:=C2) (i:=x0) (j:=x0); eauto. 
     apply gt_not_le. auto.
  -destruct pre_vs2; clarify.
   inversion Hlen. specialize(IHpre_vs1 (upd_env (upd_env G t tmp1 a) t tmp2 n0)).
   specialize(IHpre_vs1 pre_vs2 H0 Hfgt_pre Hfirst_gt).
   assert(Hn2: length (pre_vs2 ++ v2 :: suf_vs2) = S (length pre_vs2 + length suf_vs2)).
   { rewrite app_length.  clarify. }
   assert(Hn1: length (pre_vs1 ++ v1 :: suf_vs1) = S (length pre_vs2 + length suf_vs2)).
   { rewrite <- Hvs1 in Hvs2.  repeat rewrite app_length in Hvs2. clarify. inversion Hvs2.
     rewrite app_length. clarify. rewrite <- H1. omega. }
   specialize(IHpre_vs1 (length pre_vs2 + length suf_vs2) Hn2 Hn1).
   assert(Hn: n=length (pre_vs2 ++ suf_vs2) +1).
   { inversion Hvs2. repeat rewrite app_length in *.   clarify. omega. }
   split;[|split;[|split]]; clarify.
   +omega.
   +assert(Hlen_before: length pre_vs2 + length suf_vs2 + 1 = S(length pre_vs2 + length suf_vs2 )) by omega.
     eapply exec_step'; eauto.
      { instantiate (1:=(upd_env G t tmp1 a)).
        eapply exec_load with (v:=a); eauto. }
     { eapply exec_step'; eauto.
       -instantiate (1:=upd_env (upd_env G t tmp1 a) t tmp2 n0).
         eapply exec_load with (v:=n0); eauto.
       -eapply exec_step; eauto.
        +eapply exec_assert_pass; eauto. simpl.
         rewrite upd_same; rewrite upd_assoc; auto. rewrite upd_same; auto.
         apply leb_le; auto.
        +assert(HG: (upd_env
                    (upd_env (upd_env (upd_env G t tmp1 a) t tmp2 n0) t tmp1
                             v1) t tmp2 v2) =
                    (upd_env (upd_env G t tmp1 v1) t tmp2 v2)).
         { rewrite upd_assoc, upd_overwrite; clarify.
           rewrite upd_assoc, upd_overwrite; clarify. }
         rename IHpre_vs1221 into IHexecs.
         rename IHpre_vs1222 into IHexec.
         rewrite HG in IHexecs.
         rewrite app_length. clarify.
         
         rewrite Hlen_before. simpl. apply IHexecs.
     }
     { clarify. }
     { clarify. rewrite <- Hlen_before, app_length. auto.  }
    +eapply exec_assert_fail; eauto.
     simpl. rewrite upd_same. rewrite upd_assoc; eauto. rewrite upd_same.
     apply first_gt_spec in Hfirst_gt. apply gt_not_le. clarify.
Qed.
    

Corollary hb_check_fail_spec': forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2
  vs1 vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)) Ggood
   (HGgood: Ggood=(upd_env (upd_env G t tmp1 v1) t tmp2 v2)),
                               exists c Pgood,
                                 c < n /\
   Pgood=P1++(t,Assert_le (V tmp1) (V tmp2)::hb_check C1 C2 (n -c-1) tmp1 tmp2 ++rest)::P2  /\
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
 (mops_hb_check C1 C2 vs1 vs2 n t) (Some Pgood) Ggood
 /\ exec Pgood Ggood t None
           None None Ggood. 
Proof.
  destruct n; intros.
  - destruct vs1, vs2; clarify.
  -eapply hb_check_fail_spec_n'; eauto.
Qed.

Lemma load_handler_race_spec' : forall (n x t : nat) (P : list (nat * list instr)) 
         (G : env) (P1 P2 : list (nat * list instr)) 
         (rest : list instr) (vs1 vs2 : list nat)
       (HP: P = P1 ++ (t, load_handler t x n ++ rest) :: P2 )
       (Hlen1: length vs1 = n ) (Hlen2: length vs2 = n)
       v1 v2 (Hfirst_gt: first_gt vs1 vs2 = Some (v1, v2) )
        Ggood (HGgood: Ggood=(upd_env (upd_env G t tmp1 v1) t tmp2 v2)),
                                exists c Pgood, c < n /\
   Pgood=P1++(t,Assert_le (V tmp1) (V tmp2)::hb_check (W'+x) (C' + t) (n -c-1) tmp1 tmp2++
   Load tmp1 (C' + t, t) :: Store (R' + x, t) (V tmp1) :: rest )::P2 /\
       exec_star (Some P) G
         (acq t (X' + x) :: events_hb_check (W' + x) (C' + t) vs1 vs2 t)
         (Acq t (X' + x) :: mops_hb_check (W' + x) (C' + t) vs1 vs2 n t) (Some Pgood)
         (upd_env (upd_env G t tmp1 v1) t tmp2 v2) /\
       exec Pgood Ggood t None None None Ggood.
Proof.
  intros. unfold load_handler in *. clarify.
  exploit hb_check_fail_spec'.
  { instantiate(1:= P2). instantiate(1:= move (C' + t, t) (R' + x, t) tmp1 ++ rest).
    instantiate(1:= tmp2). instantiate(1:=tmp1). instantiate(1:=length vs1).
    instantiate(1:= C' +t ). instantiate(1:= W'+x). instantiate(1:=t).
    instantiate(1:= P1). eauto. }
  { eauto. }
  { instantiate(1:= vs1). auto. }
  { eauto. }
  { eauto. }
  { eauto. }
  intros ( c & Pgood & HPgood & Hexecs & Hexec).
  exists c, Pgood. 
  split;[|split;[|split]];clarify.
  -eapply exec_step'; eauto.
   +eapply exec_lock. rewrite <- app_assoc. clarify. 
   +clarify.
   +clarify.
  -clarify.
Qed.

Lemma store_handler_race_waw_spec': forall n x t P G P1 P2 rest v1 v2 vs1 vs2
 (Hstore_handler_spec: P= P1++(t,store_handler t x  n++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2))
 Ggood (HGgood : Ggood= (upd_env (upd_env G t tmp1 v1) t tmp2 v2) ),
                                    exists c Pgood, c < n /\
   Pgood=P1++(t,Assert_le (V tmp1) (V tmp2)::hb_check (W'+x) (C' + t) (n -c-1) tmp1 tmp2++
                          hb_check (R' + x) (C' + t) (length vs1) tmp1 tmp2 ++
                          Load tmp1 (C' + t, t) :: Store (W' + x, t) (V tmp1) :: rest )::P2 /\
 exec_star (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           (Some Pgood) Ggood /\
 exec Pgood Ggood t None None None Ggood.
Proof.
  intros. unfold store_handler in *. clarify.
  exploit hb_check_fail_spec'.
  { instantiate(1:= P2). instantiate(1:=hb_check (R' + x) (C' + t) (length vs1) tmp1 tmp2 ++
                                                 move (C' + t, t) (W' + x, t) tmp1 ++ rest).
    instantiate(1:=tmp2). instantiate(1:=tmp1). instantiate(1:=length vs1).
    instantiate(1:= C'+ t). instantiate(1:= W' + x). instantiate(1:=t).
    instantiate(1:= P1). eauto. }
  { eauto. }
  { instantiate(1:=vs1). auto. }
  { eauto. }
  { eauto. }
  { instantiate (1:= G). eauto. }
  intros ( c & Pgood & Hc & HPgood & Hexecs & Hexec).
  exists c, Pgood.
  split; [|split]; clarify.
  eapply exec_step'; eauto.
  -eapply exec_lock. do 2 rewrite <- app_assoc. eauto.
  -clarify.
  -clarify.
Qed.

Lemma store_handler_race_war_spec': forall n x t P G P1 P2 rest v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x n ++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 = n) 
 (Hfirst_gt12: first_gt vs1 vs2 = None)
 (Hfirst_gt32: first_gt vs3 vs2 = Some (v3,v2))
Ggood (HGgood : Ggood= (upd_env (upd_env G t tmp1 v3) t tmp2 v2) ),
                                   exists c Pgood, c < n /\
 Pgood=P1++(t,Assert_le (V tmp1) (V tmp2)::hb_check (R'+x) (C' + t) (n -c-1) tmp1 tmp2++
                          Load tmp1 (C' + t, t) :: Store (W' + x, t) (V tmp1) :: rest )::P2 /\
 exec_star (Some P) G 
           (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
            events_hb_check (R + x) (C + t) vs3 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
            mops_hb_check (R + x) (C + t) vs3 vs2 n t) 
           (Some Pgood) Ggood /\
 exec Pgood Ggood t None None None Ggood.
Proof.
  intros. unfold store_handler in *. clarify.
  assert(Hves: exists ve1 ve2 ve3 vss1 vss2 vss3, vs1=vss1++[ve1]/\ vs2=vss2++[ve2] /\ vs3=vss3++[ve3]).
  { destruct vs1, vs2, vs3; clarify.
    do 6 eexists.
    instantiate(1:=last (n1::vs3) n1). instantiate (1:=removelast (n1::vs3)).
    instantiate(1:=last (n0::vs2) n0). instantiate (1:=removelast (n0::vs2)).
    instantiate(1:=last (n::vs1) n). instantiate (1:=removelast (n::vs1)).
    repeat rewrite <- app_removelast_last; clarify. }
  inversion Hves as (ve1 & ve2 & ve3 & vss1 & vss2 & vss3 & Hvss1 & Hvss2 & Hvss3); clarify.
  rewrite Hvss3, Hvss2, Hvss1 in *. clear Hvss1. clear Hvss2. clear Hvss3.
  assert(Hupd: upd_env (upd_env G t tmp1 v3) t tmp2 v2 =
                 upd_env (upd_env (upd_env (upd_env G t tmp1 ve1) t tmp2 ve2) t tmp1 v3) t tmp2 v2).
  { symmetry. rewrite upd_assoc. rewrite upd_overwrite. rewrite upd_assoc.
    rewrite upd_overwrite. eauto. eauto. eauto. }
  exploit hb_check_fail_spec'.
  { instantiate(1:=P2). instantiate(1:=move(C'+t,t) (W' + x, t) tmp1 ++ rest).
    instantiate(1:=tmp2). instantiate(1:=tmp1). instantiate(1:= length (vss3 ++ [ve3])).
    instantiate(1:=C'+ t). instantiate(1:=R'+x). instantiate(1:=t).
    instantiate(1:= P1). eauto. }
  { eauto. }
  { instantiate(1:=vss3++[ve3]). eauto. }
  { instantiate(1:=vss2++[ve2]). omega. }
  { eauto. }
  { instantiate(1:=(upd_env (upd_env G t tmp1 ve1) t tmp2 ve2)). eauto. }
  intros ( c & Pgood & Hc & HPgood & Hexecs & Hexec).
  exists c, Pgood. rewrite Hvs3 in *.
  split;[|split;[|split]];clarify.
  eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
  rewrite <- app_assoc. eapply exec_star_trans.
  -apply hb_check_pass_spec; try (apply Hfirst_gt12); eauto.
  -rewrite <- app_assoc. repeat rewrite last_snoc. clarify.
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
      rewrite <- (app_nil_r (opt_to_list c)).
      -eapply exec_step. eauto. constructor.
      -apply Forall_app in Hprog_m2lc2i. clarify.
      -eapply consistent_app_SC; rewrite <- app_assoc; eauto.
      -rewrite <- app_assoc. auto. } 
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

Lemma skipn_hb_check: forall c z C1 C2 tmp1 tmp2
                             (Hc: c <= z), skipn (3*c) (hb_check C1 C2 z tmp1 tmp2) = hb_check C1 C2 (z-c) tmp1 tmp2.
Proof.
  intros.
  generalize dependent z.
  induction c; clarify.
  -rewrite <- minus_n_O. auto.
  -destruct z; clarify.
   assert(c + S (c + S (c + 0))=S ( S (c + (c + (c+0))))) as Hlen by omega.
   rewrite Hlen. simpl. apply IHc. omega.
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
  (Hcon : consistent (m0++m1 )) s  (Hs : clocks_sim m0 s)
  s_good (Hsafe:  step_star s ops1 s_good)   
  (Hrace : forall s', ~step_star s_good (opt_to_list o) s'),
  exists  lo2 m2 lo lc o2 c2 G2s P2' G2' G2'',
    exec_star (Some (init_state (instrument P 0))) init_env lo2 m2 (Some P2) G2s
 /\ exec_star (Some P2) G2s lo lc (Some P2') G2' /\ state_suffix P1 P2' /\
    exec P2' G2' t o2 c2 None G2'' /\ consistent (m0 ++ m2 ++ lc ++ opt_to_list c2) /\
    mem_vals (m0++m1) (m0++m2) /\ env_sim G1 G2s /\
    (Forall (fun c0=> meta_loc (loc_of c0)) lc)/\ env_sim G2s G2'.
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
      assert(exists v1 v2, first_gt (map (write_of s_good x) (rev (interval 0 zt)))
     (map (clock_of s_good t0) (rev (interval 0 zt))) =
                           Some (v1, v2)) as Hfirst_gt.
      { do 2 eexists.
        rewrite first_gt_spec.
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
      clarify.
      exploit load_handler_race_spec'.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s_good t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s_good x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { apply Hfirst_gt. }
      { eauto. } 
      intros (c & Pgood & Hc & HPgood & Hexecs & Hexec ).
      clarify.
      do 10 eexists.
      split; [|split;[|split;[|split;[|split;[|split]]]]].
      -eapply Hexec_starP2good.
      -rewrite map_length, rev_length, interval_length, <- minus_n_O in Hexecs.
       assert(zt+0=zt) as Hztsilly by omega.
       rewrite Hztsilly in Hexecs.
       rewrite <- app_assoc. apply Hexecs.
      -unfold state_suffix. apply Forall2_app.
       +apply sim_suffix. apply HP0.
       +apply Forall2_cons.
        *split; clarify.
         rewrite map_length, rev_length, interval_length in Hc.
         exists (S (3*c+2)). split.
         { repeat rewrite app_length. rewrite hb_check_len. clarify.
           omega. }
         { simpl. rewrite <- skipn_skipn. assert((c + (c + (c + 0)))=3*c) as H3c by omega.
           rewrite H3c. do 2 rewrite <- app_assoc. rewrite skipn_app'. 
           -rewrite skipn_hb_check.
            +assert(zt-c = S (zt-c -1)) as Hztc by omega.
             rewrite Hztc. simpl. rewrite <- minus_n_O. auto.
            +omega.
           -rewrite hb_check_len.  omega. }
        *apply sim_suffix. apply HP3.
      -rewrite map_length, rev_length, interval_length in Hexec.
       rewrite <- minus_n_O, plus_0_r in Hexec. apply Hexec.
      -do 2 rewrite app_assoc. rewrite split_app. simpl. rewrite app_nil_r.
       apply mops_hb_check_con; clarify.
       +apply clocks_sim_acq; clarify.
       +inversion Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
        inversion Ht2 as (HtP0 & Hirest).  inversion Hirest. clarify.
       +apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify.
      -auto.
      -split;[|split]; auto.
       constructor.
       +clarify. apply X_meta; auto.
       +rewrite Forall_forall. intros.
        exploit mops_hb_check_meta.
        { apply H22. }
        { inversion Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
          inversion Ht2 as (HtP0 & Hirest).  inversion Hirest. clarify. apply H4. }
        { left. eauto. }
        clarify.
       +unfold env_sim. unfold upd_env, upd. clarify. destruct (eq_dec tmp2 v0); clarify.
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
      exploit store_handler_race_war_spec'.
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
      { eauto. }
      intros ( c & Pgood & Hc & HPgood & Hexecs & Hexec).
      instantiate(1:=t0) in Hexecs.
      instantiate(1:=G2_good) in Hexecs. instantiate(1:=x) in Hexecs. 
      instantiate(1:= l') in Hexecs.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hexecs.
      instantiate(1:=P0') in Hexecs.
      rewrite <- app_assoc. unfold store_handler in Hexecs.
      rewrite map_length, rev_length, interval_length, <- minus_n_O, plus_0_r in *.
      clarify.
      do 10 eexists. split;[|split;[|split;[|split;[|split;[|split]]]]]; eauto.
      -rewrite <- app_assoc in Hexec_starP2good. apply Hexec_starP2good.
      -apply Forall2_app.
       +apply sim_suffix. auto.
       +apply Forall2_cons; clarify.
        *exists (S (3*zt +(3*c+2))).
         split; clarify.
         { repeat rewrite app_length. repeat rewrite hb_check_len. clarify. omega. }
         { repeat rewrite <- app_assoc. rewrite <- skipn_skipn. rewrite skipn_app.
           assert(forall x, (x + (x + (x + 0)))= 3*x) as H3x by (intros; omega).
           rewrite (H3x zt), (H3x c) . rewrite skipn_hb_check; auto.
           rewrite hb_check_len. rewrite <- (minus_n_n zt), <- (minus_n_n (3*zt)) .
           simpl. rewrite <- skipn_skipn. rewrite (H3x c).
           rewrite skipn_app'; auto.
           -rewrite skipn_hb_check; auto.
            +assert(zt-c = S (zt-c-1)) as Hztc by omega.
             rewrite Hztc. simpl.  rewrite <- minus_n_O. auto.
            +omega.
           -rewrite hb_check_len. omega. }
        *apply sim_suffix. auto.
      -clarify. rewrite app_nil_r, app_assoc, split_app, app_assoc.
       destruct Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
       inversion Ht2 as (Ht21  & Ht22). inversion Ht22. clarify.
       assert (Hcon_hb:   consistent (((m0 ++ m2) ++ [Acq t0 (X' + x)]) ++
         mops_hb_check (W' + x) (C' + t0)
        (map (write_of s_good x) (rev (interval 0 zt)))
        (map (clock_of s_good t0) (rev (interval 0 zt))) zt t0)).
       { apply mops_hb_check_con; clarify.
        - apply clocks_sim_acq; clarify.
        - apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify. }
       apply mops_hb_check_conR; clarify.
       apply clocks_sim_allreads; clarify.
       +apply clocks_sim_acq; clarify.
       +apply mops_hb_check_read.
      -split;[|split]; clarify.
       constructor.
       +clarify. apply X_meta; auto.
       +inversion Ht as (Ht1 & Ht2); clarify. rewrite Forall_app in Ht2; clarify.
        inversion Ht22. clarify.
         apply Forall_app. split; rewrite Forall_forall; intros; eapply mops_hb_check_meta.
        *apply H22.
        *apply H4.
        *left. eauto.
        *apply H22.
        *apply H4.
        *right.  eauto.
       +unfold env_sim. unfold upd_env, upd. clarify. destruct (eq_dec tmp2 v); clarify.
    }
    {(*WAW*)
      exploit store_handler_race_waw_spec'.
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
      { eauto. }
      intros (c & Pgood & Hc & HPgood & Hexecs & Hexec).
      rewrite plus_0_r in Hexecs. 
      instantiate(1:=t0) in Hexecs.
      instantiate(1:=G2_good) in Hexecs. instantiate(1:=x) in Hexecs. 
      instantiate(1:= l') in Hexecs.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hexecs.
      instantiate(1:=P0') in Hexecs.
      rewrite <- app_assoc. unfold store_handler in Hexecs.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hexecs.
      simpl in Hexecs. simpl.
      rewrite <- app_assoc in Hexec_starP2good.
      destruct Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
      inversion Ht2 as (Ht21  & Ht22). inversion Ht22.
      do 10 eexists. split;[|split;[|split;[|split;[|split;[|split]]]]]; eauto.
      -rewrite HPgood.
       rewrite plus_0_r, map_length, rev_length, interval_length, <- minus_n_O in *.
       apply Forall2_app.
       +apply sim_suffix; auto.
       +apply Forall2_cons; clarify.
        *exists (S (3*c +2)). split.
         { repeat rewrite <- app_assoc. repeat rewrite app_length, hb_check_len. simpl.
           omega. }
         { simpl. repeat rewrite <- app_assoc. rewrite <- skipn_skipn.
           rewrite skipn_app'; auto.
           -assert((c + (c + (c + 0)))=3*c) as H3c by omega.
            rewrite H3c. rewrite skipn_hb_check.
            +assert (zt -c = S (zt -c -1)) as Hztc by omega.
             rewrite Hztc. clarify. rewrite <- minus_n_O. auto.
            +omega.
           -rewrite hb_check_len. omega. }
        *apply sim_suffix; auto.
      -clarify. rewrite app_assoc, split_app. rewrite app_nil_r.
       apply mops_hb_check_con; clarify.
       +apply clocks_sim_acq; clarify.
       +apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify.
      -split;[|split]; auto. constructor.
       +simpl. apply X_meta; auto.
       +simpl in H4. rewrite Forall_forall; intros. eapply mops_hb_check_meta; eauto.
       +unfold env_sim. unfold upd_env, upd. clarify. destruct (eq_dec tmp2 v); clarify.
     }
    {(*both WAW&WAR, equilvalent to WAW*)
      exploit store_handler_race_waw_spec'.
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
      { eauto. }
      intros (c & Pgood & Hc & HPgood & Hexecs & Hexec).
      rewrite plus_0_r in Hexecs. 
      instantiate(1:=t0) in Hexecs.
      instantiate(1:=G2_good) in Hexecs. instantiate(1:=x) in Hexecs. 
      instantiate(1:= l') in Hexecs.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hexecs.
      instantiate(1:=P0') in Hexecs.
      rewrite <- app_assoc. unfold store_handler in Hexecs.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hexecs.
      simpl in Hexecs. simpl.
      rewrite <- app_assoc in Hexec_starP2good.
      destruct Ht as (Ht1 & Ht2). rewrite Forall_app in Ht2.
      inversion Ht2 as (Ht21  & Ht22). inversion Ht22.
      do 10 eexists. split;[|split;[|split;[|split;[|split;[|split]]]]]; eauto.
      -rewrite HPgood.
       rewrite plus_0_r, map_length, rev_length, interval_length, <- minus_n_O in *.
       apply Forall2_app.
       +apply sim_suffix; auto.
       +apply Forall2_cons; clarify.
        *exists (S (3*c +2)). split.
         { repeat rewrite <- app_assoc. repeat rewrite app_length, hb_check_len. simpl.
           omega. }
         { simpl. repeat rewrite <- app_assoc. rewrite <- skipn_skipn.
           rewrite skipn_app'; auto.
           -assert((c + (c + (c + 0)))=3*c) as H3c by omega.
            rewrite H3c. rewrite skipn_hb_check.
            +assert (zt -c = S (zt -c -1)) as Hztc by omega.
             rewrite Hztc. clarify. rewrite <- minus_n_O. auto.
            +omega.
           -rewrite hb_check_len. omega. }
        *apply sim_suffix; auto.
      -clarify. rewrite app_assoc, split_app. rewrite app_nil_r.
       apply mops_hb_check_con; clarify.
       +apply clocks_sim_acq; clarify.
       +apply can_arw_SC; specialize(Hs_x (m0++m2) H22); clarify.
      -split;[|split]; auto. constructor.
       +apply X_meta; auto.
       +simpl in H2. rewrite Forall_forall. intros. eapply mops_hb_check_meta; eauto.
       +unfold env_sim. unfold upd_env, upd. clarify. destruct (eq_dec tmp2 v); clarify.
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
  (Hinit: forall p : ptr, (*meta_loc p ->*) initialized m0 p)
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
   { constructor. }
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
   { instantiate(1:=[]). constructor. }
   { rewrite app_nil_r. auto. }
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

Lemma fail_iexec_execs : forall P G t lo lc P0 (Hsim : state_sim P0 P)
  (Hsafe : safe_locs P0) (Hdistinct : distinct P) (Ht : t < zt),
  fail_iexec P t lo lc ->
  Forall (fun c => meta_loc (loc_of c)) lc /\
  exists G', exec_star (Some P) G lo lc None G' /\ env_sim G G'.
Proof.
  intros; inversion H; subst.
  - split.
    { exploit state_sim_inv'; eauto; intros (? & [|?] & ?); clarify.
      exploit instrument_incom.
      { instantiate (3 := Load a (x, o)); simpl.
        rewrite <- app_assoc; simpl; eauto. }
      clarify.
      setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
      constructor; [apply X_meta; auto|].
      rewrite Forall_forall; intros; eapply mops_hb_check_meta; eauto. }
    eexists; split.
    erewrite <- events_hb_check_extend; [|intro; clarify].
    erewrite <- mops_hb_check_extend; [|intro; clarify].
    eapply load_handler_race_spec; eauto.
    + instantiate (1 := replicate 0 (zt - length vs1)).
      rewrite app_length, replicate_length, Nat.add_sub_assoc, minus_plus; auto.
    + instantiate (1 := replicate 0 (zt - length vs2)).
      rewrite app_length, replicate_length, Nat.add_sub_assoc, minus_plus; auto.
    + apply first_gt_extend; eauto.
    + unfold env_sim; intros; rewrite upd_old, upd_old; auto.
  - split.
    { exploit state_sim_inv'; eauto; intros (? & [|?] & ?); clarify.
      exploit instrument_incom.
      { instantiate (3 := Store (x, o) e); simpl.
        rewrite <- app_assoc; simpl; eauto. }
      clarify.
      setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
      constructor; [apply X_meta; auto|].
      rewrite Forall_forall; intros; eapply mops_hb_check_meta; eauto. }
    eexists; split.
    erewrite <- events_hb_check_extend; [|intro; clarify].
    erewrite <- mops_hb_check_extend; [|intro; clarify].
    eapply store_handler_race_waw_spec; eauto.
    + instantiate (1 := replicate 0 (zt - length vs1)).
      rewrite app_length, replicate_length, Nat.add_sub_assoc, minus_plus; auto.
    + instantiate (1 := replicate 0 (zt - length vs2)).
      rewrite app_length, replicate_length, Nat.add_sub_assoc, minus_plus; auto.
    + apply first_gt_extend; eauto.
    + unfold env_sim; intros; rewrite upd_old, upd_old; auto.
  - split.
    { exploit state_sim_inv'; eauto; intros (? & [|?] & ?); clarify.
      exploit instrument_incom.
      { instantiate (3 := Store (x, o) e); simpl.
        rewrite <- app_assoc; simpl; eauto. }
      clarify.
      setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
      constructor; [apply X_meta; auto|].
      rewrite Forall_app; split; rewrite Forall_forall; intros;
        eapply mops_hb_check_meta; eauto. }
    eexists; split.
    eapply store_handler_race_war_spec; eauto.
    + unfold env_sim; intros; rewrite upd_old, upd_old; auto.
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

Lemma no_asserts_step:
  forall P G o c P' G' t
         (Hno_asserts: no_asserts P)
         (Hstep: exec P G t o c (Some P') G'),
    no_asserts P'.
Proof.
  intros.
  inversion Hstep; clarify;
  unfold no_asserts, state_forall in *; apply Forall_app in Hno_asserts; clarify;
  inversion Hno_asserts2; clarify; inversion H1; clarify;
  rewrite Forall_app; clarify.
  rewrite instr_forall_list in H3.
  clarify.
Qed.

Lemma no_asserts_steps:
  forall  P G o c P' G'
          (Hno_asserts: no_asserts P)
          (Hsteps: exec_star (Some P) G o c (Some P') G' ),
    no_asserts P'.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb;
  generalize dependent P; generalize dependent P'; induction Hsteps; clarify.
  destruct P'; clarify.
  -specialize (no_asserts_step Hno_asserts Hexec). clarify.
   apply IHHsteps with (P:=s); clarify.
  -inversion Hsteps.
Qed.
   
(* safe up to a point, then race step *)
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
  (Hclocks_sim: clocks_sim m0 s0) G1' m1' (Hcon_m01': consistent (m0++m1')) t (Ht: t< zt),
  (exists ops2 (*t*) m2 P2' G2' G2'' o c,
    exec_star (Some (init_state (instrument P 0))) init_env ops2 m2 (Some P2') G2' /\
     exec P2' G2' t o c None G2''
     /\
     consistent (m0 ++ m2) /\ mem_vals (m0++m2) (m0++m1') /\ env_sim G1' G2') <->
  (exists ops m1 P' G' (*t*) o c P1'' G1'',
     exec_star (Some (init_state P)) init_env ops m1 (Some P') G' /\
     exec P' G' t o c (Some P1'') G1'' /\ consistent (m0 ++ m1) /\ mem_vals (m0++m1) (m0++m1') /\
     env_sim G' G1' /\ exists s, step_star s0 ops s /\ forall s', ~step_star s (opt_to_list o) s').
Proof.
  intros. split.
  -intros (ops2 (*& t*) & m2 & P2' & G2' & G2'' & o & c & Hexec_star_inst & Hexec_inst & Hcon_m02  & Hmem_m2 & HenvG1'2').
   exploit exec_fail_iexec; eauto.
   { unfold init_state; constructor; auto. }
   { constructor; auto. }
   { unfold init_state; constructor; auto. }
   { constructor; auto; simpl; omega. }
   { apply exec_refl. }
   intro X; exploit X; clear X.
   { inversion Hexec_inst; subst.
     simpl; rewrite app_nil_r; eauto. }
   { auto. }
   intros (? & ? & ? & ? & ? & ? & Hiexec & ?); clarify.
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
   exploit instrument_sim_race2; try apply Hiexec; try apply Hfresh_tmpsP1';
     auto.
   { unfold legal_tids in Hlegal_tidsP1'; clarify. }
   { etransitivity; [apply HenvG1'2' | eauto]. }
   { eauto. }
   { auto.  }
   { eauto. }
   intros (o1' & ops1 & m1 & c1' & P1'' & G1s' & G1''  & Hmon).
   destruct Hmon as (Hexec_starP1' & Henv_simG1' & HexecP1'' & Hcon_m01
                     & Hmem_valsm012 & s' & Hss_s' & Hrace); clarify.
   do 8 eexists; split;[|split;[|split;[|split;[|split]]]]; eauto.
   eapply mem_vals_cond_trans.
   { instantiate(1:=(m0++m2)). intros. split; clarify; apply init_steps; auto; eapply prog_steps; eauto. }
   { eapply mem_vals_cond_trans; clarify.
     -instantiate(1:=(m0++x0)). intros. split; clarify; apply init_steps; auto; eapply prog_steps; eauto.
      apply iexec_star_exec_star in Hiexec. eauto.
     -auto.
     -apply mem_vals_cond_symm; clarify.
      intros. split; clarify; apply init_steps; auto; eapply prog_steps; eauto.
      apply iexec_star_exec_star in Hiexec. eauto. }
   { auto. }
  -intros (ops1 & m1 & P1_good & G1_good (*& t*) & o1 & c1 & P1_race & G1_race &
                Hexec_starP1_good & Hexec_race & Hcon_m01 & Hmem_valsm011' &
                Henv_simG1_good & s_good & Hstep_starsgood & Hnostep).
   exploit instrument_sim_safe'.
   { instantiate (1:=init_state P); auto. }
   { auto. }
   { instantiate (1:=init_state (instrument P 0)). unfold distinct, init_state.
     clarify. constructor; auto. }
   { auto. }
   { auto. }
   { unfold state_sim, init_state. clarify. }
   { apply env_sim_refl. }
   { intros; apply Hinit. }
   { apply exec_refl. }
   { eauto. }
   { rewrite app_nil_r; auto. }
   { constructor. }
   { instantiate(1:=[]). constructor. }
   { rewrite app_nil_r; auto. }
   { apply mem_vals_refl. }
   { rewrite app_nil_r; eauto. }
   { eauto. }
   rewrite app_nil_r.
   intros (ops2 & m2 & P2_good & G2_good & Hexec_starP2_good & Hcon_m02 &
                Hstate_simP2good & Henv_simG2good & Hmem_vals_m012 & Hclocks_sims_good).
   rewrite app_assoc, app_nil_r in Hclocks_sims_good.
   exploit instrument_sim_race.
   { eauto. }
   { auto. }
   { auto. }
   { instantiate (1:=P1_good). eapply fresh_tmps_steps; eauto. }
   { eapply safe_locs_steps; eauto. }
   { eapply legal_tids_steps in Ht; eauto. }
   { instantiate (1:=P2_good). eapply distinct_steps; eauto.
     unfold distinct, init_state. clarify. constructor; auto. }
   { auto. }
   { auto. }
   { apply Henv_simG2good. }
   { eauto. }
   { eauto. }
   { intros; apply Hinit. }
   { auto. }
   { eauto. }
   { eauto. }
   { auto. }
   intros (ops2' & m2s & lo & lc & o & c & G2s & P2' & G2' & G2'' &
     Hexec_starP2good & Hexec2 & Hsuffix2 & Hexec_race2 & Hcon_m02s &
     Hmem_vals_m12s & Henv_sim_G12s ).
   exploit first_fail'.
   { apply instrumented. }
   { instantiate (1 := [(0, P)]); constructor; auto. }
   { auto. }
   { auto. }
   { constructor; simpl; destruct zt; auto; omega. }
   { auto. }
   { auto. }
   { auto. }
   { auto. }
   { auto. }
   { auto. }
   { eauto. }
   { eapply safe_locs_steps; eauto. }
   { eapply fresh_tmps_steps; eauto. }
   { eapply no_asserts_steps; eauto.  }
   { eauto. }
   { eauto. }
   { eauto. }
   { eauto. }
   intro X; exploit X; clear X; eauto; clarify.
   exploit fail_iexec_execs; eauto.
   { eapply safe_locs_steps; eauto. }
   { eapply distinct_steps; eauto. unfold init_state. constructor; clarify. }
   intros (Hmeta & ? & Hfails & HG).
   rewrite exec_rev in Hfails; inversion Hfails; subst; clear Hfails;
     rewrite <- exec_rev in *.
   do 8 eexists; [|split; eauto].
   { eapply exec_star_trans; eauto. }
   split; [|split].
   + eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto.
   + rewrite Forall_app in Hmeta; clarify. 
     rewrite app_assoc; apply mem_vals_app_meta; auto.
     * eapply mem_vals_cond_trans; eauto.
       { intros. split; clarify; apply init_steps; clarify; eapply prog_steps; eauto. }
       { apply mem_vals_cond_symm; auto.
         split; clarify; apply init_steps; clarify; eapply prog_steps; eauto. }
     * intros; eapply init_steps, prog_steps; eauto.
     * eapply prog_steps; eauto.
     * eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto.
   + inversion Hexec'; clarify.
     inversion Hexec_race2. clarify.
     instantiate(1:= G2s) in HG.
     eapply env_sim_trans.
     *instantiate (1:= G2s). eapply env_sim_trans.
      { instantiate (1:= G1_good). apply env_sim_symm. auto. }
      { auto. }
     *auto.
Qed.

End Sim_Proofs.