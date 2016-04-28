(* Lemmas about memory *)
Require Import Util.
Require Import block_model.
Require Import conc_model.
Require Import Lang.

Set Implicit Arguments.

Section SC.

Context {ML : @Memory_Layout var nat _}.

Global Instance conc_op_dec : EqDec_eq conc_op.
Proof. eq_dec_inst. Qed.

Definition consistent (m : list conc_op) := @SC _ _ _ ML _ _ Base m.

Definition can_read (m : list conc_op) p v := consistent (m ++ [Read 0 p v]).
Definition can_write (m : list conc_op) p :=
  forall v, consistent (m ++ [Write 0 p v]).

Definition prog_op c := match c with Read _ _ _ | Write _ _ _ | ARW _ _ _ _ =>
  True | _ => False end.

Lemma op_indep : forall c1 c2 (Hindep : loc_of c1 <> loc_of c2)
   (Hc1 : prog_op c1) (Hc2 : prog_op c2),
   Forall (fun l => Forall (independent l) (map block_model.loc_of (to_seq c2)))
     (map block_model.loc_of (to_seq c1)).
Proof.
  destruct c1, c2; clarify.
Qed.

Lemma loc_comm_SC : forall m1 c1 c2 m2 (Hindep : loc_of c1 <> loc_of c2)
  (Hc1 : prog_op c1) (Hc2 : prog_op c2)
  (Hcon : consistent (m1 ++ c1 :: c2 :: m2)), consistent (m1 ++ c2 :: c1 :: m2).
Proof.
  unfold consistent, SC; clarify.
  rewrite lower_app, lower_cons, lower_cons;
    rewrite lower_app, lower_cons, lower_cons in Hcon.
  repeat rewrite to_ilist_app in *; rewrite loc_comm_ops; auto.
  apply op_indep; auto.
Qed.
  
Lemma loc_comm_ops1_SC : forall c lc m1 m2
  (Hindep : Forall (fun c' => loc_of c' <> loc_of c) lc)
  (Hc : prog_op c) (Hlc : Forall prog_op lc),
  consistent (m1 ++ c :: lc ++ m2) <-> consistent (m1 ++ lc ++ c :: m2).
Proof.
  induction lc; clarify; [reflexivity|].
  inversion Hlc; inversion Hindep; clarify.
  specialize (IHlc (m1 ++ [a]) m2); clarsimp.
  etransitivity; eauto; split; apply loc_comm_SC; auto.
Qed.

Lemma loc_comm_ops_SC : forall lc1 lc2 m1 m2
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lc2) lc1)
  (Hlc1 : Forall prog_op lc1) (Hlc2 : Forall prog_op lc2),
  consistent (m1 ++ lc1 ++ lc2 ++ m2) <-> consistent (m1 ++ lc2 ++ lc1 ++ m2).
Proof.
  induction lc1; clarify; [reflexivity|].
  inversion Hlc1; clarify.
  specialize (IHlc1 lc2 (m1 ++ [a]) m2); inversion Hindep; clarsimp.
  etransitivity; eauto; apply loc_comm_ops1_SC; auto.
Qed.

Lemma consistent_app_SC : forall m1 m2 (Hcon : consistent (m1 ++ m2)),
  consistent m1.
Proof.
  unfold consistent, SC; intros.
  rewrite lower_app in Hcon; eapply consistent_app; eauto.
Qed.

Lemma consistent_drop : forall m c1 c2, consistent (m ++ [c1; c2]) ->
  consistent (m ++ [c1]).
Proof.
  intros; eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
Qed.

Lemma loc_valid_SC : forall m c1 c2 (Hindep : loc_of c1 <> loc_of c2)
  (Hc1 : prog_op c1) (Hc2 : prog_op c2),
  consistent (m ++ [c1; c2]) <->
  (consistent (m ++ [c1]) /\ consistent (m ++ [c2])).
Proof.
  split; intros.
  - split.
    + rewrite split_app in H; exploit consistent_app_SC; eauto; clarify.
    + exploit loc_comm_SC; eauto; intro H'.
      rewrite split_app in H'; exploit consistent_app_SC; eauto; clarify.
  - unfold consistent, SC in *; clarify.
    repeat rewrite lower_app; rewrite lower_cons; repeat rewrite lower_single.
    rewrite lower_app, lower_single in H1, H2.
    apply loc_valid_ops; auto.
    apply op_indep; auto.
Qed.

Lemma loc_valid_ops1_SC : forall c lc m
  (Hindep : Forall (fun c' => loc_of c' <> loc_of c) lc)
  (Hc : prog_op c) (Hlc : Forall prog_op lc),
  consistent (m ++ lc ++ [c]) <->
  (consistent (m ++ lc) /\ consistent (m ++ [c])).
Proof.
  induction lc; clarify.
  { split; clarsimp.
    eapply consistent_app_SC; eauto. }
  inversion Hlc; clarify.
  specialize (IHlc (m ++ [a])); inversion Hindep; clarsimp.
  rewrite IHlc, loc_valid_SC; auto.
  split; intro Hcon; clarify.
  rewrite split_app in Hcon1; eapply consistent_app_SC; eauto.
Qed.

Corollary loc_valid_ops2_SC : forall m c lc
  (Hindep : Forall (fun c' => loc_of c' <> loc_of c) lc)
  (Hc : prog_op c) (Hlc : Forall prog_op lc),
  consistent (m ++ c :: lc) <->
  (consistent (m ++ lc) /\ consistent (m ++ [c])).
Proof.
  intros; rewrite <- loc_valid_ops1_SC; auto.
  generalize (loc_comm_ops1_SC _ m [] Hindep); rewrite app_nil_r; auto.
Qed.

Lemma loc_valid_ops_SC : forall lc1 lc2 m
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lc2) lc1)
  (Hlc1 : Forall prog_op lc1) (Hlc2 : Forall prog_op lc2),
  consistent (m ++ lc1 ++ lc2) <->
  (consistent (m ++ lc1) /\ consistent (m ++ lc2)).
Proof.
  induction lc1; clarify.
  { split; clarsimp.
    eapply consistent_app_SC; eauto. }
  inversion Hlc1; clarify.
  specialize (IHlc1 lc2 (m ++ [a])); inversion Hindep; clarsimp.
  rewrite IHlc1; setoid_rewrite loc_valid_ops2_SC at 2; auto.
  split; intro Hcon; clarify.
  rewrite split_app in Hcon1; eapply consistent_app_SC; eauto.
Qed.  

Lemma read_noop_SC : forall m t x v m2 (Hcon : consistent (m ++ [Read t x v])),
  consistent (m ++ Read t x v :: m2) <-> consistent (m ++ m2).
Proof.
  unfold consistent, SC; clarify.
  repeat rewrite lower_app; rewrite lower_app in Hcon.
  rewrite lower_single in Hcon; rewrite lower_cons; clarify.
  rewrite split_app; do 2 rewrite to_ilist_app; apply read_noop; auto.
Qed.

Corollary reads_noops_SC : forall ops m m2
  (Hcon : consistent (m ++ ops))
  (Hread : Forall (fun c => match c with Read _ _ _ => True | _ => False end)
                  ops),
  consistent (m ++ ops ++ m2) <-> consistent (m ++ m2).
Proof.
  induction ops; clarify; [reflexivity|].
  specialize (IHops (m ++ [a]) m2); inversion Hread; clarsimp.
  destruct a; clarify.
  rewrite IHops; apply read_noop_SC.
  rewrite split_app in Hcon; eapply consistent_app_SC; eauto.
Qed.


Lemma can_read_thread : forall m p v t, can_read m p v ->
  consistent (m ++ [Read t p v]).
Proof.
  unfold can_read, consistent, SC; setoid_rewrite lower_app; clarify.
Qed.

Lemma can_write_thread : forall m p v t, can_write m p ->
  consistent (m ++ [Write t p v]).
Proof.
  unfold can_write, consistent, SC; setoid_rewrite lower_app; clarify.
  specialize (H v); clarify.
Qed.

Lemma can_write_SC : forall p ops m (Hcan : can_write m p)
  (Hcon : consistent (m ++ ops)) (Hops : Forall prog_op ops),
  can_write (m ++ ops) p.
Proof.
  induction ops; clarsimp.
  inversion Hops; clarify.
  specialize (IHops (m ++ [a])); clarsimp.
  apply IHops; auto; clear IHops.
  rewrite split_app in Hcon; exploit consistent_app_SC; eauto; intro Hcon'.
  clear Hcon; unfold can_write, consistent, SC in *; clarsimp.
  specialize (Hcan v); rewrite lower_app, lower_single in Hcan, Hcon';
    rewrite lower_app, lower_cons, lower_single.
  destruct a; clarify.
  - rewrite read_noop_single; auto.
  - rewrite write_not_read_single; clarify.
  - rewrite split_app, write_not_read_single; clarsimp.
    rewrite read_noop_single; auto.
    rewrite split_app in Hcon'; eapply consistent_app; eauto.
Qed.

Lemma can_read_SC: forall p ops m v (Hcan: can_read m p v)
 (Hcon: consistent (m ++ ops)) (Hops : Forall prog_op ops)
  (Hnmods: Forall (fun c => match c with | Write _ x _ => p <> x
     | ARW _ x _ _=> p <> x | _ => True end) ops),
 can_read (m++ops) p v.
Proof.
 induction ops; clarsimp.
 inversion Hops; clarify.
 specialize(IHops (m++[a])); clarsimp.
 apply IHops; auto.
 rewrite split_app in Hcon; exploit consistent_app_SC; eauto; intro Hcon'.
 unfold can_read, consistent, SC in *; clarsimp.
rewrite lower_app, lower_single in Hcon'.
 rewrite lower_app, lower_single in Hcan.
 rewrite lower_app, lower_cons, lower_single.


 destruct a; clarify.
 -rewrite read_noop_single; clarify; auto.
 -rewrite write_not_read_single; auto.
  intros.
  apply Forall_inv in Hnmods. clarsimp.
  intro Heq. inversion Heq; clarify.
 -rewrite split_app. rewrite write_not_read_single; clarsimp.
  +rewrite read_noop_single; auto.
   rewrite split_app in Hcon'; eapply consistent_app; eauto.
  +apply Forall_inv in Hnmods. clarsimp.
   intro Heq. inversion Heq; clarify.
 -assert( a::ops =[a]++ops) as Haops.
    clarify.
  rewrite Haops in Hnmods.
  apply Forall_app in Hnmods. inversion Hnmods. auto.
Qed.


Lemma can_arw_SC_iff: forall p m v v' t,
  consistent (m ++ [ARW t p v v']) <-> can_write (m ++ [Read t p v]) p. 
Proof.
  unfold can_write, consistent, SC.
  repeat setoid_rewrite lower_app. setoid_rewrite lower_single. clarify. unfold seq_con. 
  rewrite split_app.  
  split; clarify.
  rewrite write_any_value.
  eauto.
Qed.

Lemma can_arw_SC : forall p m v (Hcan_r : can_read m p v)
  (Hcan_w: can_write m p) t v', consistent (m ++ [ARW t p v v']).
Proof.
  intros.
  rewrite can_arw_SC_iff.
  apply can_write_SC; auto.
  apply can_read_thread.
  auto.
  { constructor; clarify. }
Qed.
  
Lemma write_any_value_SC : forall m t p v v',
  consistent (m ++ [Write t p v]) <-> consistent (m ++ [Write t p v']).
Proof.
  intros; unfold consistent, SC; setoid_rewrite lower_app.
  repeat rewrite lower_single; simpl; apply write_any_value.
Qed.  

Lemma can_read_SC': forall p ops m v (Hcan: can_read m p v)
  (Hcon: consistent (m ++ ops)) (Hops : Forall prog_op ops)
  (Hnmods: Forall (fun c => match c with | Write _ x _ => p <> x
     | ARW _ x _ _=> p <> x | _ => True end) ops),
 can_read (m ++ ops) p v.
Proof.
 induction ops; clarsimp.
 inversion Hops; clarify.
 specialize(IHops (m++[a])); clarsimp.
 apply IHops; auto.
 rewrite split_app in Hcon; exploit consistent_app_SC; eauto; intro Hcon'.
 unfold can_read, consistent, SC in *; clarsimp.
rewrite lower_app, lower_single in Hcon'.
 rewrite lower_app, lower_single in Hcan.
 rewrite lower_app, lower_cons, lower_single.


 destruct a; clarify.
 -rewrite read_noop_single; clarify; auto.
 -rewrite write_not_read_single; auto.
  intros.
  apply Forall_inv in Hnmods. clarsimp.
  intro Heq. inversion Heq; clarify.
 -rewrite split_app. rewrite write_not_read_single; clarsimp.
  +rewrite read_noop_single; auto.
   rewrite split_app in Hcon'; eapply consistent_app; eauto.
  +apply Forall_inv in Hnmods. clarsimp.
   intro Heq. inversion Heq; clarify.
 -assert( a::ops =[a]++ops) as Haops.
    clarify.
  rewrite Haops in Hnmods.
  apply Forall_app in Hnmods. inversion Hnmods. auto.
Qed.

Lemma read_arwritten_SC : forall m p u v v' t (Hcon : consistent (m ++ [ARW t p u v])),
      consistent ((m ++ [ARW t p u v] )++ [Read t p v']) <-> v' = v.
Proof.
  intros.
  unfold consistent, SC in *; clarify.
  repeat rewrite lower_app in Hcon. rewrite lower_single in Hcon. clarify. 
  repeat rewrite lower_app,lower_single in *; clarify.
  rewrite <- app_assoc; simpl.
  rewrite split_app in *.
  apply read_written. auto.
Qed.

Lemma can_release_SC: forall t m l
  (Hcon: consistent (m ++ [Acq t l])) (Hcan_write: can_write m (l, 0)),
 consistent ((m ++ [Acq t l]) ++ [Rel t l]).
Proof.
  intros. 
  rewrite can_arw_SC_iff.
  apply can_write_SC.
  -apply can_write_SC; auto.
   constructor; clarify.
  -rewrite read_arwritten_SC; auto.
  -constructor; clarify.
Qed.

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

Definition initialized m p :=
  exists v, last_op (lower(MM_base := Base) m) (Ptr p) (MWrite p v).

Definition in_range_dec i a b : {a <= i < b} + {~a <= i < b}.
Proof.
  destruct (le_dec a i); [|right; omega].
  destruct (lt_dec i b); [left; auto | right; omega].
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

Global Instance mem_ext_refl : RelationClasses.Reflexive mem_ext.
Proof. repeat intro; split; reflexivity. Qed.

Global Instance mem_ext_sym : RelationClasses.Symmetric mem_ext.
Proof.
  intros ?? (? & ?).
  split; symmetry; auto.
Qed.

Global Instance mem_ext_trans : RelationClasses.Transitive mem_ext.
Proof.
  intros ??? (Hext1 & Hinit1) (Hext2 & Hinit2); split; intro.
  - rewrite (Hext1 ops); auto.
  - rewrite (Hinit1 p); auto.
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

Definition read_val c :=
  match c with
  | Read _ _ v | ARW _ _ v _ => Some v
  | _ => None
  end.

Lemma no_write_read : forall c (Hprog : prog_op c)
  (Hno_write : writesb c (loc_of c) = false), exists t p v, c = Read t p v.
Proof.
  destruct c; clarify; unfold beq in *; clarify; eauto.
Qed.

Lemma ARW_write : forall m t p v v' (Hcon : consistent (m ++ [ARW t p v v']))
  ops, consistent (m ++ ARW t p v v' :: ops) <->
       consistent (m ++ Write t p v' :: ops).
Proof.
  intros.
  unfold consistent, SC in *.
  do 2 rewrite lower_app, lower_cons; simpl.
  rewrite split_app, to_ilist_app, to_ilist_app.
  apply read_noop.
  rewrite lower_app, lower_single in Hcon; simpl in Hcon.
  eapply consistent_app; rewrite <- app_assoc; simpl; eauto.
Qed.

Lemma can_read_written_SC: forall m t p v (Hcon: consistent (m++[Write t p v])),
                             can_read (m++[Write t p v]) p v.
Proof.
  intros.
  unfold can_read. rewrite <- app_assoc. unfold consistent, SC, seq_con in *. repeat rewrite lower_app in *. repeat rewrite lower_single in *. clarify. rewrite read_written; auto.
  rewrite lower_app, lower_single in Hcon. clarify.
Qed.

Lemma consistent_next_write : forall m c1 c2 v (Hprog1 : prog_op c1)
  (Hprog2 : prog_op c2) (Hcon : consistent (m ++ [c1]))
  (Hloc : loc_of c1 = loc_of c2) (Hwrite : writesb c1 (loc_of c1) = true)
  (Hval : write_val c1 = Some v)
  (Hcond : match read_val c2 with Some v' => v' = v | None => True end),
  consistent (m ++ [c1; c2]).
Proof.
  intros.
  assert (forall t, consistent (m ++ [Write t (loc_of c1) v; c2])).
  assert (consistent (m ++ [Write (thread_of c1) (loc_of c1) v])).
  { destruct c1; clarify.
    rewrite ARW_write in Hcon; auto. }
  generalize (write_any_SC _ _ _ _ H); intro Hcan.
  intro; generalize (can_write_thread v t Hcan); intro Hcon'.
  generalize (can_write_SC Hcan Hcon'); intro Hcan'.
  use Hcan'; [|constructor; simpl; auto].
  generalize (can_read_written_SC _ _ _ _ Hcon'); intro.
  destruct c2; clarify.
  - exploit can_read_thread; eauto.
    rewrite <- app_assoc; simpl; eauto.
  - exploit can_write_thread; eauto.
    rewrite <- app_assoc; simpl; eauto.
  - rewrite split_app; apply can_arw_SC; auto.
  - destruct c1; clarify.
    rewrite ARW_write; auto.
Qed.

Lemma read_written_SC : forall m p v v' t t'
  (Hcon : consistent (m ++ [Write t p v])),
  consistent (m ++ [Write t p v; Read t' p v']) <-> v' = v.
Proof.
  intros.
  unfold consistent, SC in *; rewrite lower_app; rewrite lower_app in Hcon.
  rewrite lower_cons; rewrite lower_single; rewrite lower_single in Hcon;
    simpl in *.
  apply read_written; auto.
Qed.

Lemma consistent_next_write_iff : forall m c1 c2 v (Hprog1 : prog_op c1)
  (Hprog2 : prog_op c2) (Hcon : consistent (m ++ [c1]))
  (Hloc : loc_of c1 = loc_of c2) (Hwrite : writesb c1 (loc_of c1) = true)
  (Hval : write_val c1 = Some v),
  consistent (m ++ [c1; c2]) <->
  match read_val c2 with Some v' => v' = v | None => True end.
Proof.
  split; intro.
  - destruct (read_val c2) eqn: Hread; auto.
    assert (consistent (m ++ [c1; Read (thread_of c2) (loc_of c2) n])) as Hcon'.
    { destruct c2; clarify.
      rewrite split_app, can_arw_SC_iff in H.
      specialize (H 0); eapply consistent_app_SC.
      do 2 rewrite <- app_assoc in H; rewrite <- app_assoc; simpl in *; eauto. }
    assert (consistent (m ++ [Write (thread_of c1) (loc_of c1) v;
        Read (thread_of c2) (loc_of c2) n])).
    { destruct c1; clarify.
      rewrite ARW_write in Hcon'; auto. }
    rewrite Hloc in *; rewrite <- read_written_SC; eauto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
  - eapply consistent_next_write; eauto.
Qed.

End SC.