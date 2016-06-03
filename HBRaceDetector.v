Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import SCFacts.
Require Import Lang.
Require Import FunctionalExtensionality.
Require Import ExecFacts.
Set Implicit Arguments.

Definition move src tgt tmp := [Load tmp src; Store tgt (V tmp)].

Definition events_move (src tgt:var) (t:tid): list operation :=
  [rd t src; wr t tgt].

Definition mops_move (src tgt: ptr) (t:tid) (v:nat): list conc_op := [Read t src v; Write t tgt v].

Lemma move_spec_t : forall src tgt i j tmp P P1 P2 G t rest v
  (Hmove : P = P1 ++ (t, move (src, i) (tgt, j) tmp ++ rest) :: P2),
  exec_star_t t (Some P) G
            (events_move src tgt t) (mops_move (src, i) (tgt, j) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env G t tmp v).
Proof.
  clarify.
  eapply exec_step_t'.
  - apply exec_load; eauto.
  - eapply exec_step_t'; auto.
    + apply exec_store; eauto.
    + apply exec_refl_t.
  - auto.
  - simpl.
    rewrite upd_same; auto.
Qed.

Corollary move_spec : forall src tgt i j tmp P P1 P2 G t rest v
  (Hmove : P = P1 ++ (t, move (src, i) (tgt, j) tmp ++ rest) :: P2),
  exec_star (Some P) G
            (events_move src tgt t) (mops_move (src, i) (tgt, j) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env G t tmp v).
Proof.
  intros; eapply exec_t_exec, move_spec_t; auto.
Qed.

Fixpoint set_vc (src : var (* loc of source VC *)) (tgt : var (* loc of target VC *))
  (z : nat (* thread bound/size of VCs *))
  (tmp : local (* a local to use as temp *)) :=
(* Move all z of the timestamps in src into tgt. *)
match z with
| 0 => []
| S n =>  move (src,n) (tgt,n) tmp++set_vc src tgt n tmp 
end.

Fixpoint events_set_vc (src tgt: var) (z : nat) (t : tid) : list operation:=
match z with
| O => []
| S n => (events_move src tgt t)++events_set_vc src tgt n t
end.

Fixpoint mops_set_vc (src tgt: var) (z : nat) (t : tid) (vs: list nat): list conc_op :=
match (z,vs) with
| (S n,v::vss) => (mops_move (src,n) (tgt,n) t v)++mops_set_vc src tgt n t vss
| _ => []
end.

Lemma empty_list : forall (vs:list nat) (Hl: (length vs) = 0), vs=[]. 
Proof.
  destruct vs; clarify.
Qed.

Lemma events_set_vc_step: forall src tgt n t,
  events_set_vc src tgt (S n) t = (events_move src tgt t)++events_set_vc src tgt n t.
Proof.
  auto.
Qed.

Lemma mops_set_vc_step: forall src tgt n t v vss,
  mops_set_vc src tgt (S n) t (v::vss)= (mops_move (src,n) (tgt,n) t v)++mops_set_vc src tgt n t vss.
Proof.
  auto.
Qed.

Lemma set_vc_step: forall  src tgt n tmp,
  set_vc src tgt (S n) tmp =(move (src,n) (tgt,n) tmp)++set_vc src tgt n tmp.
Proof.
  auto.
Qed.

Lemma nonempty_list: forall (ls : list nat) n, 
  length ls = S n -> exists x xs, ls=x::xs /\ length xs=n.
Proof.
  destruct ls; clarify; eauto.
Qed.

Opaque last.

Lemma set_vc_spec_t : forall n src tgt tmp P G P1 P2 t rest vss 
(Hset_vc: P=P1++(t, set_vc src tgt n tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star_t t (Some P) G (events_set_vc src tgt n t)
             (mops_set_vc src tgt n t vss)
             (Some (P1++(t,rest)::P2)) (upd_env G t tmp (last vss (G t tmp))).
Proof.
  induction n; destruct vss; clarify.
  - rewrite upd_triv; apply exec_refl_t.
  - eapply exec_step_t'.
    { apply exec_load; eauto. }
    eapply exec_step_t'; auto.
    { apply exec_store; eauto. }
    instantiate (1 := mops_set_vc src tgt n t vss).
    instantiate (1 := events_set_vc src tgt n t).
    instantiate (1 := n0).
    destruct (nil_dec vss); clarify.
    + destruct n; clarify.
      apply exec_refl_t.
    + rewrite last_cons; auto.
      exploit IHn; eauto.
      instantiate (3 := upd_env G t tmp n0).
      rewrite upd_overwrite, upd_same.
      erewrite last_def; eauto.
    + auto.
    + simpl.
      rewrite upd_same; auto.
Qed.

Corollary set_vc_spec : forall n src tgt tmp P G P1 P2 t rest vss 
(Hset_vc: P=P1++(t, set_vc src tgt n tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star (Some P) G (events_set_vc src tgt n t) (mops_set_vc src tgt n t vss)
  (Some (P1++(t,rest)::P2)) (upd_env G t tmp (last vss (G t tmp))).
Proof.
  intros; eapply exec_t_exec, set_vc_spec_t; auto.
Qed.
 
Definition inc_vc t tgt tmp := [
  Load tmp (tgt, t);
  Assign tmp (Plus (V tmp) (I 1));
  Store (tgt, t) (V tmp)
].

Definition events_inc_vc (tgt:var) (t:tid): list operation:=
  [rd t tgt; wr t tgt]. 
Definition mops_inc_vc' (tgt: var) (v: nat) (t t' :tid): list conc_op:=
  [Read t (tgt,t') v; Write t (tgt, t') (v+1)].
Notation mops_inc_vc tgt v t := (mops_inc_vc' tgt v t t).

Lemma inc_vc_spec_t : forall  tgt tmp P G P1 P2 rest v t t'
  (Hinc_vc: P=P1++((t,inc_vc t' tgt tmp++rest)::P2)),
  exec_star_t t (Some P) G 
            (events_inc_vc tgt t) (mops_inc_vc' tgt v t t') 
            (Some (P1++(t,rest)::P2)) (upd_env G t tmp (v+1)). 
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_load; eauto. }
  eapply exec_step_t'; auto.
  { apply exec_assign; eauto. }
  rewrite upd_overwrite; simpl.
  rewrite upd_same.
  eapply exec_step_t'; auto.
  { apply exec_store; eauto. }
  apply exec_refl_t.
  - auto. 
  - simpl.
    rewrite upd_same; auto.
Qed.

Corollary inc_vc_spec : forall  tgt tmp P G P1 P2 rest v t t'
  (Hinc_vc: P=P1++((t,inc_vc t' tgt tmp++rest)::P2)),
  exec_star (Some P) G 
            (events_inc_vc tgt t) (mops_inc_vc' tgt v t t') 
            (Some (P1++(t,rest)::P2)) (upd_env G t tmp (v+1)). 
Proof.
  intros; eapply exec_t_exec, inc_vc_spec_t; auto.
Qed.

Definition max src tgt tmp1 tmp2 :=
[
  Load tmp1 src;
  Load tmp2 tgt;
  Assign tmp2 (Max (V tmp1) (V tmp2));
  Store tgt (V tmp2)
].

Definition events_max (src tgt:var) (t:tid) : list operation :=
[
  rd t src ;
  rd t tgt ;
  wr t tgt
]. 

Definition mops_max (src tgt: ptr) (v1 v2 : nat) (t:tid): list conc_op:=
[
  Read t src v1;
  Read t tgt v2;
  Write t tgt (Peano.max v1 v2)
].

Lemma max_spec_t : forall P P1 P2 rest G src tgt i j tmp1 tmp2 v1 v2 t
 (Hmax_spec: P= P1++((t, max (src, i) (tgt, j) tmp1 tmp2++rest)::P2)) (Hdist: tmp1<> tmp2),
exec_star_t t (Some P) G (events_max src tgt t) (mops_max (src, i) (tgt, j) v1 v2 t) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_load; eauto. }
  eapply exec_step_t'; auto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; auto.
  { apply exec_assign; eauto. }
  rewrite upd_overwrite; simpl.
  rewrite upd_old, upd_same, upd_same; auto.
  eapply exec_step_t'; auto.
  { apply exec_store; auto. }
  apply exec_refl_t.
  - auto.
  - simpl.
    rewrite upd_same; auto.
Qed.
 
Corollary max_spec : forall P P1 P2 rest G src tgt i j tmp1 tmp2 v1 v2 t
 (Hmax_spec: P= P1++((t, max (src, i) (tgt, j) tmp1 tmp2++rest)::P2)) (Hdist: tmp1<> tmp2),
exec_star (Some P) G (events_max src tgt t) (mops_max (src, i) (tgt, j) v1 v2 t) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).
Proof.
  intros; eapply exec_t_exec, max_spec_t; auto.
Qed.

Fixpoint max_vc src tgt z tmp1 tmp2 :=
match z with
| 0 => []
| S n => max (src,n) (tgt,n) tmp1 tmp2++ max_vc src tgt n tmp1 tmp2
end.

Fixpoint events_max_vc (src tgt:var) (t: tid) (z:nat): list operation:=
match z with
|0 => []
|S n => events_max src tgt t ++ events_max_vc src tgt t n
end.

Fixpoint mops_max_vc (src tgt: var) (vs1 vs2: list nat) (t:tid) (z:nat) : list conc_op:=
match (z,vs1,vs2) with
|(0,[],[]) => []
|(S n,v1::vss1,v2::vss2) => mops_max (src,n) (tgt,n) v1 v2 t ++ mops_max_vc src tgt vss1 vss2 t n
| _ => []
end. 

Lemma events_max_vc_step: forall src tgt t n,
  events_max_vc src tgt t (S n) = events_max src tgt t ++ events_max_vc src tgt t n.
Proof.
  auto.
Qed.

Lemma mops_max_vc_step: forall src tgt n v1 v2 vss1 vss2 t,
  mops_max_vc src tgt (v1::vss1) (v2::vss2) t (S n) =
  mops_max (src,n) (tgt,n) v1 v2 t ++ mops_max_vc src tgt vss1 vss2 t n.
Proof.
  auto.
Qed.

Lemma max_vc_step: forall  src tgt n tmp1 tmp2,
  max_vc src tgt (S n) tmp1 tmp2 = max (src,n) (tgt,n) tmp1 tmp2++ max_vc src tgt  n tmp1 tmp2.
Proof.
  auto.
Qed.

Lemma max_vc_spec_t : forall n src tgt tmp1 tmp2 P G P1 P2 t rest vss1
  vss2 (Hmax_vc: P=P1++(t, max_vc src tgt n tmp1 tmp2 ++ rest)::P2)
  (Htmp: tmp1 <> tmp2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
  exec_star_t t (Some P) G (events_max_vc src tgt t n)
    (mops_max_vc src tgt vss1 vss2 t n) (Some (P1++(t,rest)::P2))
    (upd_env (upd_env G t tmp1 (last vss1 (G t tmp1))) t tmp2
      (last (map (fun x => Peano.max (fst x) (snd x)) (combine vss1 vss2))
      (G t tmp2))).
Proof.
  induction n; destruct vss1, vss2; intros; subst; try solve [clarify].
  - do 2 rewrite upd_triv; apply exec_refl_t.
  - rewrite max_vc_step, events_max_vc_step, mops_max_vc_step.
    eapply exec_star_t_trans; [apply max_spec_t; eauto; reflexivity|].
    exploit IHn.
    { eauto. }
    { eauto. }
    { instantiate (1 := vss1); clarify. }
    { instantiate (1 := vss2); clarify. }
    simpl; do 2 rewrite last_cons'.
    instantiate (2 := upd_env (upd_env G t tmp1 n0) t tmp2 (Peano.max n0 n1)).
    rewrite upd_three, upd_three; auto.
    rewrite upd_same, upd_assoc, upd_same; eauto.
Qed.

Corollary max_vc_spec : forall n src tgt tmp1 tmp2 P G P1 P2 t rest vss1
  vss2 (Hmax_vc: P=P1++(t, max_vc src tgt n tmp1 tmp2 ++ rest)::P2)
  (Htmp: tmp1 <> tmp2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
  exec_star (Some P) G (events_max_vc src tgt t n)
    (mops_max_vc src tgt vss1 vss2 t n) (Some (P1++(t,rest)::P2))
    (upd_env (upd_env G t tmp1 (last vss1 (G t tmp1))) t tmp2
      (last (map (fun x => Peano.max (fst x) (snd x)) (combine vss1 vss2))
      (G t tmp2))).
Proof.
  intros; eapply exec_t_exec, max_vc_spec_t; auto.
Qed.

Definition assert_le (a b : ptr) (tmp1 tmp2:local): prog :=
[
    Load tmp1 a;
    Load tmp2 b;
    Assert_le (V tmp1) (V tmp2)
].

Definition events_assert_le(a b: var) (t:tid) : list operation :=
[
  rd t a;
  rd t b
].

Definition mops_assert_le (a b : ptr) (v1 v2: nat) (t: tid): list conc_op :=
[
  Read t a v1;
  Read t b v2
].

Lemma assert_le_fail_spec_t : forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: ~ v1 <= v2),
 exec_star_t t (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t)
            None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_load; auto. }
  eapply exec_step_t'; auto.
  { apply exec_load; auto. }
  eapply exec_step_t'; auto.
  { eapply exec_assert_fail; eauto.
    simpl.
    rewrite upd_old, upd_same, upd_same; eauto. }
  apply exec_refl_t.
  - auto.
  - auto.
Qed.

Corollary assert_le_fail_spec: forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: ~ v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t)
            None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros; eapply exec_t_exec, assert_le_fail_spec_t; eauto.
Qed.

Lemma assert_le_pass_spec_t : forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: v1 <= v2),
 exec_star_t t (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t)
            (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_load; auto. }
  eapply exec_step_t'; auto.
  { apply exec_load; auto. }
  eapply exec_step_t'; auto.
  { eapply exec_assert_pass; eauto.
    simpl.
    rewrite upd_old, upd_same, upd_same; eauto. }
  apply exec_refl_t.
  - auto.
  - auto.
Qed.
    
Lemma assert_le_pass_spec: forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t)
            (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros; eapply exec_t_exec, assert_le_pass_spec_t; eauto.
Qed.
  

Fixpoint hb_check C1 C2 z tmp1 tmp2 :=
match z with
| 0 => []
| S n =>(assert_le (C1,n) (C2,n) tmp1 tmp2)++ hb_check C1 C2 n tmp1 tmp2
end.

Lemma hb_check_step: forall C1 C2 n tmp1 tmp2,
 hb_check C1 C2 (S n) tmp1 tmp2 = (assert_le (C1,n) (C2,n) tmp1 tmp2)++ hb_check C1 C2 n tmp1 tmp2.
Proof.
  auto.
Qed.

Fixpoint events_hb_check (C1 C2: var) (vs1 vs2: list nat) (t:tid) : list operation :=
match (vs1,vs2) with
| (v1::vss1, v2::vss2) => events_assert_le C1 C2 t++
                               if leb v1 v2 then events_hb_check C1 C2 vss1 vss2 t else []
| _ => []
end.

Lemma events_hb_check_step : forall C1 C2 v1 v2 vs1 vs2 t,
 events_hb_check C1 C2 (v1::vs1) (v2::vs2) t = 
 events_assert_le C1 C2 t ++ 
 if leb v1 v2 then events_hb_check C1 C2 vs1 vs2 t else [].
Proof.
  auto.
Qed.


Fixpoint mops_hb_check (C1 C2: var) (vs1 vs2: list nat) (z:nat) (t:tid) : list conc_op :=
match (z,vs1,vs2) with
| (S n, v1::vss1, v2::vss2) => mops_assert_le (C1,n) (C2,n) v1 v2 t ++ 
                               (if leb v1 v2 then mops_hb_check C1 C2 vss1 vss2 n t
                               else [])
| _ => []
end.

Lemma mops_hb_check_step : forall C1 C2 v1 v2 vs1 vs2 n t,
 mops_hb_check C1 C2 (v1::vs1) (v2::vs2) (S n) t =
 mops_assert_le (C1,n) (C2,n) v1 v2 t ++
 if leb v1 v2 then mops_hb_check C1 C2 vs1 vs2 n t else [].
Proof.
  auto.
Qed.

Fixpoint first_gt l1 l2 :=
match (l1,l2) with
| (x1::xs1, x2::xs2) => if leb x1 x2 then first_gt xs1 xs2 else Some (x1,x2) 
| _   => None
end.

Lemma first_gt_step: forall x1 x2 xs1 xs2,
first_gt (x1::xs1) (x2::xs2) = if leb x1 x2 then first_gt xs1 xs2 else Some (x1,x2).
Proof.
  auto.
Qed.

Lemma hb_check_fail_spec_t : forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2
  vs1 vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star_t t (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
   (mops_hb_check C1 C2 vs1 vs2 n t)
   None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  induction n; destruct vs1, vs2; intros; subst; try solve [clarify].
  rewrite hb_check_step, events_hb_check_step, mops_hb_check_step.
  simpl in Hfirst_gt.
  destruct (leb n0 n1) eqn: Hle.
  - exploit IHn.
    { eauto. }
    { eauto. }
    { instantiate (1 := vs1); clarify. }
    { instantiate (1 := vs2); clarify. }
    { eauto. }
    instantiate (3 := upd_env (upd_env G t tmp1 n0) t tmp2 n1).
    rewrite upd_three, upd_three; auto.
    rewrite leb_le in *.
    eapply exec_star_t_trans; eauto.
    apply assert_le_pass_spec_t; auto; reflexivity.
  - inversion Hfirst_gt; subst.
    destruct (le_dec v1 v2); [rewrite <- leb_le in *; clarify|].
    eapply assert_le_fail_spec_t; auto; reflexivity.
Qed.

Corollary hb_check_fail_spec: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2
  vs1 vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
   (mops_hb_check C1 C2 vs1 vs2 n t)
   None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros; eapply exec_t_exec, hb_check_fail_spec_t; eauto.
Qed.
     
Lemma hb_check_pass_spec_t : forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest vs1
  vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = None),
 exec_star_t t (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
           (mops_hb_check C1 C2 vs1 vs2 n t) (Some (P1++(t,rest)::P2))
   (upd_env (upd_env G t tmp1 (last vs1 (G t tmp1))) t tmp2 (last vs2 (G t tmp2))).
Proof.
  induction n; destruct vs1, vs2; intros; subst; try solve [clarify].
  { repeat rewrite upd_triv; apply exec_refl_t. }
  rewrite hb_check_step, events_hb_check_step, mops_hb_check_step.
  simpl in Hfirst_gt.
  destruct (leb n0 n1) eqn: Hle; [|clarify].
  rewrite leb_le in Hle.
  exploit IHn.
  { eauto. }
  { eauto. }
  { instantiate (1 := vs1); clarify. }
  { instantiate (1 := vs2); clarify. }
  { eauto. }
  instantiate (2 := upd_env (upd_env G t tmp1 n0) t tmp2 n1).
  rewrite upd_three, upd_three; auto.
  rewrite upd_old, upd_same, upd_same; auto.
  do 2 rewrite last_cons'.
  intro; eapply exec_star_t_trans; eauto.
  apply assert_le_pass_spec_t; auto; reflexivity.
Qed.
   
Lemma hb_check_pass_spec: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest vs1
  vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = None),
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
           (mops_hb_check C1 C2 vs1 vs2 n t) (Some (P1++(t,rest)::P2))
   (upd_env (upd_env G t tmp1 (last vs1 (G t tmp1))) t tmp2 (last vs2 (G t tmp2))).
Proof.
  intros; eapply exec_t_exec, hb_check_pass_spec_t; auto.
Qed.

(* Since everything is a nat, we can use C + t as the t component of C. *)

Class metadata := { C : var; L : var; R : var; W : var; X : var;
  zt : nat; zl : nat; zv : nat; tmp1 : local; tmp2 : local;
  Htmp : tmp1 <> tmp2;
  zt_non_zero : zt <> 0;
  Hmetalocs_disjoint_CX: forall t x, (t < zt -> x < zv -> C + t <> X + x);
  Hmetalocs_disjoint_RX: forall z x,   (z < zv -> x < zv -> R + z <> X + x);
  Hmetalocs_disjoint_CR: forall t x, (t < zt -> x < zv -> C + t <> R + x);
  Hmetalocs_disjoint_CW: forall t x, (t < zt -> x < zv -> C + t <> W + x);
  Hmetalocs_disjoint_LR: forall l x, (l < zl -> x < zv -> L +l  <> R + x);
  Hmetalocs_disjoint_LW: forall l x, (l < zl -> x < zv -> L + l <> W + x);
  Hmetalocs_disjoint_WX: forall y x,  (y < zv -> x < zv -> W + y <> X + x);
  Hmetalocs_disjoint_WR: forall y x, (y < zv -> x < zv -> W + y <> R + x);
  Hmetalocs_disjoint_LX: forall l x,  (l < zl -> x < zv -> L + l <> X + x);
  Hmetalocs_disjoint_CL: forall l t,  (l < zl -> t < zt -> C + t <> L + l) }.

Section Instrumentation.

Context {meta : metadata}.

Hint Resolve Htmp.

Definition load_handler t x z := 
  Lock (X + x) :: hb_check (W + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (R + x, t) tmp1.

Lemma split_app' : forall A (x : A) l, x :: l = [x] ++ l.
Proof. auto. Qed.

Lemma load_handler_norace_spec_t : forall n x t P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1 ++ (t, load_handler t x n ++ rest) :: P2)   (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hfirst_gt : first_gt vs1 vs2 = None) v,
  exec_star_t t (Some P) G
    (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++ events_move (C + t) (R + x) t)
    (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++ mops_move (C + t, t) (R + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_lock; eauto. }
  rewrite <- app_assoc.
  eapply exec_star_t_trans.
  - eapply hb_check_pass_spec_t; try apply Hfirst_gt; eauto.
  - exploit move_spec_t; eauto.
    rewrite upd_three; eauto.
  - auto. 
  - auto.
Qed.

Corollary load_handler_norace_spec: forall n x t P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1 ++ (t, load_handler t x n ++ rest) :: P2)   (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hfirst_gt : first_gt vs1 vs2 = None) v,
  exec_star (Some P) G
    (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++ events_move (C + t) (R + x) t)
    (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++ mops_move (C + t, t) (R + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  intros; eapply exec_t_exec, load_handler_norace_spec_t; auto.
Qed.

Lemma load_handler_race_spec_t : forall n x t P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1++(t,load_handler t x n++
  rest)::P2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
  v1 v2 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star_t t (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_lock; eauto. }
  rewrite <- app_assoc.
  eapply hb_check_fail_spec_t; try apply Hfirst_gt; eauto.
  - auto.
  - auto.
Qed.  

Corollary load_handler_race_spec: forall n x t P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1++(t,load_handler t x n++
  rest)::P2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
  v1 v2 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros; eapply exec_t_exec, load_handler_race_spec_t; eauto.
Qed.

Definition store_handler t x z :=
  Lock (X + x) :: hb_check (W + x) (C + t) z tmp1 tmp2 ++
  hb_check (R + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (W + x, t) tmp1.

Lemma store_handler_race_waw_spec_t : forall n x t P G P1 P2 rest v1 v2 vs1 vs2
 (Hstore_handler_spec: P= P1++(t,store_handler t x  n++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star_t t (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2). 
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_lock; eauto. }
  rewrite <- app_assoc.
  eapply hb_check_fail_spec_t; try apply Hfirst_gt; eauto.
  - auto.
  - auto.
Qed.

Corollary store_handler_race_waw_spec: forall n x t P G P1 P2 rest v1 v2 vs1 vs2
 (Hstore_handler_spec: P= P1++(t,store_handler t x  n++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2). 
Proof.
  intros; eapply exec_t_exec, store_handler_race_waw_spec_t; eauto.
Qed.

Lemma store_handler_race_war_spec_t : forall n x t P G P1 P2 rest v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x n ++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 = n) 
 (Hfirst_gt12: first_gt vs1 vs2 = None)
 (Hfirst_gt32: first_gt vs3 vs2 = Some (v3,v2)),
 exec_star_t t (Some P) G 
           (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
            events_hb_check (R + x) (C + t) vs3 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
            mops_hb_check (R + x) (C + t) vs3 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v3) t tmp2 v2). 
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_lock; eauto. }
  repeat rewrite <- app_assoc.
  eapply exec_star_t_trans; [apply hb_check_pass_spec_t; try apply Hfirst_gt12;
                            eauto|].
  exploit hb_check_fail_spec_t; try apply Hfirst_gt32; eauto.
  instantiate (5 := upd_env (upd_env G t tmp1 (last vs1 (G t tmp1))) t tmp2
        (last vs2 (G t tmp2))).
  rewrite upd_three, upd_three; eauto.
  - auto.
  - auto.
Qed.

Lemma store_handler_race_war_spec: forall n x t P G P1 P2 rest v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x n ++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 = n) 
 (Hfirst_gt12: first_gt vs1 vs2 = None)
 (Hfirst_gt32: first_gt vs3 vs2 = Some (v3,v2)),

 exec_star (Some P) G 
           (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
            events_hb_check (R + x) (C + t) vs3 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
            mops_hb_check (R + x) (C + t) vs3 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v3) t tmp2 v2). 
Proof.
  intros; eapply exec_t_exec, store_handler_race_war_spec_t; eauto.
Qed.

(* up *)
Lemma last_last : forall A (d : A) l, last l (last l d) = last l d.
Proof.
  destruct l; clarify.
  apply last_def; clarify.
Qed.

Lemma store_handler_norace_spec_t : forall n x t P G P1 P2 rest
  vs1 vs2 vs3 (Hstore_handler_spec: P = P1 ++ (t, store_handler t x n
  ++ rest) :: P2) (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hvs3: length vs3 = n) (Hfirst_gt12 : first_gt vs1 vs2 = None) (Hfirst_gt32: first_gt vs3 vs2 = None) v,
  exec_star_t t (Some P) G
    (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++ 
     events_hb_check (R + x) (C + t) vs3 vs2 t ++
     events_move (C + t) (W + x) t)
    (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
     mops_hb_check (R + x) (C + t) vs3 vs2 n t ++
     mops_move (C + t, t) (W + x, t) t v )
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  clarify.
  eapply exec_step_t'.
  { apply exec_lock; eauto. }
  repeat rewrite <- app_assoc.
  eapply exec_star_t_trans; [apply hb_check_pass_spec_t; try apply Hfirst_gt12;
                            eauto|].
  eapply exec_star_t_trans; [apply hb_check_pass_spec_t; try apply Hfirst_gt32;
                            eauto|].
  repeat rewrite upd_three; auto.
  rewrite upd_old, upd_same, upd_same; auto.
  repeat rewrite last_last.
  exploit move_spec_t; eauto.
  rewrite upd_three; eauto.
  - auto.
  - auto.
Qed.

Corollary store_handler_norace_spec: forall n x t P G P1 P2 rest
  vs1 vs2 vs3 (Hstore_handler_spec: P = P1 ++ (t, store_handler t x n
  ++ rest) :: P2) (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hvs3: length vs3 = n) (Hfirst_gt12 : first_gt vs1 vs2 = None) (Hfirst_gt32: first_gt vs3 vs2 = None) v,
  exec_star (Some P) G
    (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++ 
     events_hb_check (R + x) (C + t) vs3 vs2 t ++
     events_move (C + t) (W + x) t)
    (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
     mops_hb_check (R + x) (C + t) vs3 vs2 n t ++
     mops_move (C + t, t) (W + x, t) t v )
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  intros; eapply exec_t_exec, store_handler_norace_spec_t; auto.
Qed.
   
Definition lock_handler t l z :=
  max_vc (L+l) (C+t) z tmp1 tmp2.

(* up! *)
Lemma last_single : forall A (x d : A), last [x] d = x.
Proof. auto. Qed.

Lemma lock_handler_spec_t : forall n t l P G P1 P2 rest vs1 vs2 v
  (HP : P = P1 ++ (t, lock_handler t l n ++ rest) :: P2)
  (Hlen1 : length vs1 = n) (Hlen2 : length vs2 = n) (Hn : n <> 0),
  exec_star_t t (Some P) G (events_max_vc (L + l) (C + t) t n)
    (mops_max_vc (L + l) (C + t) vs1 vs2 t n) (Some (P1 ++ (t, rest) :: P2))
    (upd_env (upd_env G t tmp1 (last vs1 0)) t tmp2
       (Peano.max (last vs1 v) (last vs2 v))).
Proof.
  induction n; clarify.
  destruct vs1, vs2; clarify.
  eapply exec_step_t'; eauto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_assign; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_store; eauto. }
  instantiate (1 := mops_max_vc (L + l) (C + t) vs1 vs2 t n).
  instantiate (1 := events_max_vc (L + l) (C + t) t n).
  rewrite upd_overwrite.
  destruct (eq_dec n 0).
  - clarify.
    destruct vs1; clarify.
    repeat rewrite last_single.
    rewrite upd_old, upd_same, upd_same; auto.
    apply exec_refl_t.
  - repeat rewrite last_cons; try solve [intro; clarify; omega].
    exploit IHn.
    { eauto. }
    { instantiate (1 := vs1); auto. }
    { instantiate (1 := vs2); auto. }
    { auto. }
    instantiate (5 := upd_env (upd_env G t tmp1 n0) t tmp2
        (eval (upd_env (upd_env G t tmp1 n0) t tmp2 n1 t)
           (Max (V tmp1) (V tmp2)))).
    setoid_rewrite upd_assoc at 2; auto.
    rewrite upd_overwrite.
    setoid_rewrite upd_assoc at 2; auto.
    rewrite upd_overwrite; eauto.
  - auto.
  - simpl.
    rewrite upd_overwrite, upd_same, upd_same.
    rewrite upd_assoc, upd_same; auto.
Qed.  

Corollary lock_handler_spec : forall n t l P G P1 P2 rest vs1 vs2 v
  (HP : P = P1 ++ (t, lock_handler t l n ++ rest) :: P2)
  (Hlen1 : length vs1 = n) (Hlen2 : length vs2 = n) (Hn : n <> 0),
  exec_star (Some P) G (events_max_vc (L + l) (C + t) t n)
    (mops_max_vc (L + l) (C + t) vs1 vs2 t n) (Some (P1 ++ (t, rest) :: P2))
    (upd_env (upd_env G t tmp1 (last vs1 0)) t tmp2
       (Peano.max (last vs1 v) (last vs2 v))).
Proof.
  intros; eapply exec_t_exec, lock_handler_spec_t; auto.
Qed.

Definition unlock_handler t m z tmp :=
  set_vc (C + t) (L + m) z tmp ++ inc_vc t (C + t) tmp.

Lemma unlock_handler_spec_t : forall n u tmp P G P1 P2 t rest vss vt
(Hset_vc: P=P1++(t, unlock_handler t u n tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star_t t (Some P) G
          (events_set_vc (C+t)(L+u) n t++(events_inc_vc (C+t) t)) (mops_set_vc (C+t) (L+u) n t vss++ (mops_inc_vc (C+t) vt t)) (Some (P1++(t,rest)::P2)) (upd_env G t tmp (vt+1)).
Proof.
  clarify.
  setoid_rewrite <- app_assoc.
  eapply exec_star_t_trans; [apply set_vc_spec_t; eauto|].
  exploit inc_vc_spec_t; eauto.
  rewrite upd_overwrite; eauto.
Qed.

Corollary unlock_handler_spec : forall n u tmp P G P1 P2 t rest vss vt
(Hset_vc: P=P1++(t, unlock_handler t u n tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star (Some P) G
          (events_set_vc (C+t)(L+u) n t++(events_inc_vc (C+t) t)) (mops_set_vc (C+t) (L+u) n t vss++ (mops_inc_vc (C+t) vt t)) (Some (P1++(t,rest)::P2)) (upd_env G t tmp (vt+1)).
Proof.
  intros; eapply exec_t_exec, unlock_handler_spec_t; auto.
Qed.

Definition spawn_handler t l z :=
  max_vc (C + t) (C+l) z tmp1 tmp2 ++ inc_vc t (C + t) tmp1.

Lemma spawn_handler_spec_t : forall n l P G P1 P2 t rest vss1 vss2 vt
(Hset_vc: P=P1++(t, spawn_handler t l n ++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n) (Htmp: tmp1<>tmp2),
 exec_star_t t (Some P) G
          (events_max_vc (C+t)(C+l) t n++(events_inc_vc (C+t) t)) (mops_max_vc (C+t) (C+l) vss1 vss2 t n ++ (mops_inc_vc (C+t) vt t)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp2 (last (map (fun x => Peano.max (fst x) (snd x))
  (combine vss1 vss2)) (G t tmp2))) t tmp1 (vt+1)).
Proof.
  clarify.
  setoid_rewrite <- app_assoc.
  eapply exec_star_t_trans; [apply max_vc_spec_t; eauto|].
  exploit inc_vc_spec_t; eauto.
  instantiate (4 := upd_env (upd_env G t tmp1 (last vss1 (G t tmp1))) t tmp2
    (last (map (fun x => Peano.max (fst x) (snd x)) (combine vss1 vss2))
          (G t tmp2))).
  rewrite upd_three; auto.
  rewrite upd_assoc with (v1 := vt + 1); eauto.
Qed.

Lemma spawn_handler_spec : forall n l P G P1 P2 t rest vss1 vss2 vt
(Hset_vc: P=P1++(t, spawn_handler t l n ++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n) (Htmp: tmp1<>tmp2),
 exec_star (Some P) G
          (events_max_vc (C+t)(C+l) t n++(events_inc_vc (C+t) t)) (mops_max_vc (C+t) (C+l) vss1 vss2 t n ++ (mops_inc_vc (C+t) vt t)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp2 (last (map (fun x => Peano.max (fst x) (snd x))
  (combine vss1 vss2)) (G t tmp2))) t tmp1 (vt+1)).
Proof.
  intros; eapply exec_t_exec, spawn_handler_spec_t; auto.
Qed.


Definition wait_handler t u z :=
  max_vc (C + u) (C + t) z tmp1 tmp2
         ++inc_vc u (C + u) tmp1.

Lemma wait_handler_spec_t : forall n t u P G P1 P2 rest vs1 vs2 v
  (HP : P = P1 ++ (t, wait_handler t u n ++ rest) :: P2)
  (Hlen1 : length vs1 = n) (Hlen2 : length vs2 = n) (Hn : n <> 0),
  exec_star_t t (Some P) G
    (events_max_vc (C + u) (C + t) t n ++ events_inc_vc (C + u) t)
    (mops_max_vc (C + u) (C + t) vs1 vs2 t n ++ mops_inc_vc' (C + u) v t u)
    (Some (P1 ++ (t, rest) :: P2))
    (upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
             t tmp1 (v + 1)).
Proof.
  induction n; clarify.
  destruct vs1, vs2; clarify.
  eapply exec_step_t'; eauto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_assign; eauto. }
  rewrite upd_overwrite; simpl.
  rewrite upd_same, upd_old, upd_same; auto.
  eapply exec_step_t'; eauto.
  { apply exec_store; eauto. }
  instantiate (1 := mops_max_vc (C + u) (C + t) vs1 vs2 t n ++
    mops_inc_vc' (C + u) v t u).
  instantiate (1 := events_max_vc (C + u) (C + t) t n ++
    events_inc_vc (C + u) t).
  destruct (eq_dec n 0).
  - destruct vs1, vs2; clarify.
    repeat rewrite last_single.
    eapply exec_step_t'; eauto.
    { apply exec_load; eauto. }
    eapply exec_step_t'; eauto.
    { apply exec_assign; eauto. }
    simpl; eapply exec_step_t'; eauto.
    { apply exec_store; eauto. }
    repeat rewrite upd_three; auto.
    rewrite upd_old, upd_same, upd_assoc; auto.
    apply exec_refl_t.
    + auto.
    + simpl.
      repeat rewrite upd_same; auto.
  - repeat rewrite last_cons; try solve [intro; clarify; omega].
    exploit IHn.
    { eauto. }
    { instantiate (1 := vs1); auto. }
    { instantiate (1 := vs2); auto. }
    { auto. }
    instantiate (4 := upd_env (upd_env G t tmp1 n0) t tmp2 (Peano.max n0 n1)).
    rewrite upd_overwrite.
    rewrite upd_three; auto.
    setoid_rewrite upd_assoc at 2; eauto.
  - auto.
  - simpl.
    rewrite upd_same; auto.
Qed.  

Corollary wait_handler_spec : forall n t u P G P1 P2 rest vs1 vs2 v
  (HP : P = P1 ++ (t, wait_handler t u n ++ rest) :: P2)
  (Hlen1 : length vs1 = n) (Hlen2 : length vs2 = n) (Hn : n <> 0),
  exec_star (Some P) G
    (events_max_vc (C + u) (C + t) t n ++ events_inc_vc (C + u) t)
    (mops_max_vc (C + u) (C + t) vs1 vs2 t n ++ mops_inc_vc' (C + u) v t u)
    (Some (P1 ++ (t, rest) :: P2))
    (upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
             t tmp1 (v + 1)).
Proof.
  intros; eapply exec_t_exec, wait_handler_spec_t; auto.
Qed.

(* Note that for now, we assign metadata to a block, rather than to
   offsets within that block. *)
Fixpoint instrument_instr (ins : instr) (t : tid)
  : prog :=
let instrument := fix f p t :=
  match p with
  | [] => []
  | ins::inss => (instrument_instr ins t)++(f inss t)
  end in
(match ins with
 | Load a (x, _)   => load_handler t x zt ++ [ins; Unlock (X + x)]
 | Store (x, _) e  => store_handler t x zt ++ [ins; Unlock (X + x)]
 | Lock l          => [ins] ++ lock_handler t l zt
 | Unlock l   => unlock_handler t l zt  tmp1++ [ins]
 | Spawn u li =>  spawn_handler t u zt ++ [Spawn u (instrument li u)] 
 | Wait u     => [ins] ++ wait_handler t u zt
 | _          => [ins]
end).

Fixpoint instrument (p: prog) (t: tid) : prog:=
match p with
| [] => []
| ins::inss => (instrument_instr ins t)++(instrument inss t)
end.

Lemma instrument_nonnil : forall i t, instrument_instr i t <> [].
Proof.
  destruct i; repeat intro; clarify.
  - destruct x, zt; clarify.
  - destruct x, zt; clarify.
  - destruct zt; clarify.
  - destruct zt; clarify.
Qed.

Section Sim_Defs.

Context {ML : @Memory_Layout var nat _}.

Definition vstate := @VectorClocks.state tid var lock.

Definition clock_match m V x := forall t,
  if lt_dec t zt then can_read m (x, t) (V t) /\ can_write m (x, t)
  else V t = 0.

Definition clocks_sim (m : list conc_op) (s : vstate) :=
  (forall t, t < zt -> clock_match m (clock_of s t) (C + t)) /\
  (forall l, l < zl -> clock_match m (lock_of s l) (L + l)) /\
  (forall v, v < zv -> clock_match m (read_of s v) (R + v) /\
     clock_match m (write_of s v) (W + v)) (*/\
  (forall x, x < zv -> can_read m (X+x,0) 0 /\ can_write m (X+x,0)) *) .

(* returns true if v is not used in e*)
Fixpoint expr_fresh (v : local) (e : expr) :=
  match e with
  | I _ => True
  | V v' => v <> v'
  | Plus e1 e2 => expr_fresh v e1 /\ expr_fresh v e2
  | Max e1 e2 => expr_fresh v e1 /\ expr_fresh v e2
  end.
(* returns true if v is not used in i*)
Fixpoint fresh (v : local) (i : instr) :=
  let list_fresh := fix list_fresh l :=
    match l with
    | [] => True
    | i :: rest => fresh v i /\ list_fresh rest
    end in
  match i with
  | Assign v' e => v <> v' /\ expr_fresh v e
  | Load v' _ => v <> v'
  | Store _ e => expr_fresh v e
  | Assert_le e1 e2 => expr_fresh v e1 /\ expr_fresh v e2
  | Spawn _ li => list_fresh li
  | _ => True
  end.

(*P2 is the instrumented program of P1*)
Definition state_sim (P1 P2 : state) := Forall2 (fun t1 t2 => fst t1 = fst t2 /\
  snd t2 = instrument (snd t1) (fst t1)) P1 P2.
(*all locals except tmp1 or tmp2 in G1 & G2 have the same values *)
Definition env_sim (G1 G2 : env) := forall t v, v <> tmp1 -> v <> tmp2 ->
  G1 t v = G2 t v.
(*tmp1 & tmp2 are not used in P*)
Definition fresh_tmps (P : state) :=
  Forall (fun e => Forall (fun i => fresh tmp1 i /\ fresh tmp2 i) (snd e)) P.
(* checks whether x points to some meta location *)
Definition meta_loc (x : ptr) := C <= fst x < C + zt \/
  L <= fst x < L + zl \/ R <= fst x < R + zv \/ W <= fst x < W + zv \/ X <= fst x < X+zv.

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

(* m2 holds the set of values in m1 + the meta locations*)
Definition mem_sim (m1 : option conc_op) (m2 : list conc_op) :=
  forall c, In c (opt_to_list m1) <-> In c m2 /\ ~meta_loc (loc_of c).

Instance ptr_eq : EqDec_eq ptr.
Proof. eq_dec_inst. Qed.

Lemma fresh_tmps_step : forall P G t o c P' G' (Hfresh : fresh_tmps P)
  (Hstep : exec P G t o c P' G'),
  match P' with Some P' => fresh_tmps P' | None => True end.
Proof.
  unfold fresh_tmps; intros; induction Hstep; clarify; rewrite Forall_app in *;
    clarify; inversion Hfresh2 as [|? ? Hi]; clarify; inversion Hi; clarify;
    constructor; auto.
  constructor; auto.
  clear - H21 H22.
  induction li; clarify.
Qed.

(* an instruction is safe if it only accesses the part of memory that does not
   hold meta locations. *)
Fixpoint safe_instr (i : instr) :=
  let list_safe := fix list_safe l :=
    match l with
    | [] => True
    | i :: rest => safe_instr i /\ list_safe rest
    end in
  match i with
  | Assign v' e => True
  | Load _ p => ~meta_loc p /\ fst p < zv
  | Store p _ => ~meta_loc p /\ fst p < zv
  | Lock m => ~meta_loc (m, 0) /\ m < zl
  | Unlock m => ~meta_loc (m, 0) /\ m < zl
  | Spawn u li => u < zt /\ list_safe li
  | Wait u => u < zt
  | Assert_le _ _ => True (* should this be False? *)
  end.

(* all the instructions in P are safe*)
Definition safe_locs (P : state) :=
  Forall (fun e => Forall safe_instr (snd e)) P.

Lemma safe_locs_step : forall P G t o c P' G' (Hlocs : safe_locs P)
  (Hstep : exec P G t o c P' G'),
  match P' with Some P' => safe_locs P' | None => True end.
Proof.
  unfold safe_locs; intros; induction Hstep; clarify; rewrite Forall_app in *;
    clarify; inversion Hlocs2 as [|? ? Hi]; clarify; inversion Hi; clarify;
    constructor; auto.
  constructor; auto.
  simpl.
  clear Hlocs2 Hnew Hi.
  induction li; clarify.
Qed.  

(* if all locals used in e have the same values in G1 & G2, then e evaluates to the same result under G1 & G2*)
Lemma eval_sim : forall G1 G2 e (Hsim : forall v, ~expr_fresh v e ->
  G1 v = G2 v), eval G1 e = eval G2 e.
Proof.
  induction e; clarify.
  - rewrite IHe1, IHe2; auto.
    + intros; apply Hsim; intro; clarify.
    + intros; apply Hsim; intro; clarify.
  - rewrite IHe1, IHe2; auto.
    + intros; apply Hsim; intro; clarify.
    + intros; apply Hsim; intro; clarify.
Qed.

(* if two vector clocks V1 <= V2, then no value in V1 could be greater than its counterpart in V2 *)
Lemma vc_le_first_gt : forall V1 V2 (Hle : vc_le(tid := tid) V1 V2) l,
  first_gt (map V1 l) (map V2 l) = None.
Proof.
  induction l; clarify.
  specialize (Hle a); rewrite <- leb_le in Hle; clarify.
Qed.

Lemma C_meta : forall t (Ht : t < zt) o, meta_loc (C + t, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed. 

Lemma X_meta : forall v (Ht : v < zv) o, meta_loc (X + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.
Lemma R_meta : forall v (Ht : v < zv) o, meta_loc (R + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma W_meta : forall v (Ht : v < zv) o, meta_loc (W + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma L_meta : forall l (Ht : l < zl) o, meta_loc (L + l, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

(* all the memory operations only access meta locations*)
Lemma mops_hb_check_meta : forall l1 l2 n x t c (Hx : x < zv) (Ht : t < zt)
  (Hin : In c (mops_hb_check (W + x) (C + t) l1 l2 n t)\/ In c (mops_hb_check (R+x) (C+t) l1 l2 n t)) , meta_loc (loc_of c).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  destruct Hin as [[? | [? | ?]] | [? | [? | ?]]]; clarify;
    try apply W_meta; try apply R_meta; try apply C_meta; eauto.
Qed.

(* all the memory operations only access meta locations*)
Lemma mops_max_vc_meta: forall l1 l2 n m0 t c (Hx : m0 < zl) (Ht : t < zt)
  (Hin : In c (mops_max_vc (L + m0) (C + t) l1 l2 t n)\/ In c (mops_max_vc (C+t) (L + m0) l1 l2 t n)) , meta_loc (loc_of c).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  destruct Hin as [[? | [? | [? | ?]]] | [? | [? | [? | ?]]]]; clarify;
    try apply L_meta; try apply C_meta; eauto.
Qed.

Notation lower := (@lower _ _ _ _ _ Base).

(* hb_check only generate reads to the memory*)
Lemma mops_hb_check_read : forall C1 C2 l1 l2 n t,
  Forall (fun x => match x with Read _ _ _ => True | _ => False end)
    (mops_hb_check C1 C2 l1 l2 n t).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
Qed.


(* mops generated by hb_check are consistent?*)
Lemma mops_hb_check_con : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  consistent (m ++ (mops_hb_check (W + x) (C + t) (map (write_of s x) (rev (interval 0 n)))
                   (map (clock_of s t) (rev (interval 0 n))) n t)).
Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  simpl.
  rewrite rev_app_distr; clarify.
  do 2 rewrite read_noop_SC.
  - destruct (write_of s x n <=? clock_of s t n); clarsimp.
    apply IHn; auto; omega.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
  - clarsimp.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs222 n); clarify.
    apply can_read_thread; auto.
Qed.


Lemma mops_max_vc_off : forall src tgt f g t n,
  Forall (fun c' => match loc_of c' with (x, o) => o < n end)
     (mops_max_vc src tgt (map f (rev (interval 0 n)))
        (map g (rev (interval 0 n))) t n).
Proof.
  induction n; clarify.
  rewrite rev_app_distr; clarify.
  repeat (constructor; clarify).
  eapply Forall_impl; eauto; clarify.
  destruct (loc_of a); omega.
Qed.

Lemma max_vc_prog : forall src tgt t z vs1 vs2,
  Forall prog_op (mops_max_vc src tgt vs1 vs2 t z).
Proof.
  induction z; intros; destruct vs1; clarify; destruct vs2; clarify.
  repeat constructor; clarify.
Qed.
Hint Resolve max_vc_prog.

(* mops generated by max_vc are consistent?*)
Lemma mops_max_vc_con_lc : forall m s (Hs : clocks_sim m s) m0 t0 n
  (Hn : n <= zt) (Hl : m0 < zl) (Ht : t0 < zt) (Hcon : consistent m),
  consistent (m ++ 
    (mops_max_vc (L + m0) (C + t0) (map (lock_of s m0) (rev (interval 0 n)))
       (map (clock_of s t0) (rev (interval 0 n))) t0 n)).
Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  unfold clocks_sim in Hs; clarify.
  do 2 rewrite read_noop_SC.
  - rewrite loc_valid_ops2_SC; clarify; try split.
    + apply IHn; auto; omega.
    + specialize (Hs1 _ Ht n); clarify.
      apply can_write_thread; auto.
    + simpl.
      eapply Forall_impl; [|apply mops_max_vc_off]; clarify.
      destruct (loc_of a); intro; clarify; omega.
  - specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
  - clarsimp.
  - specialize (Hs21 _ Hl); clarify.
    specialize (Hs21 n); clarify.
    apply can_read_thread; auto.
Qed.

(* mops generated by max_vc are consistent?*)
Lemma mops_max_vc_con_cl : forall m s (Hs : clocks_sim m s) m0 t0 n
  (Hn : n <= zt) (Hl : m0 < zl) (Ht : t0 < zt) (Hcon : consistent m),
  consistent (m ++ (mops_max_vc (C + t0) (L + m0) (map (clock_of s t0) (rev (interval 0 n))) (map (lock_of s m0) (rev (interval 0 n)))
            t0 n)).

Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  unfold clocks_sim in Hs; clarify.
  do 2 rewrite read_noop_SC.
  - rewrite loc_valid_ops2_SC; clarify; try split.
    + apply IHn; auto; omega.
    + specialize (Hs21 _ Hl n); clarify.
      apply can_write_thread; auto.
    + simpl.
      eapply Forall_impl; [|apply mops_max_vc_off]; clarify.
      destruct (loc_of a); intro; clarify; omega.
  - specialize (Hs21 _ Hl n); clarify.
    apply can_read_thread; auto.
  - clarsimp.
  - specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
Qed.

(* mops generated by hb_check are consistent?*)
Lemma mops_hb_check_conR : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  consistent (m ++
    (mops_hb_check (R + x) (C + t) (map (read_of s x) (rev (interval 0 n)))
      (map (clock_of s t) (rev (interval 0 n))) n t)).
Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  simpl.
  rewrite rev_app_distr; clarify.
  do 2 rewrite read_noop_SC.
  - destruct (read_of s x n <=? clock_of s t n); clarsimp.
    apply IHn; auto; omega.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
  - clarsimp.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs221 n); clarify.
    apply can_read_thread; auto.
Qed.

(*mops generated by move are consistent?*)
Lemma mops_move_con : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  consistent (m ++ mops_move (C + t, t) (R + x, t) t (clock_of s t t)).
Proof.
  unfold mops_move; clarify.
  unfold clocks_sim in Hs; clarify.
  rewrite read_noop_SC.
  - specialize (Hs22 _ Hx); clarify.
    specialize (Hs221 t); clarify.
    apply can_write_thread; auto.
  - specialize (Hs1 _ Ht t); clarify.
    apply can_read_thread; auto.
Qed.

(*mops generated by move are consistent?*)
Lemma mops_move_conW : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  consistent (m ++ mops_move (C + t, t) (W + x, t) t (clock_of s t t)).
Proof.
  unfold mops_move; clarify.
  unfold clocks_sim in Hs; clarify.
  rewrite read_noop_SC.
  - specialize (Hs22 _ Hx); clarify.
    specialize (Hs222 t); clarify.
    apply can_write_thread; auto.
  - specialize (Hs1 _ Ht t); clarify.
    apply can_read_thread; auto.
Qed.

Lemma upd_tmps: forall v e G1 G2 t0 v1 v2 
 (HGsim: env_sim G1 G2) (Htmp1: expr_fresh tmp1 e) (Htmp2: expr_fresh tmp2 e), 
   ~ expr_fresh v e ->
   upd_env (upd_env G2 t0 tmp1 v1) t0 tmp2 v2 t0 v = G1 t0 v.
Proof.
  intros.
  repeat rewrite upd_old; eauto.
  -symmetry. apply HGsim.
   +destruct (eq_dec v tmp1); clarify; eauto.
   +destruct (eq_dec v tmp2). clarify. eauto.
  -destruct (eq_dec tmp1 v). clarify. eauto.
  -destruct (eq_dec tmp2 v). clarify. eauto. 
Qed.
 
Lemma eval_old: forall G1 G2 t0 v1 v2 e (HGsim: env_sim G1 G2) (Htmp1: expr_fresh tmp1 e) (Htmp2: expr_fresh tmp2 e), eval (upd_env (upd_env G2 t0 tmp1 v1) t0 tmp2 v2 t0) e = eval (G1 t0) e.
Proof.
  intros.
  apply eval_sim. intros.
  eapply upd_tmps; eauto.
Qed.

Lemma store_tmps_fresh : forall (P0 P3:state) rest t0 ptr e (Hfresh : fresh_tmps (P0 ++ (t0, Store ptr e :: rest) :: P3)), expr_fresh tmp1 e /\ expr_fresh tmp2 e.
Proof.
  intros.
  setoid_rewrite Forall_app in Hfresh; clarify; inversion Hfresh2; clarify. 
  inversion H1; clarify.
Qed.

Lemma in_mops_hb_check: forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_hb_check vc1 vc2 vs1 vs2 n t) ),
  match c with
  | Read _ p _ => fst p = vc1 \/ fst p = vc2
  | _          => False
  end.
Proof.
  intro n.
  induction n; intros; destruct c,vs1,vs2; clarify.
  -inversion Hin; clarify.
   +left. inversion H; clarify.
   +inversion H; clarify.
    *right. inversion H0; clarify.
    *specialize(IHn _ _ _ _ _ _ H0); clarify.
  -specialize(IHn _ _ _ _ _ _ Hin); clarify.
  -specialize(IHn _ _ _ _ _ _ Hin); clarify.
  -exploit IHn; eauto.
  -exploit IHn; eauto.
Qed.

Lemma in_mops_max_vc: forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_max_vc vc1 vc2 vs1 vs2 t n)) (Hdis: vc1<>vc2),
  match c with 
  | Write tc p _ => fst p <> vc1
  | Read tc p _  => fst p = vc1 \/ fst p = vc2
  | _ => False
  end.
Proof.
  induction n; intros; destruct vs1; clarify; destruct vs2; clarify.
  destruct c; clarify; exploit IHn; eauto.
Qed.

Lemma in_mops_set_vc: forall n c vc1 vc2 vs t
  (Hin: In c (mops_set_vc vc1 vc2 n t vs)) (Hdis: vc1<>vc2),
match c with
    | Read _ _ _ => True
    | Write _ x _ => (vc1, t) <> x
    | _ => False
  end.
Proof.
  induction n; intros; destruct vs; clarify; destruct c; clarify;
    try solve [exploit IHn; eauto].
  destruct Hin; [|exploit IHn; eauto].
  inversion H; intro; clarify.
Qed.

Lemma mops_set_vc_meta_cl: forall n vs u t c (Hx : u < zl) (Ht : t < zt)
  (Hin : In c (mops_set_vc (C + t) (L + u) n t vs )), meta_loc (loc_of c).
Proof.
  induction n; clarify.
  destruct vs; clarify.
  destruct Hin as [? | [? | ?]]; clarify; try apply C_meta; try apply L_meta;
    eauto.
Qed.



Lemma mops_max_vc_con_cc : forall m s (Hs : clocks_sim m s) u t0 n
  (Hn : n <= zt) (Hu : u < zt) (Ht : t0 < zt) (Hcon : consistent m),
  consistent (m ++ 
    (mops_max_vc (C + u) (C + t0) (map (clock_of s u) (rev (interval 0 n)))
       (map (clock_of s t0) (rev (interval 0 n))) t0 n)).

Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  unfold clocks_sim in Hs; clarify.
  do 2 rewrite read_noop_SC.
  - rewrite loc_valid_ops2_SC; clarify; try split.
    + apply IHn; auto; omega.
    + specialize (Hs1 _ Ht n); clarify.
      apply can_write_thread; auto.
    + simpl.
      eapply Forall_impl; [|apply mops_max_vc_off]; clarify.
      destruct (loc_of a); intro; clarify; omega.
  - specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
  - clarsimp.
  -
    specialize (Hs1 _ Hu); clarify.
    specialize (Hs1 n); clarify.
    apply can_read_thread; auto.
Qed.

Lemma mops_max_vc_con_cc' : forall m s (Hs : clocks_sim m s) u t0 n
  (Hn : n <= zt) (Hu : u < zt) (Ht : t0 < zt) (Hcon : consistent m),
  consistent (m ++ 
    (mops_max_vc (C + u) (C + t0) (map (clock_of s u) (rev (interval 0 n)))
       (map (clock_of s t0) (rev (interval 0 n))) u n)).

Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  unfold clocks_sim in Hs; clarify.
  do 2 rewrite read_noop_SC.
  - rewrite loc_valid_ops2_SC; clarify; try split.
    + apply IHn; auto; omega.
    + specialize (Hs1 _ Ht n); clarify.
      apply can_write_thread; auto.
    + simpl.
      eapply Forall_impl; [|apply mops_max_vc_off]; clarify.
      destruct (loc_of a); intro; clarify; omega.
  - specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
  - clarsimp.
  -
    specialize (Hs1 _ Hu); clarify.
    specialize (Hs1 n); clarify.
    apply can_read_thread; auto.
Qed.

Lemma mops_set_vc_off : forall src tgt f t n,
  Forall (fun c' => match loc_of c' with (x, o) => o < n end)
     (mops_set_vc src tgt n t (map f (rev (interval 0 n)))).
Proof.
  induction n; clarify.
  rewrite rev_app_distr; clarify.
  repeat (constructor; clarify).
  eapply Forall_impl; eauto; clarify.
  destruct (loc_of a); omega.
Qed.

Lemma set_vc_prog : forall src tgt z t vs,
  Forall prog_op (mops_set_vc src tgt z t vs).
Proof.
  induction z; intros; destruct vs; clarify.
  repeat constructor; clarify.
Qed.
Hint Resolve set_vc_prog.

Lemma mops_set_vc_con_cl : forall m s (Hs : clocks_sim m s) u t0 n
  (Hn : n <= zt) (Hu : u < zl) (Ht : t0 < zt) (Hcon : consistent m),
  consistent (m ++ 
    (mops_set_vc (C + t0) (L + u) n t0 (map (clock_of s t0) (rev (interval 0 n))))).
Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  unfold clocks_sim in Hs; clarify.
  
  rewrite read_noop_SC.
  - rewrite loc_valid_ops2_SC; clarify; try split.
    + apply IHn; auto; omega.
    + specialize (Hs21 _ Hu n); clarify.
      apply can_write_thread; auto.
    + simpl.
      eapply Forall_impl; [|apply mops_set_vc_off]; clarify.
      destruct (loc_of a); intro; clarify; omega.
  - specialize (Hs1 _ Ht n); clarify.
    apply can_read_thread; auto.
Qed.

Lemma mops_max_vc_meta_cc: forall l1 l2 n u t c (Hx : u < zt) (Ht : t < zt)
  (Hin : In c (mops_max_vc (C + u) (C + t) l1 l2 t n)\/ In c (mops_max_vc (C+t) (C + u) l1 l2 t n)) , meta_loc (loc_of c).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  destruct Hin as [[? | [? | [? | ?]]] | [? | [? | [? | ?]]]]; clarify;
    try apply C_meta; eauto.
Qed.

Lemma hb_check_prog : forall C1 C2 z t vs1 vs2,
  Forall prog_op (mops_hb_check C1 C2 vs1 vs2 z t).
Proof.
  induction z; intros; destruct vs1; clarify; destruct vs2; clarify.
  repeat constructor; clarify.
Qed.
Hint Resolve hb_check_prog.

(* Bigger-step semantics *)
Inductive iexec P G t :
    list operation -> list conc_op -> state -> env -> Prop :=
  | iexec_assign P1 P2 a e rest
      (Hassign : P = P1 ++ (t, Assign a e :: rest) :: P2) :
      iexec P G t [] []
        (P1 ++ (t, rest) :: P2) (upd_env G t a (eval (G t) e))
  | iexec_load P1 P2 a x o vt v rest vs1 vs2
      (Hload : P = P1 ++ (t, load_handler t x zt ++
                             Load a (x, o) :: Unlock (X + x) :: rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt)
      (Hle : first_gt vs1 vs2 = None)  :
      iexec P G t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
                   events_move (C + t) (R + x) t ++ [rd t x; rel t (X + x)])
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                   mops_move (C + t, t) (R + x, t) t vt ++
                   [Read t (x, o) v; Rel t (X + x)])
        (P1 ++ (t, rest) :: P2)
        (upd_env (upd_env (upd_env G t tmp1 vt) t tmp2 (last vs2 (G t tmp2)))
           t a v)
  | iexec_store P1 P2 x o e rest vs1 vs2 vs3 v
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt)
      (Hlen3 : length vs3 = zt) (Hle1 : first_gt vs1 vs2 = None)
      (Hle2 : first_gt vs3 vs2 = None)
      (Hfresh1 : expr_fresh tmp1 e) (Hfresh2 : expr_fresh tmp2 e) :
      iexec P G t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
                   events_hb_check (R + x) (C + t) vs3 vs2 t ++
                   events_move (C + t) (W + x) t ++ [wr t x; rel t (X + x)])
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                   mops_hb_check (R + x) (C + t) vs3 vs2 zt t ++
                   mops_move (C + t, t) (W + x, t) t v ++
                   [Write t (x, o) (eval (G t) e); Rel t (X + x)])
        (P1 ++ (t, rest) :: P2)
        (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2)))
  | iexec_lock P1 P2 m rest vs1 vs2
      (Hlock : P = P1 ++ (t, Lock m ::
                             lock_handler t m zt ++ rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) (Hlt : t < zt) :
      iexec P G t (acq t m :: events_max_vc (L + m) (C + t) t zt)
                  (ARW t (m, 0) 0 (S t) ::
                   mops_max_vc (L + m) (C + t) vs1 vs2 t zt)
        (P1 ++ (t, rest) :: P2) (upd_env (upd_env G t tmp1 (last vs1 0)) 
          t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
  | iexec_unlock P1 P2 m rest vs v
      (Hunlock : P = P1 ++ (t, unlock_handler t m zt tmp1 ++
                               Unlock m :: rest) :: P2)
      (Hlen : length vs = zt) :
      iexec P G t (events_set_vc (C + t) (L + m) zt t ++
                   events_inc_vc (C + t) t ++ [rel t m])
                  (mops_set_vc (C + t) (L + m) zt t vs ++
                   mops_inc_vc (C + t) v t ++ [ARW t (m, 0) (S t) 0])
        (P1 ++ (t, rest) :: P2) (upd_env G t tmp1 (v + 1))
  | iexec_spawn P1 P2 u li rest vs1 vs2 v
      (Hspawn : P = P1 ++ (t, spawn_handler t u zt ++
                              Spawn u li :: rest) :: P2)
      (Hnew : ~In u (map fst P))  (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) :
      iexec P G t (events_max_vc (C + t) (C + u) t zt ++
                   events_inc_vc (C + t) t ++ [fork t u])
                  (mops_max_vc (C + t) (C + u) vs1 vs2 t zt ++
                   mops_inc_vc (C + t) v t)
        (P1 ++ (t, rest) :: (u, li) :: P2) (upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0))) t tmp1 (v + 1)) 
  | iexec_wait P1 P2 u rest vs1 vs2 v
      (Hwait : P = P1 ++ (t, Wait u :: wait_handler t u zt ++ rest) 
                   :: P2) (Hdone : In (u, []) P)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) :
      iexec P G t (join t u :: events_max_vc (C + u) (C + t) t zt ++ events_inc_vc (C+u) t)
                 (mops_max_vc (C + u) (C + t) vs1 vs2 t zt ++ mops_inc_vc' (C+u) v t u)
        (P1 ++ (t, rest) :: P2) (upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0))) t tmp1 (v + 1)) 
  | iexec_assert P1 P2 e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hpass : eval (G t) e1 <= eval (G t) e2) :
      iexec P G t [] [] (P1 ++ (t, rest) :: P2) G.

Require Import RelationClasses.

Instance env_sim_refl : Reflexive env_sim.
Proof. repeat intro; auto. Qed.

Corollary eval_old' : forall G t v1 v2 e
  (Hfresh1 : expr_fresh tmp1 e) (Hfresh2 : expr_fresh tmp2 e),
  eval (upd_env (upd_env G t tmp1 v1) t tmp2 v2 t) e = eval (G t) e.
Proof.
  intros; apply eval_old; auto.
  apply env_sim_refl.
Qed.

Lemma last_f : forall A B (f : A -> A -> B) d d' l1 l2
  (Hl1 : l1 <> []) (Hl2 : l2 <> []) (Hlen : length l1 = length l2),
  last (map (fun x => f (fst x) (snd x)) (combine l1 l2)) d =
  f (last l1 d') (last l2 d').
Proof.
  induction l1; clarify.
  destruct l2; clarify.
  destruct (nil_dec l1).
  - destruct l2; clarify.
  - destruct (nil_dec l2); [destruct l1; clarify|].
    rewrite last_cons, last_cons, last_cons; auto.
    destruct (combine l1 l2) eqn: Hcom; clarify.
    destruct l1, l2; clarify.
Qed.

Lemma iexec_exec_t : forall P G t lo lc P' G'
  (Hiexec : iexec P G t lo lc P' G'),
  exec_star_t t (Some P) G lo lc (Some P') G'.
Proof.
  intros; inversion Hiexec; clarify.
  - eapply exec_step_t'.
    + apply exec_assign; eauto.
    + apply exec_refl_t.
    + auto.
    + auto.
  - eapply exec_step_inv_t'.
    eapply exec_step_inv_t'; auto.
    + apply load_handler_norace_spec_t; try (apply Hle); eauto.
      unfold load_handler.
      simpl; do 2 rewrite <- (app_assoc (hb_check _ _ _ _ _)); eauto.
    + apply exec_load; eauto.
    + apply exec_unlock; eauto.
    + simpl; repeat rewrite <- app_assoc; auto.
    + simpl; repeat rewrite <- app_assoc; auto.
  - eapply exec_step_inv_t'.
    eapply exec_step_inv_t'; auto.
    + apply store_handler_norace_spec_t.
      * unfold store_handler.
        simpl; eauto.
      * apply Hlen1.
      * apply Hlen2.
      * apply Hlen3.
      * auto.
      * auto.
    + apply exec_store; eauto.
    + apply exec_unlock; eauto.
    + simpl; repeat rewrite <- app_assoc; auto.
    + simpl; repeat rewrite <- app_assoc; auto.
      rewrite eval_old'; auto.
  - eapply exec_step_t'.
    + eapply exec_lock; eauto.
    + apply lock_handler_spec_t; eauto.
      apply zt_non_zero.
    + auto.
    + auto.
  - eapply exec_step_inv_t'.
    + apply unlock_handler_spec_t; eauto.
    + apply exec_unlock; eauto.
    + rewrite <- app_assoc; auto.
    + rewrite <- app_assoc; auto.
  - eapply exec_step_inv_t'.
    + apply spawn_handler_spec_t.
      * eauto.
      * apply Hlen1.
      * apply Hlen2.
      * auto.
    + generalize zt_non_zero; intro.
      erewrite last_f.
      * apply exec_spawn; auto.
        intro; contradiction Hnew.
        rewrite map_app, in_app in *; clarify.
      * intro; clarify.
      * intro; clarify.
      * rewrite Hlen1; auto.
    + rewrite <- app_assoc; auto.
    + rewrite <- app_assoc; auto.
  - eapply exec_step_t'.
    + apply exec_wait; eauto.
    + apply wait_handler_spec_t; eauto.
      apply zt_non_zero.
    + auto.
    + auto.
  - eapply exec_step_t'.
    + eapply exec_assert_pass; eauto.
    + apply exec_refl_t.
    + auto.
    + auto.
Qed.

Corollary iexec_exec : forall P G t lo lc P' G'
  (Hiexec : iexec P G t lo lc P' G'), exec_star (Some P) G lo lc (Some P') G'.
Proof.
  intros; eapply exec_t_exec, iexec_exec_t; eauto.
Qed.

Inductive iexec_star : state -> env ->
  list operation -> list conc_op -> state -> env -> Prop :=
| iexec_refl P G : iexec_star P G [] [] P G
| iexec_step P G t o c P' G' (Hexec : iexec P G t o c P' G') lo lc P'' G''
    (Hexec' : iexec_star P' G' lo lc P'' G'') :
    iexec_star P G (o ++ lo) (c ++ lc) P'' G''.

Transparent move.
Lemma set_vc_len : forall src tgt z tmp,
  length (set_vc src tgt z tmp) = 2 * z.
Proof.
  induction z; clarify.
  rewrite IHz; omega.
Qed.
Opaque move.

Lemma unlock_handler_len : forall t u z tmp,
  length (unlock_handler t u z tmp) = 2 * z + 3.
Proof.
  unfold unlock_handler; clarify.
  rewrite app_length, set_vc_len; simpl; omega.
Qed.

Lemma iexec_inv : forall i P P1 t rest P2 G lo lc P' G'
  (HP : P = P1 ++ (t, instrument_instr i t ++ rest) :: P2)
  (Hdistinct : distinct P) (Hiexec : iexec P G t lo lc P' G'),
  match i with
  | Assign a e => lo = [] /\ lc = [] /\ P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env G t a (eval (G t) e)
  | Load a (x, o) => exists vs1 vs2 v vt, length vs1 = zt /\ length vs2 = zt /\
      first_gt vs1 vs2 = None /\
      lo = acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
           events_move (C + t) (R + x) t ++ [rd t x; rel t (X + x)] /\
      lc = Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
           mops_move (C + t, t) (R + x, t) t vt ++
           [Read t (x, o) v; Rel t (X + x)] /\
      P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env (upd_env (upd_env G t tmp1 vt) t tmp2 (last vs2 (G t tmp2))) 
                   t a v
  | Store (x, o) e => exists vs1 vs2 vs3 v, length vs1 = zt /\
      length vs2 = zt /\ length vs3 = zt /\ first_gt vs1 vs2 = None /\
      first_gt vs3 vs2 = None /\ expr_fresh tmp1 e /\ expr_fresh tmp2 e /\
      lo = acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
           events_hb_check (R + x) (C + t) vs3 vs2 t ++
           events_move (C + t) (W + x) t ++ [wr t x; rel t (X + x)] /\
      lc = Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
           mops_hb_check (R + x) (C + t) vs3 vs2 zt t ++
           mops_move (C + t, t) (W + x, t) t v ++
           [Write t (x, o) (eval (G t) e); Rel t (X + x)] /\
      P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))
  | Lock m => exists vs1 vs2, length vs1 = zt /\ length vs2 = zt /\ t < zt /\
      lo = acq t m :: events_max_vc (L + m) (C + t) t zt /\
      lc = ARW t (m, 0) 0 (S t) :: mops_max_vc (L + m) (C + t) vs1 vs2 t zt /\
      P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env (upd_env G t tmp1 (last vs1 0)) t tmp2
                   (Peano.max (last vs1 0) (last vs2 0))
  | Unlock m => exists vs v,  length vs = zt  /\
      lo = events_set_vc (C + t) (L + m) zt t ++
           events_inc_vc (C + t) t ++ [rel t m] /\
      lc = mops_set_vc (C + t) (L + m) zt t vs ++
           mops_inc_vc (C + t) v t ++ [ARW t (m, 0) (S t) 0] /\
      P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env G t tmp1 (v + 1)
  | Spawn u li => exists vs1 vs2 v, ~In u (map fst P) /\length vs1 = zt /\ length vs2 = zt/\
      lo = events_max_vc (C + t) (C + u) t zt ++
           events_inc_vc (C + t) t ++ [fork t u] /\
      lc = mops_max_vc (C + t) (C + u) vs1 vs2 t zt ++
           mops_inc_vc (C + t) v t/\
      P' = P1 ++ (t, rest) :: (u, instrument li u)
           :: P2 /\ G' = upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
                   t tmp1 (v + 1)
  | Wait u => exists vs1 vs2 v, In (u, []) P /\ length vs1 = zt /\
      length vs2 = zt /\
      lo = join t u :: events_max_vc (C + u) (C + t) t zt ++ events_inc_vc (C+u) t/\
      lc = mops_max_vc (C + u) (C + t) vs1 vs2 t zt ++ mops_inc_vc' (C+u) v t u/\
      P' = P1 ++ (t, rest) :: P2 /\
      G' =upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
                   t tmp1 (v + 1)
  | Assert_le e1 e2 => eval (G t) e1 <= eval (G t) e2 /\ lo = [] /\ lc = [] /\
      P' = P1 ++ (t, rest) :: P2 /\ G' = G
  end.
Proof.
  intros.
  generalize zt_non_zero.
  inversion Hiexec; clarify; exploit distinct_thread; eauto; clarify.
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
  - destruct i; clarify; try (destruct x0); destruct zt; clarify.
    rewrite Nat.add_cancel_l in *; subst.
    repeat rewrite <- app_assoc in *; simpl in *.
    exploit app_eq_inv; eauto; clarify.
    exploit app_eq_inv; eauto; clarify.
    repeat eexists; eauto.
    { repeat rewrite <- app_assoc in *; simpl in *.
      exploit app_eq_inv; eauto; clarify. }
  - destruct i; clarify; try (destruct x0); destruct zt; clarify.
    { repeat rewrite <- app_assoc in *; simpl in *.
      exploit app_eq_inv; eauto; clarify. }
    rewrite Nat.add_cancel_l in *; subst.
    repeat rewrite <- app_assoc in *; simpl in *.
    exploit app_eq_inv; eauto; clarify.
    exploit app_eq_inv; eauto; clarify.
    repeat eexists; eauto.
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
    exploit app_eq_inv; eauto; clarify.
    repeat eexists; eauto.
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
    repeat rewrite <- app_assoc in *; simpl in *.
    exploit app_eq_inv.
    { do 2 rewrite unlock_handler_len; eauto. }
    { eauto. }
    clarify.
    repeat eexists; eauto.
    
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
    rewrite Nat.add_cancel_l in *; subst.
    repeat rewrite <- app_assoc in *; simpl in *.
    exploit app_eq_inv; eauto; clarify.
    repeat eexists; eauto.
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
    exploit app_eq_inv; eauto; clarify.
    repeat eexists; eauto.
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
Qed.

Lemma state_sim_step : forall P1 P2 G1 G2 t o lo c lc P1' P2' G1' G2'
  (Hdistinct : distinct P2)
  (Hexec : exec P1 G1 t o c (Some P1') G1')
  (HPsim : state_sim P1 P2)
  (Hiexec : iexec P2 G2 t lo lc P2' G2'),
  state_sim P1' P2'.
Proof.
  intros.
  inversion Hexec; clarify; exploit Forall2_app_inv_l; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - exploit (iexec_inv (Assign a e)); simpl; eauto; clarify.
    apply Forall2_app; auto.
  - destruct x as (x, o).
    exploit (iexec_inv (Load a (x, o))); eauto.
    { apply Hdistinct. }
    { eauto. }
    unfold state_sim; clarify.
    apply Forall2_app; auto.
  - destruct x as (x, o).
    exploit (iexec_inv (Store (x, o) e)); eauto.
    { apply Hdistinct. }
    { eauto. }
    unfold state_sim; clarify.
    apply Forall2_app; auto.
  - exploit (iexec_inv (Lock m)); simpl; eauto; unfold state_sim; clarify.
    apply Forall2_app; auto.
  - exploit (iexec_inv (Unlock m)); simpl; eauto; unfold state_sim; clarify.
    apply Forall2_app; auto.
  - exploit (iexec_inv (Spawn u li)); simpl; eauto; unfold state_sim; clarify.
    apply Forall2_app; auto.
  - exploit (iexec_inv (Wait u)); simpl; eauto; unfold state_sim; clarify.
    apply Forall2_app; auto.
  - exploit (iexec_inv (Assert_le e1 e2)); simpl; eauto; unfold state_sim;
      clarify.
    apply Forall2_app; auto.
Qed.

Lemma sim_step : forall P1 P2 G1 G2 t o lo c lc P1' P2' G1' G2'
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1) (Hdistinct : distinct P2)
  (Ht : Forall (fun e => fst e < zt) P1)
  (Hexec : exec P1 G1 t o c (Some P1') G1')
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  (Hiexec : iexec P2 G2 t lo lc P2' G2') (Hmem : mem_sim c lc),
  state_sim P1' P2' /\ env_sim G1' G2'.
Proof.
  intros.
  exploit state_sim_step; eauto; intro HPsim'; clarify.
  inversion Hexec; clarify; exploit Forall2_app_inv_l; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - exploit (iexec_inv (Assign a e)); simpl; eauto; clarify.
    unfold env_sim in *; unfold upd_env, upd; clarify.
    setoid_rewrite Forall_app in Hfresh; clarify.
    inversion Hfresh2 as [|? ? Hi]; clarify; inversion Hi. clarify.
    apply eval_sim; intros; apply HGsim; intro; clarify.
  - destruct x as (x, o).
    exploit (iexec_inv (Load a (x, o))); eauto.
    { apply Hdistinct. }
    { eauto. }
    intros (vs1 & vs2 & v0 & vt & Hlen1 & Hlen2 & ?).
    clarify; clear Hlen1.
    unfold env_sim in *; clarify. (*env_sim*)
    destruct (eq_dec v1 a); [subst | repeat rewrite upd_old; auto].
    destruct (eq_dec t t0); [subst | repeat rewrite upd_old_t; auto].
    repeat rewrite upd_same; auto.
    specialize (Hmem (Read t0 (x, o) v)); destruct Hmem as (Hmem & _);
      clarify.
    rewrite in_app in *; clarify.
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|? ? Hx ?]; inversion Hx; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    destruct Hmem1 as [? | [Hmem1 | [? | [Hmem1 | ?]]]]; clarify.
    + exploit mops_hb_check_meta; eauto; clarify.
    + inversion Hmem1; clarify.
      contradiction Hmem2; unfold meta_loc; simpl; omega.
    + inversion Hmem1; auto.
  - destruct x as (x, o).
    exploit (iexec_inv (Store (x, o) e)); eauto.
    { apply Hdistinct. }
    { eauto. }
    intros (vs1 & vs2 & vs3 & v & Hlen1 & Hlen2 & Hlen3 & ?).
    unfold env_sim in *; clarify. (*env_sim*)
    repeat rewrite upd_old; eauto.
  - exploit (iexec_inv (Lock m)); simpl; eauto.
    unfold state_sim; clarify.
    unfold env_sim in *; clarify.
    repeat rewrite upd_old; eauto.
  - exploit (iexec_inv (Unlock m)); simpl; eauto; clarify.
    unfold env_sim in *; unfold upd_env, upd; clarify.
    
  - exploit (iexec_inv (Spawn u li)); simpl; eauto; clarify.
    unfold env_sim in *; unfold upd_env, upd; clarify.
    destruct (eq_dec tmp1 v); clarify.
  - exploit (iexec_inv (Wait u)); simpl; eauto; clarify.
    unfold env_sim in *; unfold upd_env, upd; clarify.
    destruct (eq_dec tmp2 v); clarify.
  - exploit (iexec_inv (Assert_le e1 e2)); simpl; eauto; clarify.
Qed.

End Sim_Defs.

End Instrumentation.
Hint Resolve max_vc_prog set_vc_prog hb_check_prog.