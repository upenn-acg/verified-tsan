Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import FunctionalExtensionality.
Set Implicit Arguments.

Definition move src tgt tmp := [Load tmp src; Store tgt (V tmp)].

Lemma upd_same : forall G t a v,
  (upd_env G t a v) t a = v.
Proof.
  unfold upd_env, upd; clarify.
Qed.

Lemma upd_overwrite : forall G t a v1 v2,
  upd_env (upd_env G t a v1) t a v2 = upd_env G t a v2.
Proof.
  intros; extensionality t'; extensionality v'.
  unfold upd_env, upd; clarify.
Qed.

Definition events_move (src tgt:var) (t:tid): list operation :=
  [rd t src; wr t tgt].

Definition mops_move (src tgt: ptr) (t:tid) (v:nat): list conc_op := [Read t src v; Write t tgt v].

Lemma move_spec : forall src tgt i j tmp P P1 P2 G t rest v
  (Hmove : P = P1 ++ (t, move (src, i) (tgt, j) tmp ++ rest) :: P2),
  exec_star (Some P) G
            (events_move src tgt t) (mops_move (src, i) (tgt, j) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env G t tmp v).
Proof.
    
  intros. 
  eapply exec_step'.
  - apply exec_load.
    unfold move in Hmove.  eauto.
  - simpl.
    eapply exec_step'.
    + apply exec_store.
      eauto.
    + apply exec_refl.
    + auto.
    + auto.
  - auto.
  - simpl.
    rewrite upd_same.
    auto.
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

Lemma set_vc_spec_0 : forall src tgt tmp P G P1 P2 t rest 
(Hset_vc0: P=P1++(t, set_vc src tgt 0 tmp ++ rest)::P2),
exec_star (Some P) G [] [] (Some (P1++(t,rest)::P2)) G.
Proof.
  intros.
  unfold set_vc in Hset_vc0.
  rewrite Hset_vc0.
  simpl.
  eapply exec_refl.
Qed.

Lemma events_set_vc_step: forall src tgt n t,
  events_set_vc src tgt (S n) t = (events_move src tgt t)++events_set_vc src tgt n t.
Proof.
  intros.
  eauto.
Qed.

Lemma mops_set_vc_step: forall src tgt n t v vss,
  mops_set_vc src tgt (S n) t (v::vss)= (mops_move (src,n) (tgt,n) t v)++mops_set_vc src tgt n t vss.
Proof.
  intros.
  eauto.
Qed.

Lemma set_vc_step: forall  src tgt n tmp,
  set_vc src tgt (S n) tmp =(move (src,n) (tgt,n) tmp)++set_vc src tgt n tmp.
Proof.
  intros.
  eauto.
Qed.

Lemma nonempty_list: forall (ls : list nat) n, 
  length ls = S n -> exists x xs, ls=x::xs /\ length xs=n.
Proof.
  destruct ls; clarify; eauto.
Qed.

Lemma set_vc_spec_step : forall src tgt n tmp P G P1 P2 t rest v 
(Hset_vc: P=P1++(t, set_vc src tgt (S n) tmp++ rest)::P2),
 exec_star (Some P) G
          (events_move src tgt t) (mops_move (src,n) (tgt,n) t v) (Some (P1++(t, set_vc src tgt n tmp++rest)::P2)) (upd_env G t tmp v).
Proof.
  intros.
  rewrite Hset_vc.
  rewrite set_vc_step.
  apply move_spec.
  auto.
Qed.

Lemma exec_star_trans : forall P G P' S G' G'' e1 m1 e2 m2,
  exec_star (Some P) G e1 m1 (Some P') G' -> exec_star (Some P') G' e2 m2 S G''-> exec_star (Some P) G (e1++e2) (m1++m2) S G''.
Proof.
  intros ?????????? Hexec; induction Hexec; clarify.
  eapply exec_step'; eauto; clarsimp.
Qed.

Lemma list_cons_plus_assoc: forall (T:Type) (x:T) (x0 y: list T),
 (x::x0)++y=x::(x0++y).
Proof.
  intros.
  auto.
Qed.

Lemma set_vc_spec_n : forall n src tgt tmp P G P1 P2 t rest v vss 
(Hset_vc: P=P1++(t, set_vc src tgt (S n) tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star (Some P) G
          (events_set_vc src tgt (S n) t) (mops_set_vc src tgt (S n) t (vss++[v])) (Some (P1++(t,rest)::P2)) (upd_env G t tmp v).
Proof.
  
  intros n.
  induction n.

  -intros.
   apply empty_list in Hvs.
   clarify.
   apply move_spec.
   eauto.  
  -intros.
   rewrite Hset_vc.
   (*
   eapply set_vc_spec_step in Hset_vc.
   rewrite set_vc_step in Hset_vc.*)
   apply nonempty_list in Hvs.
   inversion Hvs.
   inversion H.
   inversion H0.
   rewrite H1.
   rewrite list_cons_plus_assoc.
   rewrite events_set_vc_step,mops_set_vc_step, set_vc_step.
   eapply exec_star_trans.
   +rewrite <- set_vc_step.
    apply set_vc_spec_step.
    eauto.
   +assert( Hupd: upd_env G t tmp v = upd_env (upd_env G t tmp x) t tmp v).  
    rewrite upd_overwrite. auto.
    rewrite Hupd.
    apply IHn.
    *auto.
    *auto.
Qed.

Lemma upd_triv : forall G t a, upd_env G t a (G t a) = G.
Proof.
  intros; extensionality t'; extensionality a'; unfold upd_env, upd; clarify.
Qed.
 
Corollary set_vc_spec : forall n src tgt tmp P G P1 P2 t rest vss 
(Hset_vc: P=P1++(t, set_vc src tgt n tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star (Some P) G (events_set_vc src tgt n t) (mops_set_vc src tgt n t vss)
  (Some (P1++(t,rest)::P2)) (upd_env G t tmp (last vss (G t tmp))).
Proof.
  destruct n; intros.
  - destruct vss; clarify.
    rewrite upd_triv; apply exec_refl.
  - intros.
    assert (vss <> []) as Hnnil by (destruct vss; clarify).
    rewrite (app_removelast_last (G t tmp) Hnnil) in *.
    rewrite last_snoc; apply set_vc_spec_n; auto.
    rewrite app_length in *; clarify; omega.
Qed.
 
Definition inc_vc t tgt tmp := [
  Load tmp (tgt, t);
  Assign tmp (Plus (V tmp) (I 1));
  Store (tgt, t) (V tmp)
].

Definition events_inc_vc (tgt:var) (t:tid): list operation:=
  [rd t tgt; wr t tgt]. 
Definition mops_inc_vc (tgt:var) (v:nat) (t:tid): list conc_op:=
  [Read t (tgt,t) v; Write t (tgt,t) (v+1) ].

Lemma inc_vc_spec : forall  tgt tmp P G P1 P2 t rest v 
  (Hinc_vc: P=P1++((t,inc_vc t tgt tmp++rest)::P2)),
  exec_star (Some P) G 
            (events_inc_vc tgt t) (mops_inc_vc tgt v t) 
            (Some (P1++(t,rest)::P2)) (upd_env G t tmp (v+1)). 
Proof.
  intros.
  eapply exec_step'.
  -apply exec_load.
   unfold inc_vc in Hinc_vc; eauto.
  -simpl.
   eapply exec_step'.
   +apply exec_assign; eauto.
   +simpl.
    
    eapply exec_step'.
    *apply exec_store; eauto.
    *rewrite upd_same.
     rewrite upd_overwrite.
     apply exec_refl.
    *auto.
    *auto.
   +auto.
   +auto.
  -auto.
  -simpl.
   unfold mops_inc_vc.
   repeat rewrite upd_same.
   auto.
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
  (*;Write t tgt (nat.max v1 v2)*)
].
Lemma upd_diff : forall G t a1 a2 v1 v2
 (Ha: a1<>a2),
 (upd_env (upd_env G t a1 v1) t a2 v2) t a1 = v1. 
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

Lemma upd_assoc: forall G t a1 a2 v1 v2
 (Ha: a1<>a2),
 upd_env (upd_env G t a1 v1) t a2 v2 = upd_env (upd_env G t a2 v2) t a1 v1.
Proof.
  intros; extensionality t'; extensionality v'.
  unfold upd_env, upd; clarify.
Qed.

Lemma max_spec : forall P P1 P2 rest G src tgt i j tmp1 tmp2 v1 v2 t
 (Hmax_spec: P= P1++((t, max (src, i) (tgt, j) tmp1 tmp2++rest)::P2)) (Hdist: tmp1<> tmp2),
exec_star (Some P) G (events_max src tgt t) (mops_max (src, i) (tgt, j) v1 v2 t) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
Proof.
  intros.
  rewrite Hmax_spec.
  eapply exec_step'.
  -apply exec_load.
   unfold max. clarify.
  -eapply exec_step'.
   +apply exec_load. clarify.
   +eapply exec_step'.
    *apply exec_assign. clarify.
    *clarify.
     
     eapply exec_step'.
      apply exec_store. eauto.
      rewrite upd_overwrite. 
      repeat rewrite upd_same.
      rewrite upd_diff. apply exec_refl.
      eauto.
      eauto.
      eauto.
    *eauto.
    *eauto.
   +eauto.
   +eauto.
  -eauto.
  -eauto.
   unfold mops_max. clarify. repeat rewrite upd_same. rewrite upd_diff; eauto.
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
Lemma max_vc_spec_0 : forall src tgt tmp1 tmp2 P G P1 P2 t rest
(Hmax_vc0 : P=P1++(t, max_vc src tgt 0 tmp1 tmp2 ++ rest)::P2),
 exec_star (Some P) G 
           [] [] (Some (P1++(t,rest)::P2)) G.
Proof.
  intros.
  unfold max_vc in Hmax_vc0.
  rewrite Hmax_vc0.
  eapply exec_refl.
Qed.


Lemma events_max_vc_step: forall src tgt t n,
  events_max_vc src tgt t (S n) = events_max src tgt t ++ events_max_vc src tgt t n.
Proof.
  intros.
  eauto.
Qed.

Lemma mops_max_vc_step: forall src tgt n v1 v2 vss1 vss2 t,
  mops_max_vc src tgt (v1::vss1) (v2::vss2) t (S n) =
  mops_max (src,n) (tgt,n) v1 v2 t ++ mops_max_vc src tgt vss1 vss2 t n.
Proof.
  intros.
  eauto.
Qed.

Lemma max_vc_step: forall  src tgt n tmp1 tmp2,
  max_vc src tgt (S n) tmp1 tmp2 = max (src,n) (tgt,n) tmp1 tmp2++ max_vc src tgt  n tmp1 tmp2.
Proof.
  intros.
  eauto.
Qed.

Lemma max_vc_spec_step : forall n src tgt tmp1 tmp2 P G P1 P2 t rest v1 v2

(Hmax_vc: P=P1++(t, max_vc src tgt (S n) tmp1 tmp2 ++ rest)::P2) (Htmp: tmp1 <> tmp2),
 exec_star (Some P) G
          (events_max src tgt t) (mops_max (src,n) (tgt,n) v1 v2 t) (Some (P1++(t, max_vc src tgt n tmp1 tmp2 ++ rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).
Proof.
  intros.
  rewrite Hmax_vc.
  rewrite max_vc_step.
  apply max_spec; eauto.
Qed.
  
Lemma max_vc_spec_n : forall n src tgt tmp1 tmp2 P G P1 P2 t rest v1 v2 vss1 vss2

(Hmax_vc: P=P1++(t, max_vc src tgt (S n) tmp1 tmp2 ++ rest)::P2) (Htmp: tmp1 <> tmp2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
 exec_star (Some P) G
          (events_max_vc src tgt t (S n)) (mops_max_vc src tgt (vss1++[v1]) (vss2++[v2]) t (S n)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).
Proof.
  intro n.
  induction n.
  -intros.
   apply empty_list in Hvs1.
   apply empty_list in Hvs2.
   rewrite Hvs1, Hvs2. simpl.
   apply max_spec; eauto.

  -intros.
   rewrite Hmax_vc.
   apply nonempty_list in Hvs1.
   apply nonempty_list in Hvs2.
   inversion Hvs1.
   inversion Hvs2.
   inversion H.
   inversion H0.
   inversion H1.
   inversion H2.
   rewrite H3, H5.
   repeat rewrite list_cons_plus_assoc.
   rewrite events_max_vc_step, mops_max_vc_step, max_vc_step.
   eapply exec_star_trans.
   +apply max_vc_spec_step; eauto.
    rewrite <- max_vc_step. eauto.
   +assert(Hupd: (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)) = upd_env (upd_env (upd_env (upd_env G t tmp1 x) t tmp2 (Peano.max x x0)) t tmp1 v1) t tmp2 (Peano.max v1 v2)).
    symmetry.
    rewrite upd_assoc.
    rewrite upd_overwrite.
    rewrite upd_assoc.
    rewrite upd_overwrite. eauto.
    auto. apply Htmp.
   rewrite Hupd. 
   apply IHn; eauto.
Qed.

Corollary max_vc_spec : forall n src tgt tmp1 tmp2 P G P1 P2 t rest vss1
  vss2 (Hmax_vc: P=P1++(t, max_vc src tgt n tmp1 tmp2 ++ rest)::P2)
  (Htmp: tmp1 <> tmp2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
  exists v1 v2, exec_star (Some P) G (events_max_vc src tgt t n)
    (mops_max_vc src tgt vss1 vss2 t n) (Some (P1++(t,rest)::P2))
    (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  destruct n; intros.
  - destruct vss1, vss2; clarify.
    do 2 eexists; repeat rewrite upd_triv; apply exec_refl.
  - assert (vss1 <> []) as Hnnil1 by (destruct vss1; clarify).
    assert (vss2 <> []) as Hnnil2 by (destruct vss2; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite app_length in Hvs1, Hvs2.
    do 2 eexists; apply max_vc_spec_n; clarify; omega.
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

Lemma assert_le_fail_spec: forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: ~ v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t)
            None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros.
  rewrite Hassert_le_spec.
  eapply exec_step'.
  -apply exec_load.
   unfold assert_le.
   clarify.
  -eapply exec_step'.
   +apply exec_load.
    clarify.
    +eapply exec_step'.
     eapply exec_assert_fail. eauto.
     unfold eval. rewrite upd_same. rewrite upd_assoc. rewrite upd_same. 
     apply Hv1v2. apply Htmp. 
     apply exec_refl.
     eauto.
     eauto.
    +eauto.
    +eauto.
   -eauto.
   -eauto.
Qed.

Lemma assert_le_pass_spec: forall P P1 P2 rest G a b i j tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le (a, i) (b, j) tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le (a, i) (b, j) v1 v2 t)
            (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros.
  rewrite Hassert_le_spec.
  eapply exec_step';eauto.
  -apply exec_load.
   unfold assert_le.
   clarify.
  -eapply exec_step';eauto.
   +apply exec_load.
    clarify.
   +eapply exec_step';eauto.
    *eapply exec_assert_pass; eauto.
     unfold eval. rewrite upd_same. rewrite upd_assoc; eauto. rewrite upd_same.
     apply Hv1v2.
    *apply exec_refl.
  -eauto.
  -eauto.
Qed.
    
Fixpoint hb_check C1 C2 z tmp1 tmp2 :=
match z with
| 0 => []
| S n =>(assert_le (C1,n) (C2,n) tmp1 tmp2)++ hb_check C1 C2 n tmp1 tmp2
end.

Lemma hb_check_step: forall C1 C2 n tmp1 tmp2,
 hb_check C1 C2 (S n) tmp1 tmp2 = (assert_le (C1,n) (C2,n) tmp1 tmp2)++ hb_check C1 C2 n tmp1 tmp2.
Proof.
  intros.
  eauto.
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
  intros. auto.
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
  intros. auto.
Qed.

Lemma hb_check_spec0: forall C1 C2 t tmp1 tmp2 P G P1 P2 rest
 (Hhb_check0: P=P1++(t,hb_check C1 C2 0 tmp1 tmp2++rest)::P2),
  exec_star (Some P) G 
            [] [] (Some (P1++(t,rest)::P2)) G.
Proof.
  intros.
  unfold hb_check in Hhb_check0; eauto.
  rewrite Hhb_check0.
  apply exec_refl.
Qed.

Lemma hb_check_spec_step_fail: forall C1 C2 t tmp1 tmp2 P G P1 P2 rest n v1 v2
  (Hhb_heck_step: P=P1++(t,hb_check C1 C2 (S n) tmp1 tmp2++rest)::P2) (Htmp: tmp1<> tmp2) (Hv1v2: ~ v1 <= v2),
   exec_star (Some P) G (events_assert_le C1 C2 t)
             (mops_assert_le (C1,n) (C2,n) v1 v2 t) 
              None
             (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros.
  rewrite Hhb_heck_step.
  rewrite hb_check_step.
  eapply assert_le_fail_spec; eauto;clarify.
Qed.
 
Lemma hb_check_spec_step_pass: forall C1 C2 t tmp1 tmp2 P G P1 P2 rest n v1 v2
  (Hhb_heck_step: P=P1++(t,hb_check C1 C2 (S n) tmp1 tmp2++rest)::P2) (Htmp: tmp1<> tmp2) (Hv1v2: v1 <= v2),
   exec_star (Some P) G (events_assert_le C1 C2 t)
             (mops_assert_le (C1,n) (C2,n) v1 v2 t) 
             (Some (P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2))
             (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros.
  rewrite Hhb_heck_step.
  rewrite hb_check_step.
  eapply assert_le_pass_spec; eauto; clarify.
Qed.
    
Fixpoint first_gt l1 l2 :=
match (l1,l2) with
| (x1::xs1, x2::xs2) => if leb x1 x2 then first_gt xs1 xs2 else Some (x1,x2) 
| _   => None
end.

Lemma first_gt_step: forall x1 x2 xs1 xs2,
first_gt (x1::xs1) (x2::xs2) = if leb x1 x2 then first_gt xs1 xs2 else Some (x1,x2).
Proof.
  intros. eauto.
Qed.

Lemma hb_check_fail_spec_n: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
           (mops_hb_check C1 C2 vs1 vs2 (S n) t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2). 
Proof.
  intro n.
  induction n;intros;
  apply nonempty_list in Hvs1;apply nonempty_list in Hvs2;
  inversion Hvs1; inversion Hvs2; inversion H; inversion H0;
  inversion H1; inversion H2.
  -apply empty_list in H4. apply empty_list in H6. clarify.
   eapply assert_le_fail_spec;eauto.
   +clarify.
   +rewrite <- leb_le; intro; clarify.
  - rewrite H3, H5, first_gt_step in Hfirst_gt. 
    destruct (leb x x0) eqn:Hxx0; eauto.
    +rewrite H3,H5. 
     rewrite events_hb_check_step, mops_hb_check_step.
     rewrite Hhb_check_spec, Hxx0,  hb_check_step.
     eapply exec_star_trans.
     *apply assert_le_pass_spec; clarify.
      rewrite leb_le in *; auto.
     *clarify.
      assert(Hupd: (upd_env (upd_env G t tmp1 v1) t tmp2 v2)= upd_env (upd_env (upd_env (upd_env G t tmp1 x) t tmp2 x0) t tmp1 v1) t tmp2 v2).
       symmetry. rewrite upd_assoc. rewrite upd_overwrite.
       rewrite upd_assoc. rewrite upd_overwrite. eauto.
       clarify. eauto.
      rewrite Hupd.
      eapply IHn; eauto.
     +rewrite H3,H5.
      rewrite events_hb_check_step, mops_hb_check_step.
     rewrite Hhb_check_spec, Hxx0,  hb_check_step.
     inversion Hfirst_gt.
     rewrite <- H8, <- H9.
     eapply assert_le_fail_spec; clarify.
     rewrite <- leb_le; intro; clarify.
Qed.

Corollary hb_check_fail_spec: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2
  vs1 vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
   (mops_hb_check C1 C2 vs1 vs2 n t)
   None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  destruct n; intros.
  - destruct vs1, vs2; clarify.
  - eapply hb_check_fail_spec_n; eauto.
Qed.
     
Lemma hb_check_pass_spec_n: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt (vs1++[v1]) (vs2++[v2]) = None),
 exec_star (Some P) G (events_hb_check C1 C2 (vs1++[v1]) (vs2++[v2]) t)
           (mops_hb_check C1 C2 (vs1++[v1]) (vs2++[v2]) (S n) t) 
           (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 v2). 
Proof.
  intro n.
  induction n;intros.
  -apply empty_list in Hvs1. apply empty_list in Hvs2. clarify.
   apply assert_le_pass_spec; eauto.
   rewrite leb_le in cond; auto.
  -apply nonempty_list in Hvs1;apply nonempty_list in Hvs2;
  inversion Hvs1; inversion Hvs2; inversion H; inversion H0;
  inversion H1; inversion H2.

  rewrite H3, H5, list_cons_plus_assoc in Hfirst_gt. 
  rewrite list_cons_plus_assoc, first_gt_step in Hfirst_gt.
  
    destruct (leb x x0) eqn:Hxx0; eauto.
    +rewrite H3,H5.
     repeat rewrite list_cons_plus_assoc.
     rewrite events_hb_check_step, mops_hb_check_step.
     rewrite Hhb_check_spec, Hxx0,  hb_check_step.
     eapply exec_star_trans.
     *apply assert_le_pass_spec; clarify.
      rewrite leb_le in *; auto.
     *clarify.
      assert(Hupd: (upd_env (upd_env G t tmp1 v1) t tmp2 v2)= upd_env (upd_env (upd_env (upd_env G t tmp1 x) t tmp2 x0) t tmp1 v1) t tmp2 v2).
       symmetry. rewrite upd_assoc. rewrite upd_overwrite.
       rewrite upd_assoc. rewrite upd_overwrite. eauto.
       clarify. eauto.
      rewrite Hupd.
      eapply IHn; eauto.
     +rewrite H3,H5.
      repeat rewrite list_cons_plus_assoc.

      rewrite events_hb_check_step, mops_hb_check_step.
     rewrite Hhb_check_spec, Hxx0,  hb_check_step.
     inversion Hfirst_gt.
Qed.

Lemma hb_check_pass_spec: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest vs1
  vs2 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt vs1 vs2 = None),
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 t)
           (mops_hb_check C1 C2 vs1 vs2 n t) (Some (P1++(t,rest)::P2))
   (upd_env (upd_env G t tmp1 (last vs1 (G t tmp1))) t tmp2 (last vs2 (G t tmp2))).
Proof.
  destruct n; intros.
  - destruct vs1, vs2; clarify.
    repeat rewrite upd_triv; apply exec_refl.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite app_length in Hvs1, Hvs2; repeat rewrite last_snoc.
    apply hb_check_pass_spec_n; auto; clarify; omega.
Qed.    
   
(* Since everything is a nat, we can use C + t as the t component of C. *)
(* We should put locks on each location, and maybe each lock. *)

Definition load_handler t x C (*Cl*) R (*Rl*) (W : var) (*Wl*) z tmp1 tmp2 := 
  (*[Lock (Cl + x); Lock (Wl + x); Lock (Rl + x)] ++*)
  hb_check (W + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (R + x, t) tmp1 (*++
  [Unlock (Cl + x); Unlock (Wl + x); Unlock (Rl + x)]*).

Lemma load_handler_norace_spec_n: forall n x C R W t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hload_handler_spec: P= P1++(t,load_handler t x C R W (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt (vs1++[v1]) (vs2++[v2]) = None) v,
 exec_star (Some P) G 
           (events_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) t ++ events_move (C+t) (R+x) t)
           (mops_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) (S n) t ++ mops_move (C+t,t) (R+x, t) t v)
           (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v) t tmp2 v2).
Proof.
  intros.
  apply exec_star_trans with (P':=P1++(t,move (C+t,t) (R+x,t) tmp1 ++rest)::P2) (G':= upd_env (upd_env G t tmp1 v1) t tmp2 v2).
  -apply hb_check_pass_spec_n;eauto.
   unfold load_handler in Hload_handler_spec.
   rewrite app_assoc.  eauto.
  - assert(Hupd:(upd_env (upd_env G t tmp1 v) t tmp2 v2)= upd_env (upd_env (upd_env G t tmp1 v1) t tmp2 v2) t tmp1 v).
    symmetry. rewrite upd_assoc.
    rewrite upd_overwrite. eauto. 
    eauto.
   rewrite Hupd.
   apply move_spec. eauto.
Qed.

(* updates to different locals don't interfere with each other*)
Lemma upd_old : forall G t1 a1 v1 t2 a2 (Ha : a1 <> a2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

Corollary load_handler_norace_spec: forall n x C R W t tmp1 tmp2 P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1 ++ (t, load_handler t x C R W n tmp1 tmp2
  ++ rest) :: P2) (Htmp : tmp1 <> tmp2) (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hfirst_gt : first_gt vs1 vs2 = None) v,
  exec_star (Some P) G
    (events_hb_check (W + x) (C + t) vs1 vs2 t ++ events_move (C + t) (R + x) t)
    (mops_hb_check (W + x) (C + t) vs1 vs2 n t ++ mops_move (C + t, t) (R + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  intros; destruct n; clarify.
  - destruct vs1, vs2; clarify.
    assert (upd_env G t tmp1 v t tmp2 = G t tmp2) as Heq
      by (apply upd_old; auto).
    rewrite <- Heq, upd_triv; apply move_spec; auto.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite app_length in Hvs1, Hvs2; clarify.
    rewrite last_snoc; apply load_handler_norace_spec_n; auto; omega.
Qed.

Lemma load_handler_race_spec_n: forall n x C R W t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hload_handler_spec: P= P1++(t,load_handler t x C R W (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (events_hb_check (W + x) (C + t) vs1 vs2 t)
           (mops_hb_check (W + x) (C + t) vs1 vs2 (S n) t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros.
  unfold load_handler in Hload_handler_spec.
  apply hb_check_fail_spec_n with (P1:=P1) (P2:=P2) (rest:=(move (C+t, t) (R+x,t) tmp1)++rest); eauto.
  rewrite app_assoc. eauto.
Qed.

Corollary load_handler_race_spec: forall n x C R W t tmp1 tmp2 P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1++(t,load_handler t x C R W n tmp1 tmp2++
  rest)::P2) (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
  v1 v2 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (events_hb_check (W + x) (C + t) vs1 vs2 t)
           (mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  destruct n; intros.
  - destruct vs1, vs2; clarify.
  - eapply load_handler_race_spec_n; eauto.
Qed.

Definition store_handler t x C (R:var) W z tmp1 tmp2 := 
  hb_check (W + x) (C + t) z tmp1 tmp2 ++
  hb_check (R + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (W + x, t) tmp1.
Lemma store_handler_race_waw_spec_n: forall n x C R W t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hstore_handler_spec: P= P1++(t,store_handler t x C R W (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (events_hb_check (W + x) (C + t) vs1 vs2 t)
           (mops_hb_check (W + x) (C + t) vs1 vs2 (S n) t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2). 
Proof.
  intros.
  unfold store_handler in Hstore_handler_spec.
  apply hb_check_fail_spec_n with (P1:=P1) (P2:=P2) (rest:=hb_check (R + x) (C + t) (S n) tmp1 tmp2 ++ move (C+t, t) (W+x,t) tmp1++rest); eauto.
  repeat rewrite <- app_assoc in Hstore_handler_spec.  eauto.
Qed.

Lemma store_handler_race_war_spec_n: forall n x C R W t tmp1 tmp2 P G P1 P2 rest ve1 ve2 ve3 v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x C R W (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 = n) 
 (Hfirst_gt12: first_gt (vs1++[ve1]) (vs2++[ve2]) = None)
 (Hfirst_gt32: first_gt (vs3++[ve3]) (vs2++[ve2]) = Some (v3,v2)),

 exec_star (Some P) G 
           (events_hb_check (W + x) (C + t) (vs1++[ve1]) (vs2++[ve2]) t ++
            events_hb_check (R + x) (C + t) (vs3++[ve3]) (vs2++[ve2]) t)
           (mops_hb_check (W + x) (C + t) (vs1++[ve1]) (vs2++[ve2]) (S n) t ++
            mops_hb_check (R + x) (C + t) (vs3++[ve3]) (vs2++[ve2]) (S n) t) 
           None (upd_env (upd_env G t tmp1 v3) t tmp2 v2). 
Proof.
  intros.
  apply exec_star_trans with (P':=P1++(t,hb_check (R + x) (C + t) (S n) tmp1 tmp2 ++ move (C+t,t) (W+x, t) tmp1 ++ rest)::P2) (G':=upd_env (upd_env G t tmp1 ve1) t tmp2 ve2).
  -apply hb_check_pass_spec_n; eauto.
   unfold store_handler in Hstore_handler_spec.
   repeat rewrite <- app_assoc in Hstore_handler_spec. eauto.
  -assert(Hupd: upd_env (upd_env G t tmp1 v3) t tmp2 v2 =
                upd_env (upd_env (upd_env (upd_env G t tmp1 ve1) t tmp2 ve2) t tmp1 v3) t tmp2 v2).
    symmetry. rewrite upd_assoc. rewrite upd_overwrite. rewrite upd_assoc. rewrite upd_overwrite. eauto.
    eauto.
    eauto.
   rewrite Hupd.
   eapply hb_check_fail_spec_n; eauto;
   clarify; rewrite app_length; rewrite plus_comm; eauto.
Qed.

Lemma store_handler_norace_spec_n: forall n x C R W t tmp1 tmp2 P G P1 P2 rest v1 v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x C R W (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 =n) 
 (Hfirst_gt12: first_gt (vs1++[v1]) (vs2++[v2]) = None)
 (Hfirst_gt32: first_gt (vs3++[v3]) (vs2++[v2]) = None) v,
 exec_star (Some P) G 
           (events_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) t ++ 
            events_hb_check (R + x) (C + t) (vs3++[v3]) (vs2++[v2]) t ++               
            events_move (C+t) (W+x) t)
           (mops_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) (S n) t ++ 
            mops_hb_check (R + x) (C + t) (vs3++[v3]) (vs2++[v2]) (S n) t ++
            mops_move (C+t,t) (W+x, t) t v) 
           (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v) t tmp2 v2).
Proof.
  intros.
  apply exec_star_trans with (P':=P1++(t,hb_check (R + x) (C + t) (S n) tmp1 tmp2++move (C+t, t) (W+x, t) tmp1  ++rest)::P2) (G':= upd_env (upd_env G t tmp1 v1) t tmp2 v2).  
  -apply hb_check_pass_spec_n; eauto.
   unfold store_handler in Hstore_handler_spec.
   repeat rewrite <- app_assoc in Hstore_handler_spec. eauto.
  -apply exec_star_trans with (P':=P1++(t,move (C+t, t) (W+x, t) tmp1  ++rest)::P2) (G':= upd_env (upd_env G t tmp1 v3) t tmp2 v2).
   assert(Hupd: upd_env (upd_env G t tmp1 v3) t tmp2 v2 = 
                upd_env (upd_env (upd_env (upd_env G t tmp1 v1) t tmp2 v2) t tmp1 v3) t tmp2 v2).
    symmetry. rewrite upd_assoc.
    rewrite upd_overwrite. rewrite upd_assoc. rewrite upd_overwrite. auto.
   eauto. eauto.
   rewrite Hupd.
   apply hb_check_pass_spec_n; eauto.

   assert(Hupd: upd_env (upd_env G t tmp1 v) t tmp2 v2=
                upd_env (upd_env (upd_env G t tmp1 v3) t tmp2 v2) t tmp1 v
         ).
    symmetry. rewrite upd_assoc. rewrite upd_overwrite. eauto. eauto.

   rewrite Hupd. 
   apply move_spec. eauto.
Check move_spec.
Qed.

Corollary store_handler_norace_spec: forall n x C R W t tmp1 tmp2 P G P1 P2 rest
  vs1 vs2 vs3 (Hstore_handler_spec: P = P1 ++ (t, store_handler t x C R W n tmp1 tmp2
  ++ rest) :: P2) (Htmp : tmp1 <> tmp2) (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hvs3: length vs3 = n) (Hfirst_gt12 : first_gt vs1 vs2 = None) (Hfirst_gt32: first_gt vs3 vs2 = None) v,
  exec_star (Some P) G
    (events_hb_check (W + x) (C + t) vs1 vs2 t ++ 
     events_hb_check (R + x) (C + t) vs3 vs2 t ++
     events_move (C + t) (W + x) t)
    (mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
     mops_hb_check (R + x) (C + t) vs3 vs2 n t ++
     mops_move (C + t, t) (W + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  intros; destruct n; clarify.
  - destruct vs1, vs2, vs3; clarify.
    assert (upd_env G t tmp1 v t tmp2 = G t tmp2) as Heq
      by (apply upd_old; auto).
    rewrite <- Heq, upd_triv; apply move_spec; auto.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    assert (vs3 <> []) as Hnnil3 by (destruct vs3; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite (app_removelast_last 0 Hnnil3) in *.
    rewrite app_length in Hvs1, Hvs2, Hvs3; clarify.
    rewrite last_snoc; apply store_handler_norace_spec_n; auto; omega.
Qed.
   
Definition lock_handler t l C L z tmp1 tmp2 :=
  max_vc (L+l) (C+t) z tmp1 tmp2.

Lemma lock_handler_spec_n : forall n t l C L tmp1 tmp2 P G P1 P2 rest v1 v2 vss1 vss2

(Hmax_vc: P=P1++(t, lock_handler t l C L (S n) tmp1 tmp2 ++ rest)::P2) (Htmp: tmp1 <> tmp2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
 exec_star (Some P) G
          (events_max_vc (L+l) (C+t) t (S n)) (mops_max_vc (L+l) (C+t) (vss1++[v1]) (vss2++[v2]) t (S n)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
Proof.
  intros.
  apply max_vc_spec_n; eauto.
Qed.

Lemma lock_handler_spec : forall n t l C L tmp1 tmp2 P G P1 P2 rest vs1 vs2 v

(Hmax_vc: P=P1++(t, lock_handler t l C L n tmp1 tmp2 ++ rest)::P2) (Htmp: tmp1 <> tmp2) (Hvs1: length vs1=n) (Hvs2: length vs2=n) (Ht: t<n),
 exec_star (Some P) G
          (events_max_vc (L+l) (C+t) t n) (mops_max_vc (L+l) (C+t) (vs1) (vs2) t  n) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 (last vs1 0)) t tmp2 (Peano.max (last vs1 v) (last vs2 v))).  
Proof.
  
  intros; destruct n.
  - inversion Ht.
  -assert(vs1 <>[]) as Hnnil1 by (destruct vs1; clarify).
   assert(vs2 <>[]) as Hnnil2 by (destruct vs2; clarify).
  
   rewrite (app_removelast_last v Hnnil1) in *.
   rewrite (app_removelast_last v Hnnil2) in *.
   rewrite app_length in Hvs1, Hvs2.
   repeat rewrite last_snoc.
   apply lock_handler_spec_n with (vss1:=removelast vs1) (vss2:=removelast vs2) (v1:=last vs1 v) (v2:= last vs2 v).
   eauto.
   eauto.
   clarify. omega.
   clarify. omega.
Qed.

Definition unlock_handler t l (C : var (* start of thread VCs *))
  (L : var (* start of lock VCs *)) z tmp1 tmp2 :=
  max_vc (C + t) (L+l) z tmp1 tmp2 ++ inc_vc t (C + t) tmp1.

Lemma unlock_handler_spec_n : forall n C l L tmp1 tmp2 P G P1 P2 t rest v1 vss1 v2 vss2 vt
(Hset_vc: P=P1++(t, unlock_handler t l C L (S n) tmp1 tmp2++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n) (Htmp: tmp1<>tmp2),
 exec_star (Some P) G
          (events_max_vc (C+t)(L+l) t (S n)++(events_inc_vc (C+t) t)) (mops_max_vc (C+t) (L+l )(vss1++[v1]) (vss2++[v2]) t (S n) ++ (mops_inc_vc (C+t) vt t)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp2 (Peano.max v1 v2)) t tmp1 (vt+1)).
Proof.
  intros.
  apply exec_star_trans with (P':=P1++(t,inc_vc t (C+t) tmp1++rest)::P2) (G':=upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).
  -apply max_vc_spec_n. rewrite app_assoc. eauto. auto. auto. auto.
  -assert(Hoverwrite: upd_env (upd_env G t tmp2 (Peano.max v1 v2)) t tmp1 (vt+1) = upd_env (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)) t tmp1 (vt+1)).
    symmetry. rewrite upd_assoc. rewrite upd_overwrite. rewrite upd_assoc. eauto.
    eauto. eauto.
   rewrite Hoverwrite.
   apply inc_vc_spec. 
   eauto.
Qed.




Definition spawn_handler t u C z tmp :=
  set_vc (C + t) (C + u) z tmp ++ inc_vc t (C + t) tmp.

(* mod? *)
Lemma spawn_handler_spec_n : forall n C u tmp P G P1 P2 t rest v vss vt
(Hset_vc: P=P1++(t, spawn_handler t u C (S n) tmp++ rest)::P2) (Hvs: length vss=n),
 exec_star (Some P) G
          (events_set_vc (C+t)(C+u) (S n) t++(events_inc_vc (C+t) t)) (mops_set_vc (C+t) (C+u) (S n) t (vss++[v])++ (mops_inc_vc (C+t) vt t)) (Some (P1++(t,rest)::P2)) (upd_env G t tmp (vt+1)).
Proof.
  intros.
  unfold spawn_handler in Hset_vc.
  apply exec_star_trans with (P':=P1++(t,inc_vc t (C+t) tmp++rest)::P2) (G':=upd_env G t tmp v). 
  -eapply set_vc_spec_n;eauto.
   rewrite app_assoc. eauto.
  -assert(Hoverwrite:upd_env G t tmp (vt+1) =upd_env (upd_env G t tmp v) t tmp (vt+1)).
   rewrite <- upd_overwrite with (v1:=v). eauto.
   rewrite Hoverwrite.
   apply inc_vc_spec. eauto.
Qed.
   
    

Definition wait_handler t u C z tmp1 tmp2 :=
  max_vc (C + u) (C + t) z tmp1 tmp2.
(* The instrumentation pass is provided locations to store each of the
   race detection state components. *)
Lemma wait_handler_spec_n : forall n t u C tmp1 tmp2 P G P1 P2 rest v1 v2 vss1 vss2

(Hmax_vc: P=P1++(t, wait_handler t u C (S n) tmp1 tmp2 ++ rest)::P2) (Htmp: tmp1 <> tmp2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
 exec_star (Some P) G
          (events_max_vc (C+u) (C+t) t (S n)) (mops_max_vc (C+u) (C+t) (vss1++[v1]) (vss2++[v2]) t (S n)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
Proof.
  intros.
  apply max_vc_spec_n; eauto.
Qed.

(* Note that for now, we assign metadata to a block, rather than to
   offsets within that block. *)
Fixpoint instrument_instr (C L R W : var) z tmp1 tmp2 (ins : instr) (t : tid)
  : prog :=
let instrument := fix f p t :=
  match p with
  | [] => []
  | ins::inss => (instrument_instr C L R W z tmp1 tmp2 ins t)++(f inss t)
  end in
(match ins with
 | Load a (x, _)   => load_handler t x C R W z tmp1 tmp2 ++ [ins]
 | Store (x, _) e  => store_handler t x C R W z tmp1 tmp2 ++ [ins]
 | Lock l          => [ins] ++ lock_handler t l C L z tmp1 tmp2
 | Unlock l   => unlock_handler t l C L z tmp1 tmp2 ++ [ins]
 | Spawn u li =>  spawn_handler t u C z tmp1 ++ [Spawn u (instrument li u)] 
 | Wait u     => [ins] ++ wait_handler t u C z tmp1 tmp2  (* the wait_handler should be called after the wait returns*)
 | _          => [ins]
end).

Fixpoint instrument C L R W z tmp1 tmp2 (p: prog) (t: tid) : prog:=
match p with
| [] => []
| ins::inss => (instrument_instr C L R W z tmp1 tmp2 ins t)++(instrument C L R W z tmp1 tmp2 inss t)
end.


Section SC.

Context (ML : Memory_Layout nat var_eq).

Definition consistent (m : list conc_op) := @SC _ _ _ ML _ _ Base m.

Definition can_read (m : list conc_op) t p v := consistent (m ++ [Read t p v]).
Definition can_write (m : list conc_op) t p :=
  forall v, consistent (m ++ [Write t p v]).

Variables (C L R W : var) (zt zl zv : nat) (tmp1 tmp2 : local)
  (Htmp : tmp1 <> tmp2).

Definition vstate := @VectorClocks.state tid var lock.

Definition clock_match m V x := forall t,
  if lt_dec t zt then can_read m t (x, t) (V t) /\ can_write m t (x, t)
  else V t = 0.

Definition clocks_sim (m : list conc_op) (s : vstate) :=
  (forall t, t < zt -> clock_match m (clock_of s t) (C + t)) /\
  (forall l, l < zl -> clock_match m (lock_of s l) (L + l)) /\
  (forall v, v < zv -> clock_match m (read_of s v) (R + v) /\
     clock_match m (write_of s v) (W + v)).

Lemma op_indep : forall c1 c2 (Hindep : loc_of c1 <> loc_of c2),
   Forall (fun l => Forall (independent l) (map block_model.loc_of (to_seq c2)))
     (map block_model.loc_of (to_seq c1)).
Proof.
  destruct c1, c2; clarify.
Qed.

Lemma loc_comm_SC : forall m1 c1 c2 m2 (Hindep : loc_of c1 <> loc_of c2)
  (Hcon : consistent (m1 ++ c1 :: c2 :: m2)), consistent (m1 ++ c2 :: c1 :: m2).
Proof.
  unfold consistent, SC; clarify.
  rewrite lower_app, lower_cons, lower_cons;
    rewrite lower_app, lower_cons, lower_cons in Hcon.
  repeat rewrite to_ilist_app in *; rewrite loc_comm_ops; auto.
  apply op_indep; auto.
Qed.
  
Lemma loc_comm_ops1_SC : forall c lc m1 m2
  (Hindep : Forall (fun c' => loc_of c' <> loc_of c) lc),
  consistent (m1 ++ c :: lc ++ m2) <-> consistent (m1 ++ lc ++ c :: m2).
Proof.
  induction lc; clarify; [reflexivity|].
  inversion Hindep; clarify.
  specialize (IHlc (m1 ++ [a]) m2); clarsimp.
  etransitivity; eauto; split; apply loc_comm_SC; auto.
Qed.

Lemma loc_comm_ops_SC : forall lc1 lc2 m1 m2
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lc2) lc1),
  consistent (m1 ++ lc1 ++ lc2 ++ m2) <-> consistent (m1 ++ lc2 ++ lc1 ++ m2).
Proof.
  induction lc1; clarify; [reflexivity|].
  specialize (IHlc1 lc2 (m1 ++ [a]) m2); inversion Hindep; clarsimp.
  etransitivity; eauto; apply loc_comm_ops1_SC; auto.
Qed.

Lemma consistent_app_SC : forall m1 m2 (Hcon : consistent (m1 ++ m2)),
  consistent m1.
Proof.
  unfold consistent, SC; intros.
  rewrite lower_app in Hcon; eapply consistent_app; eauto.
Qed.

Lemma loc_valid_SC : forall m c1 c2 (Hindep : loc_of c1 <> loc_of c2),
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

Lemma read_noop_SC : forall m t x v m2 (Hcon : consistent (m ++ [Read t x v])),
  consistent (m ++ Read t x v :: m2) <-> consistent (m ++ m2).
Proof.
  unfold consistent, SC; clarify.
  repeat rewrite lower_app; rewrite lower_app in Hcon.
  rewrite lower_single in Hcon; rewrite lower_cons; clarify.
  rewrite split_app; do 2 rewrite to_ilist_app; apply read_noop; auto.
Qed.

Lemma can_write_SC : forall p ops m t (Hcan : can_write m t p)
  (Hcon : consistent (m ++ ops)), can_write (m ++ ops) t p.
Proof.
  induction ops; clarsimp.
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
  snd t2 = instrument C L R W zt tmp1 tmp2 (snd t1) (fst t1)) P1 P2.
Check state_sim.
(*all locals except tmp1 or tmp2 in G1 & G2 have the same values *)
Definition env_sim (G1 G2 : env) := forall t v, v <> tmp1 -> v <> tmp2 ->
  G1 t v = G2 t v.
(*tmp1 & tmp2 are not used in P*)
Definition fresh_tmps (P : state) :=
  Forall (fun e => Forall (fun i => fresh tmp1 i /\ fresh tmp2 i) (snd e)) P.
(* checks whether x points to some meta location *)
Definition meta_loc (x : ptr) := C <= fst x < C + zt \/
  L <= fst x < L + zl \/ R <= fst x < R + zv \/ W <= fst x < W + zv.

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

(* an instruction is safe iff it only access the part of memory that does not hold meta locations*)
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
  | Spawn _ li => list_safe li
  | _ => True
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
  clear - H2.
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

(* updates to different stacks(per-thread) don't interfere with each other*)
Lemma upd_old_t : forall G t1 a1 v1 t2 a2 (Ht : t1 <> t2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

(* all the memory operations only access meta locations*)
Lemma mops_hb_check_meta : forall l1 l2 n x t c (Hx : x < zv) (Ht : t < zt)
  (Hin : In c (mops_hb_check (W + x) (C + t) l1 l2 n t)\/ In c (mops_hb_check (R+x) (C+t) l1 l2 n t)) , meta_loc (loc_of c).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  destruct Hin as [? | [? | ?]].
  destruct H; clarify.
  - unfold meta_loc; clarify; omega.
  - destruct H; clarify.
    +unfold meta_loc; clarify; omega.
    +eapply IHl1; eauto.
  
- clarify.
  unfold meta_loc; clarify; omega.
- destruct H; clarify.
  + unfold meta_loc; clarify; omega.
  + 
    eapply IHl1; eauto.
Qed.
Print mops_max_vc.
(* all the memory operations only access meta locations*)
Lemma mops_max_vc_meta: forall l1 l2 n m0 t c (Hx : m0 < zl) (Ht : t < zt)
  (Hin : In c (mops_max_vc (L + m0) (C + t) l1 l2 t n)\/ In c (mops_max_vc (C+t) (L + m0) l1 l2 t n)) , meta_loc (loc_of c).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  destruct Hin;
  destruct n; clarify; destruct l2; clarify;
  repeat (destruct H; clarify;  [unfold meta_loc; clarify; omega |]);
  eauto.
Qed.

Definition lower' := @lower _ _ _ _ _ Base.

(* hb_check only generate reads to the memory*)
Lemma mops_hb_check_read : forall C1 C2 l1 l2 n t,
  Forall (fun x => match x with MRead _ _ => True | _ => False end)
    (lower' (mops_hb_check C1 C2 l1 l2 n t)).
Proof.
  induction l1; unfold lower', lower; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  do 2 constructor; eauto.
Qed.
(* mops generated by hb_check are consistent?*)
Lemma mops_hb_check_con : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  @block_model.consistent _ _ _ ML (lower' m ++ lower'
    (mops_hb_check (W + x) (C + t) (map (write_of s x) (rev (interval 0 n)))
      (map (clock_of s t) (rev (interval 0 n))) n t)).
Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  setoid_rewrite lower_cons.
  rewrite app_assoc, to_ilist_app, reads_noops.
  rewrite lower_cons, to_ilist_app, iapp_app, reads_noops.
  - destruct (write_of s x n <=? clock_of s t n).
    + rewrite to_ilist_app in IHn; apply IHn; auto; omega.
    + simpl; rewrite iapp_nil_ilist; auto.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs1 _ Ht n); clarify.
    unfold can_read, consistent, SC in Hs11; rewrite lower_app in Hs11. auto.
  - clarify.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs222 n); clarify.
    unfold can_read, consistent, SC in Hs2221; rewrite lower_app in Hs2221;
      auto.
  - clarify.
Qed.



(* mops generated by max_vc are consistent?*)
Lemma mops_max_vc_con_lc : forall m s (Hs : clocks_sim m s) m0 t0 n
  (Hn : n <= zt) (Hl : m0 < zl) (Ht : t0 < zt) (Hcon : consistent m),
  @block_model.consistent _ _ _ ML (lower' m ++ lower'
        (mops_max_vc (L + m0) (C + t0) (map (lock_of s m0) (rev (interval 0 n)))
           (map (clock_of s t0) (rev (interval 0 n))) t0 n)).

Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  setoid_rewrite lower_cons.
  rewrite app_assoc, to_ilist_app, reads_noops.
  rewrite lower_cons, to_ilist_app, iapp_app, reads_noops.  
  -rewrite lower_cons. rewrite <- to_ilist_app. apply loc_valid_ops; eauto.
   +rewrite Forall_forall. intros. rewrite in_map_iff in H. inversion H. clarify.
    rewrite Forall_forall. intros. (* need to prove x is not (Block _)*)
    admit.
   +unfold clocks_sim in Hs; clarify.
   
    specialize(Hs1 _ Ht n); clarify.
    unfold can_write, consistent, SC in Hs12. 
    specialize(Hs12  (Peano.max (lock_of s m0 n) (clock_of s t0 n))); clarify.
    rewrite lower_app in Hs12. eauto.
   +apply IHn; eauto. omega.
 
  -unfold clocks_sim in Hs; clarify.
   specialize (Hs1 _ Ht n); clarify.
   unfold can_read, consistent, SC in Hs11; rewrite lower_app in Hs11. eauto.
  -clarify.
  -unfold clocks_sim in Hs; clarify.
   specialize (Hs21 _ Hl n); clarify.
   unfold can_read, consistent, SC in Hs211. rewrite lower_app in Hs211. eauto.
  -clarify.
Qed.

(* mops generated by max_vc are consistent?*)
Lemma mops_max_vc_con_cl : forall m s (Hs : clocks_sim m s) m0 t0 n
  (Hn : n <= zt) (Hl : m0 < zl) (Ht : t0 < zt) (Hcon : consistent m),
  @block_model.consistent _ _ _ ML (lower' m ++ lower'
        (mops_max_vc (C + t0) (L + m0) (map (clock_of s t0) (rev (interval 0 n))) (map (lock_of s m0) (rev (interval 0 n)))
            t0 n)).

Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  setoid_rewrite lower_cons.
  rewrite app_assoc, to_ilist_app, reads_noops.
  rewrite lower_cons, to_ilist_app, iapp_app, reads_noops.  
  -rewrite lower_cons. rewrite <- to_ilist_app. apply loc_valid_ops; eauto.
   +rewrite Forall_forall. intros. rewrite in_map_iff in H. inversion H. clarify.
    rewrite Forall_forall. intros. (* need to prove x is not (Block _)*)
    admit.
   +unfold clocks_sim in Hs; clarify.
   
    specialize(Hs21 _ Hl n); clarify.
    unfold can_write, consistent, SC in Hs212. 
    specialize(Hs212  (Peano.max (clock_of s t0 n)  (lock_of s m0 n))); clarify.
    rewrite lower_app in Hs212. eauto.
   +apply IHn; eauto. omega.
 
  -unfold clocks_sim in Hs; clarify.
   specialize (Hs21 _ Hl n); clarify.
   unfold can_read, consistent, SC in Hs211; rewrite lower_app in Hs211. eauto.
  -clarify.
  -unfold clocks_sim in Hs; clarify.
   specialize (Hs1 _ Ht n); clarify.
   unfold can_read, consistent, SC in Hs11. rewrite lower_app in Hs11. eauto.
  -clarify.
Qed.

(* mops generated by hb_check are consistent?*)
Lemma mops_hb_check_conR : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  @block_model.consistent _ _ _ ML (lower' m ++ lower'
    (mops_hb_check (R + x) (C + t) (map (read_of s x) (rev (interval 0 n)))
      (map (clock_of s t) (rev (interval 0 n))) n t)).
Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  setoid_rewrite lower_cons.
  rewrite app_assoc, to_ilist_app, reads_noops.
  rewrite lower_cons, to_ilist_app, iapp_app, reads_noops.
  - destruct (read_of s x n <=? clock_of s t n).
    + rewrite to_ilist_app in IHn; apply IHn; auto; omega.
    + simpl; rewrite iapp_nil_ilist; auto.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs1 _ Ht n); clarify.
    unfold can_read, consistent, SC in Hs11; rewrite lower_app in Hs11; auto.
  - clarify.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs221 n); clarify.
    unfold can_read, consistent, SC in Hs2211; rewrite lower_app in Hs2211;
      auto.
  - clarify.
Qed.

(*mops generated by move are consistent?*)
Lemma mops_move_con : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  @block_model.consistent _ _ _ ML (lower' m ++ lower'
    (mops_move (C + t, t) (R + x, t) t (clock_of s t t))).
Proof.
  unfold mops_move; clarify.
  setoid_rewrite lower_cons.
  rewrite app_assoc, to_ilist_app, reads_noops.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs221 t); clarify.
    specialize (Hs2212 (clock_of s t t)).
    unfold consistent, SC in Hs2212; setoid_rewrite lower_app in Hs2212.
    rewrite to_ilist_app in Hs2212; auto.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs1 _ Ht t).
    unfold can_read, consistent, SC in Hs1.
    rewrite lower_app in Hs1; clarify.
  - clarify.
Qed.

(*mops generated by move are consistent?*)
Lemma mops_move_conW : forall m s (Hs : clocks_sim m s) x t n
  (Hn : n <= zt) (Hx : x < zv) (Ht : t < zt) (Hcon : consistent m),
  @block_model.consistent _ _ _ ML (lower' m ++ lower'
    (mops_move (C + t, t) (W + x, t) t (clock_of s t t))).
Proof.
  unfold mops_move; clarify.
  setoid_rewrite lower_cons.
  rewrite app_assoc, to_ilist_app, reads_noops.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs222 t); clarify.
    specialize (Hs2222 (clock_of s t t)).
    unfold consistent, SC in Hs2222; setoid_rewrite lower_app in Hs2222.
    rewrite to_ilist_app in Hs2222; auto.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs1 _ Ht t).
    unfold can_read, consistent, SC in Hs1.
    rewrite lower_app in Hs1; clarify.
  - clarify.
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

Typeclasses eauto := 2.
Lemma instrument_sim_safe : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 t o c (Some P1') G1')
  (Hcon : consistent (m ++ opt_to_list c))
  s (Hs : clocks_sim m s) s' (Hsafe : step_star s (opt_to_list o) s'),
  exists lo lc P2' G2', exec_star (Some P2) G2 lo lc (Some P2') G2' /\
    consistent (m ++ lc) /\ state_sim P1' P2' /\ env_sim G1' G2' /\
    mem_sim c lc.
Proof.
  
  intros.
  inversion Hstep; clarify; exploit Forall2_app_inv_l; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
  - do 5 eexists; [|split; [|split; [|clarify; split]]]. (*assign*)
    + eapply exec_step; [|apply exec_refl].
      apply exec_assign; eauto. (*exec_star*)
    + auto. (* consistent*)
    + apply Forall2_app; auto. (*state_sim*)
    + repeat intro; unfold upd_env, upd; clarify. (* env_sim*)
      setoid_rewrite Forall_app in Hfresh. clarify.
      inversion Hfresh2 as [|? ? Hi]; clarify; inversion Hi. clarify.
      apply eval_sim; intros; apply HGsim; intro; clarify.
    + split; clarify. (*mem_sim*)
  -destruct x as (x, o). (*load*)
    inversion Hsafe; clarify.
    inversion Hstep0; clarify.
    exploit load_handler_norace_spec. (* generating 6 subgoals*)
    { eauto. } (*Progam*)
    { eauto. }  (*tmp*)
    
    { instantiate (2 := map (W0 x) (rev (interval 0 zt))). (*length of W*)
      rewrite map_length, rev_length, interval_length. 
      rewrite <-  minus_n_O. eauto. }
    { instantiate (1 := map (C0 t0) (rev (interval 0 zt))).  (*length of C*)
      rewrite map_length, rev_length, interval_length. omega. }
    { apply vc_le_first_gt. auto. }  (*first_gt*)
    rewrite plus_0_r; intro Hload. (*exec_star*)
    rewrite <- app_assoc; do 5 eexists; [|split; [|split; [|clarify; split]]]. (* + 5 goals*)
    + eapply exec_star_trans; [apply Hload|]. (*exec_star*)
      eapply exec_step; [|apply exec_refl].
      simpl; apply exec_load; eauto.
    + rewrite app_nil_r; simpl. (*consistent*)
      instantiate (1 := v). (*value to be moved*)
      instantiate (1 := C0 t0 t0). (*value to be read: C0[t0][t0]*)
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      unfold consistent, SC in *.
      rewrite lower_app in Hcon; repeat rewrite lower_app;
        rewrite lower_single in Hcon; rewrite lower_single; simpl in *.
      rewrite <- app_assoc, app_assoc. rewrite to_ilist_app. rewrite reads_noops.
      rewrite <- to_ilist_app.
      apply loc_valid_ops1; auto.
      * rewrite Forall_forall; intros ? Hin.
        
        rewrite in_map_iff in Hin; clarify.
        destruct Hin2; clarify; intro; assert (meta_loc (x, o)); clarify;
          unfold meta_loc; simpl; omega.
      * eapply (mops_move_con Hs); eauto.
        eapply consistent_app; eauto.
      * apply (mops_hb_check_con Hs); auto.
        eapply consistent_app; eauto.
      * apply mops_hb_check_read.
    + apply Forall2_app; auto. (*state_sim*)
    + unfold env_sim in *; clarify. (*env_sim*)
      destruct (eq_dec v0 a); [subst | repeat rewrite upd_old; auto].
      destruct (eq_dec t t0); [subst | repeat rewrite upd_old_t; auto].
      repeat rewrite upd_same; auto.
    + setoid_rewrite Forall_app in Hlocs; clarify. (*mem_sim*)
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      contradiction H2.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      rewrite in_app in H1. destruct H1. eapply mops_hb_check_meta. eauto.
      eauto. eauto.
      destruct H; clarify; unfold meta_loc; simpl; omega.
  -destruct x as (x,o). (* store *)
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   exploit store_tmps_fresh.
   { eauto. }
   intro Hfresh_tmps.
   exploit store_handler_norace_spec.
   { eauto. }
   { eauto. }
    { instantiate (2 := map (W0 x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      rewrite <- minus_n_O; eauto. }
    { instantiate (1 := map (C0 t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { instantiate (1 := map (R0 x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      rewrite <- minus_n_O; eauto. }
    { apply vc_le_first_gt. auto. }
    { apply vc_le_first_gt. eauto. }
   rewrite plus_0_r; intro Hstore.
   rewrite <- app_assoc; do 5 eexists; [|split; [|split; [|clarify; split]]].
   +eapply exec_star_trans; [apply Hstore|]. (*exec_star*)
    eapply exec_step; [|apply exec_refl].
      simpl; apply exec_store; eauto.
   +rewrite app_nil_r; simpl.  (*consistent*)
    instantiate (1 := C0 t0 t0).
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      unfold consistent, SC in *.
      rewrite lower_app in Hcon; repeat rewrite lower_app;
        rewrite lower_single in Hcon; rewrite lower_single; simpl in *.
      rewrite <- app_assoc, app_assoc, <- app_assoc, app_assoc, to_ilist_app. rewrite reads_noops.
      rewrite <- to_ilist_app. 
      rewrite <- app_assoc, app_assoc, to_ilist_app, reads_noops.
      rewrite <- to_ilist_app.
      apply loc_valid_ops1; auto.
      * rewrite Forall_forall; intros ? Hin.
        rewrite in_map_iff in Hin; clarify.
 
        destruct Hin2; clarify; intro; assert (meta_loc (x, o)); clarify;
          unfold meta_loc; simpl; omega.
      * eapply (mops_move_conW Hs); eauto.
        eapply consistent_app; eauto.
      *rewrite eval_sim with (G2:=G1' t0).
       eauto. intros.
       eapply upd_tmps; eauto. 
      *apply (mops_hb_check_conR Hs); auto.
       eapply consistent_app; eauto.
      * apply mops_hb_check_read.
      * apply (mops_hb_check_con Hs); auto.
        eapply consistent_app; eauto.
      * eapply mops_hb_check_read.
   +apply Forall2_app; auto. (*state_sim*)
   +unfold env_sim in *; clarify. (*env_sim*)
      repeat rewrite upd_old.
      apply HGsim; eauto.
      eauto. eauto.
   + setoid_rewrite Forall_app in Hlocs; clarify. (*mem_sim*)
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      *right. left. 
       erewrite eval_old; eauto.
      *left.
       destruct H1.
        (*1*) 
             simpl. contradiction H5.
             rewrite in_app in H. 
             destruct H.
              (*a*)
                eapply mops_hb_check_meta; eauto.
              (*b*)
                rewrite in_app in H. 
                destruct H.
                  (*i*)
                   eapply mops_hb_check_meta; eauto. 
                  (*ii*)
                   clarify. unfold meta_loc. inversion H; clarify; omega. 
        (*2*)
             symmetry. clarify.
             erewrite eval_old; eauto.
 -(*lock*)
    inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   exploit lock_handler_spec.

           { eauto. }
           { eauto. }
     
           { instantiate(2:= map (L0 m0) (rev (interval 0 zt))). 
               rewrite map_length, rev_length, interval_length. 
      rewrite <-  minus_n_O. eauto. }
           {instantiate(1:= map (C0 t0) (rev (interval 0 zt))).
            rewrite map_length, rev_length, interval_length.
            omega.  }
           {  instantiate(1:=t0). rewrite <-  plus_n_O. eauto. 
              rewrite Forall_app in Ht. clarify. inversion Ht2; clarify. }
         instantiate (1 := 0); intros Hlock.
         rewrite <- plus_n_O in Hlock.  
   do 5 eexists; [|split; [|split; [|clarify; split]]].

  +(*exec_star*) eapply exec_star_trans with (P':=P0'++(t0,lock_handler t0 m0 C L zt tmp1 tmp2 ++ instrument C L R W zt tmp1 tmp2 rest t0) ::l') .
    *eapply exec_step; [ eapply exec_lock | eapply exec_refl]. eauto.
    * eapply Hlock.
  +(*consistent*)
    rewrite app_nil_r; simpl. (*consistent*)
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      unfold consistent, SC in *.
      Check lower_single.
      rewrite lower_app in Hcon.
        repeat rewrite lower_single in Hcon. rewrite lower_app; simpl in *.
        rewrite lower_cons.
      Check consistent_app.
      Check loc_valid_ops1.
      (*rewrite to_ilist_app. Check reads_noops. rewrite reads_noops.
      rewrite <- to_ilist_app.*)
      apply loc_valid_ops; auto.
      * rewrite Forall_forall; intros ? Hin.
        rewrite Forall_forall. intros ? Hin2.
        rewrite in_map_iff in Hin; clarify;
        rewrite in_map_iff in Hin2; clarify.
        admit.
      * eapply (mops_max_vc_con_lc Hs); eauto.
        eapply consistent_app; eauto.
  +
(*state sim*)apply Forall2_app; auto.
  +(*env_sim*)
    unfold env_sim in *; clarify.
    repeat rewrite upd_old; eauto.
  +(*mem_sim*)
    simpl. 
    setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      contradiction H2.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      eapply mops_max_vc_meta; eauto.
 -(*unlock*)
 inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   intros.
   pose proof can_write_SC as Hcan_write_SC. unfold can_write in Hcan_write_SC.
   
   exploit max_vc_spec.
   {eauto. }
   {eauto. }
   { 
     instantiate(2:=map (C0 t0) (rev (interval 0 zt))).
     instantiate(1:=zt).
     rewrite map_length, rev_length, interval_length.
     omega.
   }
   { instantiate(1:=map (L0 m0) (rev (interval 0 zt))).
     rewrite map_length, rev_length, interval_length.
     omega.
   }
   intros Hmax_vc.
   inversion Hmax_vc; inversion H.
   exploit inc_vc_spec.
   { eauto. }
   intros Hinc_vc.

   unfold unlock_handler in *. 
   do 5 eexists; [|split; [|split; [|clarify; split]]].
   
  +
   Check exec_star_trans.
(*exec_star*) eapply exec_star_trans.
    *
     repeat rewrite <-app_assoc.
     (*instantiate(1:=  (upd_env (upd_env G2 t0 tmp1 x) t0 tmp2 x0)).*)
     eapply H0.
    *eapply exec_star_trans.
     
     {eapply Hinc_vc. }
     {eapply exec_step. eapply exec_unlock. 
      unfold app. simpl.  eauto. 
      eapply exec_refl. }
  +(*consistent*)
    rewrite app_nil_r; simpl. (*consistent*)
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      assert(Htrivial: forall (X:Type) (a b c:X), [a;b;c]=[a]++[b;c]).
        intros. auto.
      instantiate(1:=C0 t0 t0).
      rewrite Htrivial.
      rewrite app_assoc. rewrite app_assoc.
      assert ((C + t0, t0) <> (m0, 0)).
      { assert(HCt0: meta_loc(C+t0,t0)).
          unfold meta_loc. clarify. omega.
        intro; clarify. }
      rewrite loc_valid_SC; auto.
      assert (consistent ((m ++
        mops_max_vc (C + t0) (L + m0) (map (C0 t0) (rev (interval 0 zt)))
        (map (L0 m0) (rev (interval 0 zt))) t0 zt) ++
        [Read t0 (C + t0, t0) (C0 t0 t0)])) as Hcon0.
      { admit. }
      split.
      * apply Hcan_write_SC; auto.
        intros. apply Hcan_write_SC; intros.
        { unfold clocks_sim in Hs; clarify.
          specialize (Hs1 t0); clarify.
          specialize (Hs1 t0); clarify. }
        { eapply consistent_app_SC; eauto. }
      * admit.
+admit.
+admit.
+admit.
 -(*spawn*)
    admit.
 -(*wait*)
    admit.
 -(*assert_le*)
    admit.
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

Lemma instrument_sim_race : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 t o c (Some P1') G1')
  (Hcon : consistent (m ++ opt_to_list c)) s (Hs : clocks_sim m s)
  (Hrace : forall s', ~step_star s (opt_to_list o) s'),
  exists lo lc G2', exec_star (Some P2) G2 lo lc None G2'.
Proof.
  intros.
  inversion Hstep; clarify; exploit Forall2_app_inv_l; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - specialize (Hrace s); contradiction Hrace; apply ss_refl.
  - destruct x as (x, o).
    destruct Hs as (HC & HL & HRW).
    generalize (HRW x); intro HRWx.
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    generalize (clock_match_bounded HRWx2); intro Hbound.
    destruct (bounded_le_dec (clock_of s t0) Hbound) as [? | (t & Hgt)].
    { destruct s as (((?, ?), ?), ?); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl]. }
    exploit load_handler_race_spec.
    { eauto. }
    { eauto. }
    { instantiate (2 := map (write_of s x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      rewrite <- minus_n_O; eauto. }
    { instantiate (1 := map (clock_of s t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { rewrite first_gt_spec.
      destruct Hgt as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
      repeat rewrite map_rev;
        exists (length (map (write_of s x) (interval 0 zt)) - t - 1).
      split.
      { apply nth_error_rev; erewrite map_nth_error; eauto.
        rewrite nth_error_interval; clarify; omega. }
      split.
      { assert (length (map (write_of s x) (interval 0 zt)) =
          length (map (clock_of s t0) (interval 0 zt))) as Heq
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
      apply Hclock; omega. }
    rewrite plus_0_r; intro Hload.
    rewrite <- app_assoc; eauto.
Admitted.

(* There's no escape from fine-grained interleaving. We can either:
   - use a messy simulation relation with cases for intermediate states; or
   - prove that for any interleaving, there's an equivalent reordering of the
     steps in which instrumented sections execute in blocks (true only with
     sufficient synchronization). *)

Definition add_lock li l := Lock l :: li ++ [Unlock l].

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

Lemma lock_stuck : forall P P1 P2 t l rest
  (HP : P = P1 ++ (t, Lock l :: rest) :: P2) (Hdistinct : distinct P)
  m (Hlocked : ~can_read m (l, 0) 0) G lo lc P' G'
  (Hexec : exec P G t lo lc P' G'), ~consistent (m ++ opt_to_list lc).
Proof.
  intros; inversion Hexec; clarify; exploit distinct_thread; eauto; clarify.
  unfold can_read, consistent, SC in *; intro Hcon.
  rewrite lower_app, lower_cons in Hlocked, Hcon; clarify.
  contradiction Hlocked.
  unfold lower in *; clarify.
  rewrite split_app in Hcon; eapply consistent_app; eauto.
Qed.  

Definition mods_loc i x :=
  match i with
  | Store y _ => y = x
  | Lock y => x = (y, 0)
  | Unlock y => x = (y, 0)
  | _ => False
  end.

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

Definition wf_lock (P : state) l := Forall (fun e => Forall (fun i =>
  mods_loc i (l, 0) -> i = Lock l \/ i = Unlock l) (snd e)) P.

(* Bigger-step semantics *)
Inductive iexec P G t :
    list operation -> list conc_op -> state -> env -> Prop :=
  | iexec_assign P1 P2 a e rest
      (Hassign : P = P1 ++ (t, Assign a e :: rest) :: P2) :
      iexec P G t [] []
        (P1 ++ (t, rest) :: P2) (upd_env G t a (eval (G t) e))
  | iexec_load P1 P2 a x v rest vs1 vs2
      (Hload : P = P1 ++ (t, load_handler t x C R W zt tmp1 tmp2 ++
                             Load a (x, 0) :: rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt)
      (Hle : first_gt vs1 vs2 = None)  :
      iexec P G t (events_hb_check (W + x) (C + t) vs1 vs2 t ++
                   events_move (C + t) (R + x) t ++ [rd t x])
                  (mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                   mops_move (C + t, t) (R + x, t) t v ++ [Read t (x, 0) v])
        (P1 ++ (t, rest) :: P2)
        (upd_env (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2)))
           t a v)
  | iexec_store P1 P2 x e rest vs1 vs2 vs3 v
      (Hstore : P = P1 ++ (t, store_handler t x C R W zt tmp1 tmp2 ++
                              Store (x, 0) e :: rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt)
      (Hlen3 : length vs3 = zt) (Hle1 : first_gt vs1 vs2 = None)
      (Hle2 : first_gt vs3 vs2 = None)
      (Hfresh1 : expr_fresh tmp1 e) (Hfresh2 : expr_fresh tmp2 e) :
      iexec P G t (events_hb_check (W + x) (C + t) vs1 vs2 t ++
                   events_hb_check (R + x) (C + t) vs3 vs2 t ++
                   events_move (C + t) (W + x) t ++ [wr t x])
                  (mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                   mops_hb_check (R + x) (C + t) vs3 vs2 zt t ++
                   mops_move (C + t, t) (W + x, t) t v ++
                   [Write t (x, 0) (eval (G t) e)])
        (P1 ++ (t, rest) :: P2)
        (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2)))
  | iexec_lock P1 P2 m rest vs1 vs2
      (Hlock : P = P1 ++ (t, Lock m ::
                             lock_handler t m C L zt tmp1 tmp2 ++ rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) (Hlt : t < zt) :
      iexec P G t (acq t m :: events_max_vc (L + m) (C + t) t zt)
                  (ARW t (m, 0) 0 (S t) ::
                   mops_max_vc (L + m) (C + t) vs1 vs2 t zt)
        (P1 ++ (t, rest) :: P2) (upd_env (upd_env G t tmp1 (last vs1 0)) 
          t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
  | iexec_unlock P1 P2 m rest vs1 vs2 v
      (Hunlock : P = P1 ++ (t, unlock_handler t m C L zt tmp1 tmp2 ++
                               Unlock m :: rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) :
      iexec P G t (events_max_vc (C + t) (L + m) t zt ++
                   events_inc_vc (C + t) t ++ [rel t m])
                  (mops_max_vc (C + t) (L + m) vs1 vs2 t zt ++
                   mops_inc_vc (C + t) v t ++ [ARW t (m, 0) (S t) 0])
        (P1 ++ (t, rest) :: P2) (upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0))) t tmp1 (v + 1))
  | iexec_spawn P1 P2 u li rest vs v
      (Hspawn : P = P1 ++ (t, spawn_handler t u C zt tmp1 ++
                              Spawn u li :: rest) :: P2)
      (Hnew : ~In u (map fst P)) (Hlen : length vs = zt) :
      iexec P G t (events_set_vc (C + t) (C + u) zt t ++
                   events_inc_vc (C + t) t ++ [fork t u])
                  (mops_set_vc (C + t) (C + u) zt t vs ++
                   mops_inc_vc (C + t) v t)
        (P1 ++ (t, rest) :: (u, li) :: P2) (upd_env G t tmp1 (v + 1))
  | iexec_wait P1 P2 u rest vs1 vs2
      (Hwait : P = P1 ++ (t, Wait u :: wait_handler t u C zt tmp1 tmp2 ++ rest) 
                   :: P2) (Hdone : In (u, []) P)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) :
      iexec P G t (join t u :: events_max_vc (C + u) (C + t) t zt)
                 (mops_max_vc (C + u) (C + t) vs1 vs2 t zt)
        (P1 ++ (t, rest) :: P2) (upd_env (upd_env G t tmp1 (last vs1 0))
                                 t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
  | iexec_assert P1 P2 e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hpass : eval (G t) e1 <= eval (G t) e2) :
      iexec P G t [] [] (P1 ++ (t, rest) :: P2) G.

Lemma env_sim_refl : forall G, env_sim G G.
Proof. repeat intro; auto. Qed.

Corollary eval_old' : forall G t v1 v2 e
  (Hfresh1 : expr_fresh tmp1 e) (Hfresh2 : expr_fresh tmp2 e),
  eval (upd_env (upd_env G t tmp1 v1) t tmp2 v2 t) e = eval (G t) e.
Proof.
  intros; apply eval_old; auto.
  apply env_sim_refl.
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

Hypothesis zt_non_zero : zt <> 0.

Lemma iexec_exec : forall P G t lo lc P' G' (Hiexec : iexec P G t lo lc P' G'),
  exec_star (Some P) G lo lc (Some P') G'.
Proof.
  intros; induction Hiexec; clarify.
  - eapply exec_step'.
    + apply exec_assign; eauto.
    + apply exec_refl.
    + auto.
    + auto.
  - eapply exec_step_inv.
    + apply load_handler_norace_spec; try (apply Hle); eauto.
    + apply exec_load; eauto.
    + clarsimp.
    + clarsimp.
  - eapply exec_step_inv.
    + apply store_handler_norace_spec.
      { eauto. }
      { apply Htmp. }
      { apply eq_refl. }
      { apply Hlen2. }
      { apply Hlen3. }
      { auto. }
      { auto. }
    + apply exec_store; eauto.
    + clarsimp.
    + clarsimp.
      rewrite eval_old'; auto.
  - eapply exec_step'.
    + eapply exec_lock; eauto.
    + apply lock_handler_spec; eauto.
    + auto.
    + auto.
  - destruct (length vs1) eqn: Hlen1; [clarify|].
    destruct (nil_dec vs1); [clarify|].
    destruct (nil_dec vs2); [clarify|].
    eapply exec_step_inv.
    + eapply unlock_handler_spec_n.
      { eauto. }
      { rewrite (app_removelast_last 0 n0), app_length, Nat.add_1_r in Hlen1;
          inversion Hlen1; eauto. }
      { rewrite (app_removelast_last 0 n1), app_length, Nat.add_1_r in Hlen2;
          inversion Hlen2; eauto. }
      { auto. }
    + apply exec_unlock; eauto.
    + clarsimp.
    + repeat rewrite <- app_removelast_last; clarsimp.
  - destruct (length vs) eqn: Hlen1; [clarify|].
    destruct (nil_dec vs); [clarify|].
    eapply exec_step_inv.
    + eapply spawn_handler_spec_n with (v := last vs 0).
      { eauto. }
      { rewrite (app_removelast_last 0 n0), app_length, Nat.add_1_r in Hlen1;
          inversion Hlen1; eauto. }
    + apply exec_spawn; eauto.
      intro; contradiction Hnew.
      rewrite in_map_iff in *; clarify.
      exists x; clarify.
      rewrite map_app, in_app in *; clarify.
      destruct x; clarify.
      contradiction Hnew; rewrite in_app; clarify.
    + clarsimp.
    + rewrite <- app_removelast_last; clarsimp.
  - destruct (length vs1) eqn: Hlen1; [clarify|].
    destruct (nil_dec vs1); [clarify|].
    destruct (nil_dec vs2); [clarify|].
    eapply exec_step'.
    + apply exec_wait; auto.
    + apply wait_handler_spec_n; eauto.
      { rewrite (app_removelast_last 0 n0), app_length, Nat.add_1_r in Hlen1;
          inversion Hlen1; eauto. }
      { rewrite (app_removelast_last 0 n1), app_length, Nat.add_1_r in Hlen2;
          inversion Hlen2; eauto. }
    + clarsimp.
    + repeat rewrite <- app_removelast_last; clarsimp.
  - eapply exec_step'.
    + eapply exec_assert_pass; eauto.
    + apply exec_refl.
    + auto.
    + auto.
Qed.

Definition mutual_exclusion : forall P l (Hl : wf_lock P l)
  (Hlocked : can_read

Lemma blocked_thread : forall P t1 l rest t2 (Hdistinct : distinct P)
  (Ht1 : In (t1, Lock l :: rest) P)
  G lo lc P' G' (Hsteps : exec_star (Some P) G lo lc P' G')
  li1 li2 (Ht2 : In (t2, li1 ++ li2) P) (* Rather, *someone* needs to unblock it. *)
  (Hlock : Forall (fun i => ~mods_loc i (l, 0)) li1)
  m (Hlocked : ~can_read m (l, 0) 0)
  (Hfinal : final_state P') (Hcon : consistent (m ++ lc)),
  exists P'' G'' lo1 lc1 lo2 lc2, exec_star (Some P) G lo1 lc1 P'' G'' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2 /\ exec_star P'' G'' lo2 lc2 P' G' /\
    match P'' with Some P'' => In (t1, Lock l :: rest) P'' /\ In (t2, li2) P''
    | None => True end.
Proof.
  intros ?????????????.
  remember (Some P) as S; generalize dependent P; induction Hsteps; clarify.
  { rewrite Forall_forall in Hfinal; specialize (Hfinal _ Ht1); clarify. }
  destruct P'.
  exploit distinct_step; eauto; specialize (IHHsteps s); clarify.
  destruct (eq_dec t t1); subst.
  { generalize (in_split _ _ Ht1); intros (P1 & P2 & HP); subst.
    exploit lock_stuck; eauto; clarify.
    rewrite app_assoc in Hcon; eapply consistent_app_SC; eauto. }
  exploit exec_other_thread; try (apply Ht1); eauto; clarify.
  destruct (eq_dec t t2).
  - subst.
    admit.
  - exploit exec_other_thread; try (apply Ht2); eauto; clarify.
    specialize (IHHsteps li1 li2); clarify.
    
  - exists None, G', (opt_to_list o), (opt_to_list c), lo, lc; clarify.
    eapply exec_step'; eauto.
    { apply exec_refl. }
    { rewrite app_nil_r; auto. }
    { rewrite app_nil_r; auto. }
Qed.
    
Theorem critical_section : forall P G lo lc P' G'
  (Hexec : exec_star P G lo lc P' G') (Hfinal : final_state P')
  m l t1 t2 li1 li2 (HP : P = Some [(t1, add_lock li1 l); (t2, add_lock li2 l)])
  (Hlock1 : Forall (fun i => ~mods_loc i (l, 0)) li1)
  (Hlock2 : Forall (fun i => ~mods_loc i (l, 0)) li2)
  (Hcon : consistent (m ++ lc)),
  exists P1 G1 lo1 lo2 lc1 lc2, final_state P1 /\ lo = lo1 ++ lo2 /\
    lc = lc1 ++ lc2 /\
    (exec_star (Some [(t1, add_lock li1 l)]) G lo1 lc1 P1 G1 /\
     exec_star (Some [(t2, add_lock li2 l)]) G1 lo2 lc2 P' G' \/
     exec_star (Some [(t2, add_lock li2 l)]) G lo1 lc1 P1 G1 /\
     exec_star (Some [(t1, add_lock li1 l)]) G1 lo2 lc2 P' G').
Proof.
  intros.
  inversion Hexec; clear Hexec; clarify.
  { inversion Hfinal; clarify. }
  inversion Hexec0; clear Hexec0; clarify; destruct P1 as [|?[|??]]; clarify;
    try solve [exploit app_eq_nil; eauto; clarify].
  - inversion Hexec'; clear Hexec'; clarify.
    { inversion Hfinal; clarify.
      exploit app_eq_nil; eauto; clarify. }
    destruct t0; clarify.
    inversion Hexec; clear Hexec; clarify; destruct P1 as [|?[|??]]; clarify;
      try solve [exploit app_eq_nil; eauto; clarify].
    
  

Lemma instrument_sim_safe2 : forall P P1 P2 G1 G2 h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o2 c2 P2' G2' (Hstep : exec P2 G2 o2 c2 (Some P2') G2')
  (Hcon : consistent (m ++ opt_to_list c2)) s (Hs : clocks_sim m s),
  exists o c P1' G1', exec P1 G1 o c (Some P1') G1' /\
    state_sim P1' P2' /\ env_sim G1' G2' /\
    mem_sim c (opt_to_list c2) /\
        exists s', step_star s (opt_to_list o) s' /\
                   clocks_sim (m ++ opt_to_list c2) s'.
Proof.
  intros.
  exploit exec_exec_t; eauto; intros (t & Hstept); clear Hstep.
  
  
  inversion Hstep; clarify; exploit Forall2_app_inv_r; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - do 5 eexists.

(* This doesn't follow. We need to get the correctness statement straight. *)
Theorem instrument_correct : forall P h m P' G'
  (HP : exec_star (Some (init_state P)) init_env h m (Some P') G'),
  (exists h2 m2 P2' G2', exec_star
     (Some (init_state (instrument C L R W zt tmp1 tmp2 P 0))) init_env h2 m2
     (Some P2') G2') <-> exists s, step_star s0 h s.
Proof.
Abort.

End SC.