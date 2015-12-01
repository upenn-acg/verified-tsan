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

Class metadata := { C : var; L : var; R : var; W : var; X : var;
  zt : nat; zl : nat; zv : nat; tmp1 : local; tmp2 : local;
  Htmp : tmp1 <> tmp2;
  Hnonoverlap : forall t l x,   t < zt -> l < zl -> x < zv -> 
    C+t <> X+x /\ R+t <> X+x /\ W + t<> X+x /\ L+l <> X+x }.

Section Instrumentation.

Context {meta : metadata}.

Hint Resolve Htmp.

Definition load_handler t x z := 
  Lock (X + x) :: hb_check (W + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (R + x, t) tmp1.

Lemma split_app' : forall A (x : A) l, x :: l = [x] ++ l.
Proof. auto. Qed.

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

Opaque hb_check.
Opaque move.

Lemma load_handler_norace_spec_n: forall n x t P G P1 P2 rest v1 v2 vs1 vs2
 (Hload_handler_spec: P= P1++(t,load_handler t x (S n)++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
 (Hfirst_gt: first_gt (vs1++[v1]) (vs2++[v2]) = None) v,
 exec_star (Some P) G 
           (acq t (X + x) :: events_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) t ++ events_move (C+t) (R+x) t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) (S n) t ++ mops_move (C+t,t) (R+x, t) t v)
           (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v) t tmp2 v2).
Proof.
  clarify.
  eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
  eapply exec_star_trans.
  rewrite <- app_assoc; apply hb_check_pass_spec_n; auto.
  rewrite upd_assoc; auto.
  setoid_rewrite upd_assoc at 2; auto.
  setoid_rewrite <- (upd_overwrite _ _ _ v1) at 3; apply move_spec; auto.
Qed.

(* updates to different locals don't interfere with each other*)
Lemma upd_old : forall G t1 a1 v1 t2 a2 (Ha : a1 <> a2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

Transparent hb_check.

Corollary load_handler_norace_spec: forall n x t P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1 ++ (t, load_handler t x n ++ rest) :: P2)   (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hfirst_gt : first_gt vs1 vs2 = None) v,
  exec_star (Some P) G
    (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++ events_move (C + t) (R + x) t)
    (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t ++ mops_move (C + t, t) (R + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 (last vs2 (G t tmp2))).
Proof.
  intros; destruct n; clarify.
  - destruct vs1, vs2; clarify.
    assert (upd_env G t tmp1 v t tmp2 = G t tmp2) as Heq
      by (apply upd_old; auto).
    rewrite <- Heq, upd_triv.
    eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
    apply move_spec; auto.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite app_length in Hvs1, Hvs2; clarify.
    rewrite last_snoc; apply load_handler_norace_spec_n; auto; omega.
Qed.

Opaque hb_check.

Lemma load_handler_race_spec_n: forall n x t P G P1 P2 rest v1 v2 vs1 vs2
 (Hload_handler_spec: P= P1++(t,load_handler t x (S n)++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 (S n) t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros; subst.
  unfold load_handler; simpl.
  eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
  eapply hb_check_fail_spec_n; eauto.
  rewrite <- app_assoc; eauto.
Qed.

Corollary load_handler_race_spec: forall n x t P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1++(t,load_handler t x n++
  rest)::P2) (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) 
  v1 v2 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 n t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  destruct n; intros.
  - destruct vs1, vs2; clarify.
  - eapply load_handler_race_spec_n; eauto.
Qed.

Definition store_handler t x z :=
  Lock (X + x) :: hb_check (W + x) (C + t) z tmp1 tmp2 ++
  hb_check (R + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (W + x, t) tmp1.
Lemma store_handler_race_waw_spec_n: forall n x t P G P1 P2 rest v1 v2 vs1 vs2
 (Hstore_handler_spec: P= P1++(t,store_handler t x (S n)++rest)::P2) 
 (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 = Some (v1,v2)),
 exec_star (Some P) G (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 (S n) t) 
           None (upd_env (upd_env G t tmp1 v1) t tmp2 v2). 
Proof.
  intros.
  unfold store_handler in Hstore_handler_spec; clarify.
  eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
  eapply hb_check_fail_spec_n; eauto.
  rewrite <- app_assoc; eauto.
Qed.

Lemma store_handler_race_war_spec_n: forall n x t P G P1 P2 rest ve1 ve2 ve3 v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x (S n)++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 = n) 
 (Hfirst_gt12: first_gt (vs1++[ve1]) (vs2++[ve2]) = None)
 (Hfirst_gt32: first_gt (vs3++[ve3]) (vs2++[ve2]) = Some (v3,v2)),

 exec_star (Some P) G 
           (acq t (X + x) :: events_hb_check (W + x) (C + t) (vs1++[ve1]) (vs2++[ve2]) t ++
            events_hb_check (R + x) (C + t) (vs3++[ve3]) (vs2++[ve2]) t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) (vs1++[ve1]) (vs2++[ve2]) (S n) t ++
            mops_hb_check (R + x) (C + t) (vs3++[ve3]) (vs2++[ve2]) (S n) t) 
           None (upd_env (upd_env G t tmp1 v3) t tmp2 v2). 
Proof.
  intros.
  unfold store_handler in Hstore_handler_spec; clarify.
  eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
  rewrite <- app_assoc; eapply exec_star_trans.
  - apply hb_check_pass_spec_n; try (apply Hfirst_gt12); eauto.
  - assert(Hupd: upd_env (upd_env G t tmp1 v3) t tmp2 v2 =
                 upd_env (upd_env (upd_env (upd_env G t tmp1 ve1) t tmp2 ve2) t tmp1 v3) t tmp2 v2).
    { symmetry. rewrite upd_assoc. rewrite upd_overwrite. rewrite upd_assoc. rewrite upd_overwrite. eauto.
      eauto.
      eauto. }
    rewrite <- app_assoc, Hupd.
    eapply hb_check_fail_spec_n; eauto;
      clarify; rewrite app_length; rewrite plus_comm; auto.
Qed.

Lemma store_handler_norace_spec_n: forall n x t P G P1 P2 rest v1 v2 v3 vs1 vs2 vs3
 (Hstore_handler_spec: P= P1++(t,store_handler t x (S n)++rest)::P2) 
 (Hvs1: length vs1 = n) (Hvs2: length vs2 = n) (Hvs3: length vs3 =n) 
 (Hfirst_gt12: first_gt (vs1++[v1]) (vs2++[v2]) = None)
 (Hfirst_gt32: first_gt (vs3++[v3]) (vs2++[v2]) = None) v,
 exec_star (Some P) G 
           (acq t (X + x) :: events_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) t ++ 
            events_hb_check (R + x) (C + t) (vs3++[v3]) (vs2++[v2]) t ++               
            events_move (C+t) (W+x) t)
           (Acq t (X + x) :: mops_hb_check (W + x) (C + t) (vs1++[v1]) (vs2++[v2]) (S n) t ++ 
            mops_hb_check (R + x) (C + t) (vs3++[v3]) (vs2++[v2]) (S n) t ++
            mops_move (C+t,t) (W+x, t) t v) 
           (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v) t tmp2 v2).
Proof.
  intros.
  unfold store_handler in Hstore_handler_spec; clarify.
  eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
  rewrite <- app_assoc; eapply exec_star_trans.
  - apply hb_check_pass_spec_n; try (apply Hfirst_gt12); eauto.
  - repeat rewrite <- app_assoc.
    eapply exec_star_trans.
    + apply hb_check_pass_spec_n; try (apply Hfirst_gt32); eauto.
    + do 2 (rewrite upd_assoc, upd_overwrite; auto).
      rewrite upd_assoc; auto.
      setoid_rewrite upd_assoc at 2; auto.
      setoid_rewrite <- (upd_overwrite _ _ _ v3) at 3; apply move_spec; auto.
Qed.

Transparent hb_check.

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
  intros; destruct n; clarify.
  - destruct vs1, vs2, vs3; clarify.
    assert (upd_env G t tmp1 v t tmp2 = G t tmp2) as Heq
      by (apply upd_old; auto).
    rewrite <- Heq, upd_triv.
    eapply (exec_step' (exec_lock _ _ _ _ _ _ eq_refl)); clarify.
    apply move_spec; auto.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    assert (vs3 <> []) as Hnnil3 by (destruct vs3; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite (app_removelast_last 0 Hnnil3) in *.
    rewrite app_length in Hvs1, Hvs2, Hvs3; clarify.
    rewrite last_snoc; apply store_handler_norace_spec_n; auto; omega.
Qed.
   
Definition lock_handler t l z :=
  max_vc (L+l) (C+t) z tmp1 tmp2.

Lemma lock_handler_spec_n : forall n t l P G P1 P2 rest v1 v2 vss1 vss2

(Hmax_vc: P=P1++(t, lock_handler t l (S n) ++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
 exec_star (Some P) G
          (events_max_vc (L+l) (C+t) t (S n)) (mops_max_vc (L+l) (C+t) (vss1++[v1]) (vss2++[v2]) t (S n)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
Proof.
  intros.
  apply max_vc_spec_n; eauto.
Qed.

Lemma lock_handler_spec : forall n t l P G P1 P2 rest vs1 vs2 v

(Hmax_vc: P=P1++(t, lock_handler t l n ++ rest)::P2) (Htmp: tmp1 <> tmp2) (Hvs1: length vs1=n) (Hvs2: length vs2=n) (Ht: t<n),
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

Definition unlock_handler t l z :=
  max_vc (C + t) (L+l) z tmp1 tmp2 ++ inc_vc t (C + t) tmp1.

Lemma unlock_handler_spec_n : forall n l P G P1 P2 t rest v1 vss1 v2 vss2 vt
(Hset_vc: P=P1++(t, unlock_handler t l (S n) ++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n) (Htmp: tmp1<>tmp2),
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




Definition spawn_handler t u z tmp :=
  set_vc (C + t) (C + u) z tmp ++ inc_vc t (C + t) tmp.

(* mod? *)
Lemma spawn_handler_spec_n : forall n u tmp P G P1 P2 t rest v vss vt
(Hset_vc: P=P1++(t, spawn_handler t u (S n) tmp++ rest)::P2) (Hvs: length vss=n),
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
   
    

Definition wait_handler t u z :=
  max_vc (C + u) (C + t) z tmp1 tmp2.
(* The instrumentation pass is provided locations to store each of the
   race detection state components. *)
Lemma wait_handler_spec_n : forall n t u P G P1 P2 rest v1 v2 vss1 vss2

(Hmax_vc: P=P1++(t, wait_handler t u (S n) ++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
 exec_star (Some P) G
          (events_max_vc (C+u) (C+t) t (S n)) (mops_max_vc (C+u) (C+t) (vss1++[v1]) (vss2++[v2]) t (S n)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
Proof.
  intros.
  apply max_vc_spec_n; eauto.
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
 | Unlock l   => unlock_handler t l zt ++ [ins]
 | Spawn u li =>  spawn_handler t u zt tmp1 ++ [Spawn u (instrument li u)] 
 | Wait u     => [ins] ++ wait_handler t u zt
 (* the wait_handler should be called after the wait returns*)
 | _          => [ins]
end).

Fixpoint instrument (p: prog) (t: tid) : prog:=
match p with
| [] => []
| ins::inss => (instrument_instr ins t)++(instrument inss t)
end.

Section Sim_Defs.

Context {ML : @Memory_Layout var nat _}.

Definition consistent (m : list conc_op) := @SC _ _ _ ML _ _ Base m.

Definition can_read (m : list conc_op) p v := consistent (m ++ [Read 0 p v]).
Definition can_write (m : list conc_op) p :=
  forall v, consistent (m ++ [Write 0 p v]).

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

Lemma loc_valid_ops1_SC : forall c lc m
  (Hindep : Forall (fun c' => loc_of c' <> loc_of c) lc),
  consistent (m ++ lc ++ [c]) <->
  (consistent (m ++ lc) /\ consistent (m ++ [c])).
Proof.
  induction lc; clarify.
  { split; clarsimp.
    eapply consistent_app_SC; eauto. }
  specialize (IHlc (m ++ [a])); inversion Hindep; clarsimp.
  rewrite IHlc, loc_valid_SC; auto.
  split; intro Hcon; clarify.
  rewrite split_app in Hcon1; eapply consistent_app_SC; eauto.
Qed.

Corollary loc_valid_ops2_SC : forall m c lc
  (Hindep : Forall (fun c' => loc_of c' <> loc_of c) lc),
  consistent (m ++ c :: lc) <->
  (consistent (m ++ lc) /\ consistent (m ++ [c])).
Proof.
  intros; rewrite <- loc_valid_ops1_SC; auto.
  generalize (loc_comm_ops1_SC _ m [] Hindep); rewrite app_nil_r; auto.
Qed.

Lemma loc_valid_ops_SC : forall lc1 lc2 m
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lc2) lc1),
  consistent (m ++ lc1 ++ lc2) <->
  (consistent (m ++ lc1) /\ consistent (m ++ lc2)).
Proof.
  induction lc1; clarify.
  { split; clarsimp.
    eapply consistent_app_SC; eauto. }
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
  (Hcon : consistent (m ++ ops)), can_write (m ++ ops) p.
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

Lemma can_read_SC: forall p ops m v (Hcan: can_read m p v)
 (Hcon: consistent ( m ++ops)) (Hnmods: Forall (fun c => match c with
                                                            | Write _ x _ => p <> x
                                                            | ARW _ x _ _=> p <> x
                                                            | _ => True
                                                          end) ops),
 can_read (m++ops) p v.
Proof.
 induction ops; clarsimp.
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
  snd t2 = instrument (snd t1) (fst t1)) P1 P2.
Check state_sim.
(*all locals except tmp1 or tmp2 in G1 & G2 have the same values *)
Definition env_sim (G1 G2 : env) := forall t v, v <> tmp1 -> v <> tmp2 ->
  G1 t v = G2 t v.
(*tmp1 & tmp2 are not used in P*)
Definition fresh_tmps (P : state) :=
  Forall (fun e => Forall (fun i => fresh tmp1 i /\ fresh tmp2 i) (snd e)) P.
(* checks whether x points to some meta location *)
Definition meta_loc (x : ptr) := C <= fst x < C + zt \/
  L <= fst x < L + zl \/ R <= fst x < R + zv \/ W <= fst x < W + zv \/ X <= fst x < X+zv.

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
  | Spawn u li => u<zt /\ list_safe li
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
  
  induction li; clarify.
  admit.
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
  + eapply IHl1; eauto.
Qed.

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
  - rewrite loc_valid_ops2_SC; [split|].
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
  - rewrite loc_valid_ops2_SC; [split|].
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

Global Instance conc_op_dec : EqDec_eq conc_op.
Proof. eq_dec_inst. Qed.

Lemma write_any_value_SC : forall m t p v v',
  consistent (m ++ [Write t p v]) <-> consistent (m ++ [Write t p v']).
Proof.
  intros; unfold consistent, SC; setoid_rewrite lower_app.
  repeat rewrite lower_single; simpl; apply write_any_value.
Qed.  

Check mops_hb_check.
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
Qed.

Lemma in_mops_max_vc: forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_max_vc vc1 vc2 vs1 vs2 t n) ) (Hdis: vc1<>vc2) ,
  match c with 
  | Write tc p _ => fst p <> vc1
  | ARW _ _ _ _ => False
  | Read tc p _  => fst p = vc1 \/ fst p= vc2
  end.
Proof.
  intro n.
  induction n; intros;
  destruct c; clarify.
  -destruct vs1, vs2; clarify.
  -destruct vs1, vs2; clarify.
  -destruct vs1, vs2; clarify.
  -destruct vs1, vs2, x; clarify. 
   inversion Hin; inversion H; clarify.
   +inversion H0; clarify.
   + specialize(IHn _ _ _ _ _ _ H0); clarify.
  -destruct vs1,vs2, x; clarify.
   inversion Hin; clarify.
   +inversion H; clarify.
   +specialize(IHn _ _ _ _ _ _ H); clarify.
  -destruct vs1,vs2, x; clarify.
   specialize(IHn _ _ _ _ _ _ Hin); clarify.
Qed.

Lemma in_mops_set_vc: forall n c vc1 vc2 vs t
  (Hin: In c (mops_set_vc vc1 vc2 n t vs)) (Hdis: vc1<>vc2),
match c with
    | Read _ _ _ => True
    | Write _ x _ => (vc1, t) <> x
    | ARW _ x _ _ => False
  end.
Proof.
  intro n. induction n; intros; destruct c; clarify.
  -destruct vs; clarify.
   inversion Hin; clarify.
   +intro Heq. inversion H. clarify.
   +specialize(IHn (Write t0 x v) vc1 vc2 vs t H Hdis). simpl in IHn. auto.
  -destruct vs; clarify.
   specialize(IHn (ARW t0 x v v') vc1 vc2 vs t Hin Hdis). simpl in IHn. auto.
Qed.


Lemma mops_set_vc_meta_cc: forall vs n u t c (Hx : u < zt) (Ht : t < zt)
  (Hin : In c (mops_set_vc (C + u) (C + t) n t vs )), meta_loc (loc_of c).
Proof.
  induction vs; clarify.
  induction n; clarify.
  destruct n; clarify.
  destruct Hin; clarify; [ unfold meta_loc; clarify; omega | ].
  destruct H; clarify. unfold meta_loc; simpl; omega.
  specialize(IHvs n u t c Hx Ht H). auto.
Qed.


Lemma can_read_SC': forall p ops m v (Hcan: can_read m p v)
 (Hcon: consistent ( m ++ops)) (Hnmods: Forall (fun c => match c with
                                                            | Write _ x _ => p <> x
                                                            | ARW _ x _ _=> p <> x
                                                            | _ => True
                                                          end) ops),
 can_read (m++ops) p v.
Proof.
 induction ops; clarsimp.
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

(* doesn't need this right now
Lemma read_written_SC : forall m p v v' t (Hcon : consistent (m ++ [Write t p v])),
      consistent (m ++ [Write t p v; Read t p v']) <-> v' = v.
Proof.
  admit.
Qed.
*)

Lemma read_arwritten_SC : forall m p u v v' t (Hcon : consistent (m ++ [ARW t p u v])),
      consistent ((m ++ [ARW t p u v] )++ [Read t p v']) <-> v' = v.
Proof.
  intros.
  unfold consistent, SC in *; clarify.
  repeat rewrite lower_app in Hcon. rewrite lower_single in Hcon. clarify. 
  repeat rewrite lower_app,lower_single in *; clarify.
  rewrite <- app_assoc. 
  assert(lower m ++ [MRead p u; MWrite p v] ++ [MRead p v']=
         lower m ++ [MRead p u; MWrite p v ; MRead p v']) as Hsilly.
    auto.
  setoid_rewrite Hsilly.
  rewrite split_app in *.
  apply read_written. auto.
Qed.

Lemma can_release_SC: forall t m x
  (Hcon: consistent (m ++ [Acq t (X + x)])) (Hcan_write: can_write m (X + x, 0)),
 consistent ((m ++ [Acq t (X + x)]) ++ [Rel t (X + x)]).
Proof.
  intros. 
  rewrite can_arw_SC_iff.
  apply can_write_SC.
  -apply can_write_SC; auto.
  -rewrite read_arwritten_SC; auto.
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
  - rewrite loc_valid_ops2_SC; [split|].
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

Lemma mops_set_vc_con_cc : forall m s (Hs : clocks_sim m s) u t0 n
  (Hn : n <= zt) (Hu : u < zt) (Ht : t0 < zt) (Hcon : consistent m),
  consistent (m ++ 
    (mops_set_vc (C + t0) (C + u) n t0 (map (clock_of s t0) (rev (interval 0 n))))).

Proof.
  induction n; clarify.
  { rewrite app_nil_r; auto. }
  rewrite rev_app_distr; clarify.
  unfold clocks_sim in Hs; clarify.
  
  rewrite read_noop_SC.
  - rewrite loc_valid_ops2_SC; [split|].
    + apply IHn; auto; omega.
    + specialize (Hs1 _ Hu n); clarify.
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
  destruct Hin;
  destruct n; clarify; destruct l2; clarify;
  repeat (destruct H; clarify;  [unfold meta_loc; clarify; omega |]);
  eauto.
Qed.


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
  | iexec_unlock P1 P2 m rest vs1 vs2 v
      (Hunlock : P = P1 ++ (t, unlock_handler t m zt ++
                               Unlock m :: rest) :: P2)
      (Hlen1 : length vs1 = zt) (Hlen2 : length vs2 = zt) :
      iexec P G t (events_max_vc (C + t) (L + m) t zt ++
                   events_inc_vc (C + t) t ++ [rel t m])
                  (mops_max_vc (C + t) (L + m) vs1 vs2 t zt ++
                   mops_inc_vc (C + t) v t ++ [ARW t (m, 0) (S t) 0])
        (P1 ++ (t, rest) :: P2) (upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0))) t tmp1 (v + 1))
  | iexec_spawn P1 P2 u li rest vs v
      (Hspawn : P = P1 ++ (t, spawn_handler t u zt tmp1 ++
                              Spawn u li :: rest) :: P2)
      (Hnew : ~In u (map fst P)) (Hlen : length vs = zt) :
      iexec P G t (events_set_vc (C + t) (C + u) zt t ++
                   events_inc_vc (C + t) t ++ [fork t u])
                  (mops_set_vc (C + t) (C + u) zt t vs ++
                   mops_inc_vc (C + t) v t)
        (P1 ++ (t, rest) :: (u, li) :: P2) (upd_env G t tmp1 (v + 1))
  | iexec_wait P1 P2 u rest vs1 vs2
      (Hwait : P = P1 ++ (t, Wait u :: wait_handler t u zt ++ rest) 
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
    eapply exec_step_inv.
    + apply load_handler_norace_spec; try (apply Hle); eauto.
      unfold load_handler.
      simpl; do 2 rewrite <- (app_assoc (hb_check _ _ _ _ _)); eauto.
    + apply exec_load; eauto.
    + eauto.
    + eauto.
    + apply exec_unlock; eauto.
    + clarsimp.
    + clarsimp.
  - eapply exec_step_inv.
    eapply exec_step_inv.
    + apply store_handler_norace_spec.
      * unfold store_handler.
        simpl; eauto.
      * apply Hlen1.
      * apply Hlen2.
      * apply Hlen3.
      * auto.
      * auto.
    + apply exec_store; eauto.
    + eauto.
    + eauto.
    + apply exec_unlock; eauto.
    + clarsimp.
    + clarsimp.
      rewrite eval_old'; auto.
  - eapply exec_step'.
    + eapply exec_lock; eauto.
    + apply lock_handler_spec; eauto.
    + auto.
    + auto.
  - destruct zt; clarify.
    destruct (nil_dec vs1); [clarify|].
    destruct (nil_dec vs2); [clarify|].
    eapply exec_step_inv.
    + eapply unlock_handler_spec_n.
      { simpl; eauto. }
      { rewrite (app_removelast_last 0 n0), app_length, Nat.add_1_r in Hlen1;
          inversion Hlen1; eauto. }
      { rewrite (app_removelast_last 0 n1), app_length, Nat.add_1_r in Hlen2;
          inversion Hlen2; eauto. }
      { auto. }
    + apply exec_unlock; eauto.
    + clarsimp.
    + repeat rewrite <- app_removelast_last; clarsimp.
  - destruct zt; clarify.
    destruct (length vs) eqn: Hlen1; [clarify|].
    inversion Hlen; clarify.
    destruct (nil_dec vs); [clarify|].
    eapply exec_step_inv.
    + eapply spawn_handler_spec_n with (v := last vs 0).
      { eauto. }
      { rewrite (app_removelast_last 0 n0), app_length, Nat.add_1_r in Hlen1;
          inversion Hlen1; eauto. }
    + apply exec_spawn; eauto.
      rewrite map_app, in_app_iff in *; clarify.
    + clarsimp.
    + rewrite <- app_removelast_last; clarsimp.
  - destruct zt; clarify.
    destruct (nil_dec vs1); [clarify|].
    destruct (nil_dec vs2); [clarify|].
    eapply exec_step'.
    + apply exec_wait; auto.
    + apply wait_handler_spec_n.
      { simpl; eauto. }
      { rewrite (app_removelast_last 0 n0), app_length, Nat.add_1_r in Hlen1;
          inversion Hlen1; simpl; eauto. }
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

Inductive iexec_star : state -> env ->
  list operation -> list conc_op -> state -> env -> Prop :=
| iexec_refl P G : iexec_star P G [] [] P G
| iexec_step P G t o c P' G' (Hexec : iexec P G t o c P' G') lo lc P'' G''
    (Hexec' : iexec_star P' G' lo lc P'' G'') :
    iexec_star P G (o ++ lo) (c ++ lc) P'' G''.

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
  | Unlock m => exists vs1 vs2 v, length vs1 = zt /\ length vs2 = zt /\
      lo = events_max_vc (C + t) (L + m) t zt ++
           events_inc_vc (C + t) t ++ [rel t m] /\
      lc = mops_max_vc (C + t) (L + m) vs1 vs2 t zt ++
           mops_inc_vc (C + t) v t ++ [ARW t (m, 0) (S t) 0] /\
      P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env (upd_env G t tmp2 (Peano.max (last vs1 0) (last vs2 0)))
                   t tmp1 (v + 1)
  | Spawn u li => exists vs v, ~In u (map fst P) /\ length vs = zt /\
      lo = events_set_vc (C + t) (C + u) zt t ++
           events_inc_vc (C + t) t ++ [fork t u] /\
      lc = mops_set_vc (C + t) (C + u) zt t vs ++ mops_inc_vc (C + t) v t /\
      P' = P1 ++ (t, rest) :: (u, instrument li u)
           :: P2 /\ G' = upd_env G t tmp1 (v + 1)
  | Wait u => exists vs1 vs2, In (u, []) P /\ length vs1 = zt /\
      length vs2 = zt /\
      lo = join t u :: events_max_vc (C + u) (C + t) t zt /\
      lc = mops_max_vc (C + u) (C + t) vs1 vs2 t zt /\
      P' = P1 ++ (t, rest) :: P2 /\
      G' = upd_env (upd_env G t tmp1 (last vs1 0)) t tmp2
                   (Peano.max (last vs1 0) (last vs2 0))
  | Assert_le e1 e2 => eval (G t) e1 <= eval (G t) e2 /\ lo = [] /\ lc = [] /\
      P' = P1 ++ (t, rest) :: P2 /\ G' = G
  end.
Proof.
  intros.
  inversion Hiexec; clarify; exploit distinct_thread; eauto; clarify.
  - destruct i; clarify; try (destruct x); destruct zt; clarify.
  - admit.  
  - admit.
  - admit.
  - admit.
  - destruct i; clarify; try solve [try destruct x; destruct zt; clarify].
    admit.
  - admit.
  - admit.
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
  (Hfresh : fresh_tmps P1) (Hdistinct : distinct P2)
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
    specialize (Hmem (Read t0 (x, o) v)); destruct Hmem; clarify.
    rewrite in_app in *; clarify.
    admit.
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
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

End Sim_Defs.

End Instrumentation.
