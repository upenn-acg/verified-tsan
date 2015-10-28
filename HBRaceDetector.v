Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import FunctionalExtensionality.
Set Implicit Arguments.

Definition move src tgt tmp := [Load tmp src; Store tgt (V tmp)].

Lemma exec_step' : forall P G o c P' G' rd mops
  (Hexec : exec P G o c P' G') lo lc P'' G''
  (Hexec' : exec_star P' G' lo lc P'' G'')
  (Hrd : rd = opt_to_list o ++ lo)
  (Hmops : mops = opt_to_list c ++ lc),
  exec_star (Some P) G rd mops P'' G''.
Proof.
  clarify; eapply exec_step; eauto.
Qed.

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
Definition load_handler t x C R (W : var) z tmp1 tmp2 := 
  hb_check (W + x) (C + t) z tmp1 tmp2 ++
  move (C + t, t) (R + x, t) tmp1.

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

Corollary load_handler_norace_spec: forall n x C R W t tmp1 tmp2 P G P1 P2 rest
  vs1 vs2 (Hload_handler_spec: P = P1 ++ (t, load_handler t x C R W n tmp1 tmp2
  ++ rest) :: P2) (Htmp : tmp1 <> tmp2) (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hfirst_gt : first_gt vs1 vs2 = None) v,
  exists v2, exec_star (Some P) G
    (events_hb_check (W + x) (C + t) vs1 vs2 t ++ events_move (C + t) (R + x) t)
    (mops_hb_check (W + x) (C + t) vs1 vs2 n t ++ mops_move (C + t, t) (R + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 v2).
Proof.
  intros; destruct n; clarify.
  - destruct vs1, vs2; clarify.
    eexists; rewrite upd_triv; apply move_spec; auto.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite app_length in Hvs1, Hvs2; clarify.
    eexists; apply load_handler_norace_spec_n; auto; omega.
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
Qed.

Corollary store_handler_norace_spec: forall n x C R W t tmp1 tmp2 P G P1 P2 rest
  vs1 vs2 vs3 (Hstore_handler_spec: P = P1 ++ (t, store_handler t x C R W n tmp1 tmp2
  ++ rest) :: P2) (Htmp : tmp1 <> tmp2) (Hvs1 : length vs1 = n)
  (Hvs2 : length vs2 = n) (Hvs3: length vs3 = n) (Hfirst_gt12 : first_gt vs1 vs2 = None) (Hfirst_gt32: first_gt vs3 vs2 = None) v,
  exists v2, exec_star (Some P) G
    (events_hb_check (W + x) (C + t) vs1 vs2 t ++ 
     events_hb_check (R + x) (C + t) vs3 vs2 t ++
     events_move (C + t) (W + x) t)
    (mops_hb_check (W + x) (C + t) vs1 vs2 n t ++
     mops_hb_check (R + x) (C + t) vs3 vs2 n t ++
     mops_move (C + t, t) (W + x, t) t v)
    (Some (P1 ++ (t, rest) :: P2)) (upd_env (upd_env G t tmp1 v) t tmp2 v2).
Proof.
  intros; destruct n; clarify.
  - destruct vs1, vs2, vs3; clarify.
    eexists; rewrite upd_triv; apply move_spec; auto.
  - assert (vs1 <> []) as Hnnil1 by (destruct vs1; clarify).
    assert (vs2 <> []) as Hnnil2 by (destruct vs2; clarify).
    assert (vs3 <> []) as Hnnil3 by (destruct vs3; clarify).
    rewrite (app_removelast_last 0 Hnnil1) in *.
    rewrite (app_removelast_last 0 Hnnil2) in *.
    rewrite (app_removelast_last 0 Hnnil3) in *.
    rewrite app_length in Hvs1, Hvs2, Hvs3; clarify.
    eexists; apply store_handler_norace_spec_n; auto; omega.
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

Definition can_read (m : list conc_op) p v := consistent (m ++ [Read 0 p v]).
Definition can_write (m : list conc_op) p :=
  forall v, consistent (m ++ [Write 0 p v]).

Variables (C L R W : var) (zt zl zv : nat) (tmp1 tmp2 : local)
  (Htmp : tmp1 <> tmp2).

Definition vstate := @VectorClocks.state tid var lock.

Definition clock_match m V x := forall t,
  if lt_dec t zt then can_read m (x, t) (V t) /\ can_write m (x, t)
  else V t = 0.

Definition clocks_sim (m : list conc_op) (s : vstate) :=
  (forall t, t < zt -> clock_match m (clock_of s t) (C + t)) /\
  (forall l, l < zl -> clock_match m (lock_of s l) (L + l)) /\
  (forall v, v < zv -> clock_match m (read_of s v) (R + v) /\
     clock_match m (write_of s v) (W + v)).

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

Lemma fresh_tmps_step : forall P G o c P' G' (Hfresh : fresh_tmps P)
  (Hstep : exec P G o c P' G'),
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
  | Lock m => ~meta_loc (m, 0) /\ m < zv
  | Unlock m => ~meta_loc (m, 0) /\ m < zv
  | Spawn _ li => list_safe li
  | _ => True
  end.

(* all the instructions in P are safe*)
Definition safe_locs (P : state) :=
  Forall (fun e => Forall safe_instr (snd e)) P.

Lemma safe_locs_step : forall P G o c P' G' (Hlocs : safe_locs P)
  (Hstep : exec P G o c P' G'),
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

(* updates to different locals don't interfere with each other*)
Lemma upd_old : forall G t1 a1 v1 t2 a2 (Ha : a1 <> a2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.
(* updates to different stacks(per-thread) don't interfere with each other*)
Lemma upd_old_t : forall G t1 a1 v1 t2 a2 (Ht : t1 <> t2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

(* all the memory operations only access meta locations*)
Lemma mops_hb_check_meta : forall l1 l2 n x t c (Hx : x < zv) (Ht : t < zt)
  (Hin : In c (mops_hb_check (W + x) (C + t) l1 l2 n t)), meta_loc (loc_of c).
Proof.
  induction l1; clarify.
  destruct n; clarify.
  destruct l2; clarify.
  destruct Hin as [? | [? | ?]].
  - unfold meta_loc; clarify; omega.
  - unfold meta_loc; clarify; omega.
  - clarify.
    eapply IHl1; eauto.
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
    unfold can_read, consistent, SC in Hs11; rewrite lower_app in Hs11; auto.
  - clarify.
  - unfold clocks_sim in Hs; clarify.
    specialize (Hs22 _ Hx); clarify.
    specialize (Hs222 n); clarify.
    unfold can_read, consistent, SC in Hs2221; rewrite lower_app in Hs2221;
      auto.
  - clarify.
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

Typeclasses eauto := 2.
Lemma instrument_sim_safe : forall P P1 P2 G1 G2 h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 o c (Some P1') G1')
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
  - do 5 eexists; [|split; [|split; [|clarify; split]]].
    + eapply exec_step; [|apply exec_refl].
      apply exec_assign; eauto.
    + auto.
    + apply Forall2_app; auto.
    + repeat intro; unfold upd_env, upd; clarify.
      setoid_rewrite Forall_app in Hfresh; clarify.
      inversion Hfresh2 as [|? ? Hi]; clarify; inversion Hi; clarify.
      apply eval_sim; intros; apply HGsim; intro; clarify.
    + split; clarify.
  -destruct x as (x, o).
    inversion Hsafe; clarify.
    inversion Hstep0; clarify.
    exploit load_handler_norace_spec.
    { eauto. }
    { eauto. }
    { instantiate (2 := map (W0 x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      rewrite <- minus_n_O; eauto. }
    { instantiate (1 := map (C0 t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { apply vc_le_first_gt. auto. }
    rewrite plus_0_r; intros [v2 Hload].
    rewrite <- app_assoc; do 5 eexists; [|split; [|split; [|clarify; split]]].
    + eapply exec_star_trans; [apply Hload|].
      eapply exec_step; [|apply exec_refl].
      simpl; apply exec_load; eauto.
    + rewrite app_nil_r; simpl.
      instantiate (1 := v).
      instantiate (1 := C0 t0 t0).
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
    + apply Forall2_app; auto.
    + unfold env_sim in *; clarify.
      destruct (eq_dec v0 a); [subst | repeat rewrite upd_old; auto].
      destruct (eq_dec t t0); [subst | repeat rewrite upd_old_t; auto].
      repeat rewrite upd_same; auto.
    + setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      contradiction H2.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      rewrite in_app in H1; destruct H1; [eapply mops_hb_check_meta; eauto|].
      destruct H; clarify; unfold meta_loc; simpl; omega.
  -destruct x as (x,o). 
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   
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
     apply vc_le_first_gt. eauto.
   rewrite plus_0_r; intros [v2 Hstore].
   rewrite <- app_assoc; do 5 eexists; [|split; [|split; [|clarify; split]]].
   +eapply exec_star_trans; [apply Hstore|].
    eapply exec_step; [|apply exec_refl].
      simpl; apply exec_store; eauto.
   +rewrite app_nil_r; simpl.
      
    instantiate (1 := C0 t0 t0).
      setoid_rewrite Forall_app in Hlocs; clarify.
      
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      unfold consistent, SC in *.
      rewrite lower_app in Hcon; repeat rewrite lower_app;
        rewrite lower_single in Hcon; rewrite lower_single; simpl in *.
      Print reads_noops.
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

       rewrite upd_old.

       rewrite upd_old.
       unfold env_sim in HGsim.
       symmetry. eapply HGsim.

setoid_rewrite Forall_app in Hfresh; clarify;
inversion Hfresh2 as [|? ? Hi']; clarify; inversion Hi'; clarify.
      
       destruct (eq_dec v tmp1). 
       rewrite e0 in H. contradiction. eauto.
setoid_rewrite Forall_app in Hfresh; clarify;
inversion Hfresh2 as [|? ? Hi']; clarify; inversion Hi'; clarify.
       destruct (eq_dec v tmp2).
       rewrite e0 in H. contradiction. eauto.
setoid_rewrite Forall_app in Hfresh; clarify;
inversion Hfresh2 as [|? ? Hi']; clarify; inversion Hi'; clarify.
       destruct (eq_dec v tmp2).
       rewrite e0 in H. contradiction. eauto.
       destruct (eq_dec v tmp1).
       rewrite e0 in H. contradiction. eauto.      
setoid_rewrite Forall_app in Hfresh; clarify;
inversion Hfresh2 as [|? ? Hi']; clarify; inversion Hi'; clarify.
       destruct (eq_dec v tmp2).
       rewrite e0 in H. contradiction. eauto.

       * 
         apply (mops_hb_check_conR Hs); auto.
        eapply consistent_app; eauto.
      * apply mops_hb_check_read.
      * apply (mops_hb_check_con Hs); auto.
        eapply consistent_app; eauto.
      * eapply mops_hb_check_read.
      
+ apply Forall2_app; auto.
    + unfold env_sim in *; clarify.
      repeat rewrite upd_old.
      apply HGsim; eauto.
      eauto. eauto.
    
      (*destruct (eq_dec v0 a); [subst | repeat rewrite upd_old; auto].
      destruct (eq_dec t t0); [subst | repeat rewrite upd_old_t; auto].
      repeat rewrite upd_same; auto.*)
    + setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify. right. left. 
      assert(Heval: eval (upd_env (upd_env G2 t0 tmp1 (C0 t0 t0)) t0 tmp2 v2 t0) e = eval (G1' t0) e).
       apply eval_sim.
       inversion Hfresh.
       intros. repeat rewrite upd_old.

       unfold env_sim in HGsim.
         symmetry. apply HGsim.
      (*rewrite in_app in H1; destruct H1; [eapply mops_hb_check_meta; eauto|].
      destruct H; clarify; unfold meta_loc; simpl; omega.*)admit.
Admitted.

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

(*(* Bigger-step semantics for instrumentation *)
Inductive exec_instr P G :
  list operation -> list conc_op -> option state -> env -> Prop :=
| instr_assign P1 P2 t a e rest
    (Hassign : P = P1 ++ (t, Assign a e :: rest) :: P2) :
    exec P G [] [] (Some (P1 ++ (t, rest) :: P2)) (upd_env G t a (eval (G t) e))
| instr_load P1 P2 t a x vs1 vs2 v rest
    (Hload : P = P1 ++ (t, load_handler t x C R W z tmp1 tmp2 ++ Load a x ::
       rest) :: P2) (Hvs1 : length vs1 = zt) (Hvs2 : length vs2 = zt)
    (Hle : first_gt vs1 vs2 = None) :
    exec P G (Some (rd t (fst x))) (Some (Read t x v))
      (Some (P1 ++ (t, rest) :: P2)) (upd_env G t a v)
| exec_store P1 P2 t x e rest
    (Hstore : P = P1 ++ (t, Store x e :: rest) :: P2) :
    exec P G (Some (wr t (fst x))) (Some (Write t x (eval (G t) e)))
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
*)

Lemma instrument_sim_race : forall P P1 P2 G1 G2 h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 o c (Some P1') G1')
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
     steps in which instrumented sections execute in blocks. *)

Lemma instrument_sim_safe2 : forall P P1 P2 G1 G2 h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o2 c2 P2' G2' (Hstep : exec P2 G2 o2 c2 (Some P2') G2')
  (Hcon : consistent (m ++ opt_to_list c2)) s (Hs : clocks_sim m s),
  
  exists o c P1' G1', exec P1 G1 o c P1' G1' /\
    state_sim P1' P2' /\ env_sim G1' G2' /\
    mem_sim c (opt_to_list c2 ++ lc) /\
        exists s', step_star s (opt_to_list o) s' /\
                   clocks_sim (m ++ opt_to_list c2 ++ lc) s'
    | None => forall s', ~step_star s (opt_to_list o) s'
    end end.
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
