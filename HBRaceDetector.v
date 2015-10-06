Require Import Lang.
Require Import Util.
Require Import VectorClocks.
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
  Admitted.


Definition events_move (src tgt:ptr) (t:tid): list Lang.operation := [rd t src; wr t tgt].

Definition mops_move (src tgt: ptr) (t:tid) (v:nat): list conc_op := [Read t src v; Write t tgt v].

Lemma move_spec : forall src tgt tmp P P1 P2 G t rest v
  (Hmove : P = P1 ++ (t, move src tgt tmp ++ rest) :: P2),
  exec_star (Some P) G
            (events_move src tgt t) (mops_move src tgt t v)
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

Fixpoint set_vc (tgt : var (* loc of target VC *))
  (src : var (* loc of source VC *)) (z : nat (* thread bound/size of VCs *))
  (tmp : local (* a local to use as temp *)) :=
(* Move all z of the timestamps in src into tgt. *)
match z with
| 0 => []
| S n =>  move (src,n) (tgt,n) tmp++set_vc tgt src n tmp 
end.

Fixpoint events_set_vc (src tgt: var) (z : nat) (t : tid) : list Lang.operation:=
match z with
| O => []
| S n => (events_move (src,n) (tgt,n) t)++events_set_vc src tgt n t
end.

Fixpoint mops_set_vc (src tgt: var) (z : nat) (t : tid) (vs: list nat): list conc_op :=
match (z,vs) with
| (S n,v::vss) => (mops_move (src,n) (tgt,n) t v)++mops_set_vc src tgt n t vss
| _ => []
end.

Lemma empty_list : forall (vs:list nat) (Hl: (length vs) = 0), vs=[]. 
Admitted.

Lemma set_vc_spec_0 : forall tgt src tmp P G P1 P2 t rest 
(Hset_vc0: P=P1++(t, set_vc tgt src 0 tmp ++ rest)::P2),
exec_star (Some P) G [] [] (Some (P1++(t,rest)::P2)) G.
Proof.
  intros.
  unfold set_vc in Hset_vc0.
  rewrite Hset_vc0.
  simpl.
  eapply exec_refl.
Qed.

Lemma events_set_vc_step: forall src tgt n t,
  events_set_vc src tgt (S n) t = (events_move (src,n) (tgt,n) t)++events_set_vc src tgt n t.
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

Lemma set_vc_step: forall  tgt src n tmp,
  set_vc tgt src (S n) tmp =(move (src,n) (tgt,n) tmp)++set_vc tgt src n tmp.
Proof.
  intros.
  eauto.
Qed.

Lemma nonempty_list: forall (ls : list nat) n, 
  length ls = S n -> exists x xs, ls=x::xs /\ length xs=n.
Proof.
Admitted.

Lemma set_vc_spec_step : forall tgt src n tmp P G P1 P2 t rest v 
(Hset_vc: P=P1++(t, set_vc tgt src (S n) tmp++ rest)::P2),
 exec_star (Some P) G
          (events_move (src,n) (tgt,n) t) (mops_move (src,n) (tgt,n) t v) (Some (P1++(t, set_vc tgt src n tmp++rest)::P2)) (upd_env G t tmp v).
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
Admitted. 
Lemma list_cons_plus_assoc: forall (T:Type) (x:T) (x0 y: list T),
 (x::x0)++y=x::(x0++y).
Proof.
  intros.
  auto.
Qed.

Lemma set_vc_spec_n : forall n tgt src tmp P G P1 P2 t rest v vss 
(Hset_vc: P=P1++(t, set_vc tgt src (S n) tmp++ rest)::P2) (Hvs: length vss=n),
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
 
Definition inc_vc t tgt tmp := [
  Load tmp (tgt, t);
  Assign tmp (Plus (V tmp) (I 1));
  Store (tgt, t) (V tmp)
].

Definition events_inc_vc (tgt:var) (t:tid): list Lang.operation:=
  [rd t (tgt,t); wr t (tgt,t)]. 
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

Definition events_max (src tgt:ptr) (t:tid) : list Lang.operation :=
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
  intros.
Admitted.

Lemma upd_assoc: forall G t a1 a2 v1 v2
 (Ha: a1<>a2),
 upd_env (upd_env G t a1 v1) t a2 v2 = upd_env (upd_env G t a2 v2) t a1 v1.
Proof.
  intros.
Admitted.

Lemma max_spec : forall P P1 P2 rest G src tgt tmp1 tmp2 v1 v2 t
 (Hmax_spec: P= P1++((t, max src tgt tmp1 tmp2++rest)::P2)) (Hdist: tmp1<> tmp2),
exec_star (Some P) G (events_max src tgt t) (mops_max src tgt v1 v2 t) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).  
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
 
Fixpoint max_vc tgt src z tmp1 tmp2 :=
match z with
| 0 => []
| S n => max (tgt,n) (src,n) tmp1 tmp2++ max_vc tgt src n tmp1 tmp2
end.

Fixpoint events_max_vc (src tgt:var) (t: tid) (z:nat): list Lang.operation:=
match z with
|0 => []
|S n => events_max (src,n) (tgt,n) t ++ events_max_vc src tgt t n
end.

Fixpoint mops_max_vc (src tgt: var) (vs1 vs2: list nat) (t:tid) (z:nat) : list conc_op:=
match (z,vs1,vs2) with
|(0,[],[]) => []
|(S n,v1::vss1,v2::vss2) => mops_max (src,n) (tgt,n) v1 v2 t ++ mops_max_vc src tgt vss1 vss2 t z 
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
  events_max_vc src tgt t (S n) = events_max (src,n) (tgt,n) t ++ events_max_vc src tgt t n.
Proof.
  intros.
  eauto.
Qed.

Lemma mops_max_vc_step: forall src tgt n v1 v2 vss1 vss2 t,
  mops_max_vc src tgt (v1::vss1) (v2::vss2) t (S n)= mops_max (src,n) (tgt,n) v1 v2 t ++ mops_max_vc src tgt vss1 vss2 t n.
Proof.
  intros.
  eauto.
Admitted.

Lemma max_vc_step: forall  tgt src n tmp1 tmp2,
  max_vc tgt src (S n) tmp1 tmp2 = max (tgt,n) (src,n) tmp1 tmp2++ max_vc tgt src n tmp1 tmp2.
Proof.
  intros.
  eauto.
Qed.

Lemma max_vc_spec_step : forall n src tgt tmp1 tmp2 P G P1 P2 t rest v1 v2

(Hmax_vc: P=P1++(t, max_vc src tgt (S n) tmp1 tmp2 ++ rest)::P2) (Htmp: tmp1 <> tmp2),
 exec_star (Some P) G
          (events_max (src,n) (tgt,n) t) (mops_max (src,n) (tgt,n) v1 v2 t) (Some (P1++(t, max_vc src tgt n tmp1 tmp2 ++ rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 (Peano.max v1 v2)).
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
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.    
Definition assert_le (a b : ptr) (tmp1 tmp2:local): prog :=
[
    Load tmp1 a;
    Load tmp2 b;
    Assert_le (V tmp1) (V tmp2)
].

Definition events_assert_le(a b: ptr) (t:tid) : list Lang.operation :=
[
  rd t a;
  rd t b
].

Definition mops_assert_le (a b : ptr) (v1 v2: nat) (t: tid): list conc_op :=
[
  Read t a v1;
  Read t b v2
].

Lemma ble_nat_implies_le: forall v1 v2,
 ble_nat v1 v2 = true -> v1 <=v2.
Proof.
  Admitted.

Lemma nble_nat_implies_nle: forall v1 v2,
 ble_nat v1 v2 = false ->~ v1 <= v2.
Proof.
  Admitted.

Lemma assert_le_fail_spec: forall P P1 P2 rest G a b tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le a b tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: ~ v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le a b v1 v2 t)
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

Lemma assert_le_pass_spec: forall P P1 P2 rest G a b tmp1 tmp2 t v1 v2
 (Hassert_le_spec: P=P1++(t,assert_le a b tmp1 tmp2++rest)::P2) (Htmp: tmp1<>tmp2) (Hv1v2: v1 <= v2),
 exec_star (Some P) G (events_assert_le a b t) (mops_assert_le a b v1 v2 t)
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

Fixpoint events_hb_check (C1 C2: var) (vs1 vs2: list nat) (z:nat) (t:tid) : list Lang.operation :=
match (z,vs1,vs2) with
| (S n, v1::vss1, v2::vss2) => events_assert_le (C1,n) (C2,n) t++
                               if ble_nat v1 v2 then events_hb_check C1 C2 vss1 vss2 n t else []
| _ => []
end.

Lemma events_hb_check_step : forall C1 C2 v1 v2 vs1 vs2 n t,
 events_hb_check C1 C2 (v1::vs1) (v2::vs2) (S n) t = 
 events_assert_le (C1,n) (C2,n) t ++ 
 if ble_nat v1 v2 then events_hb_check C1 C2 vs1 vs2 n t else [].
Proof.
  intros. auto.
Qed.



Fixpoint mops_hb_check (C1 C2: var) (vs1 vs2: list nat) (z:nat) (t:tid) : list conc_op :=
match (z,vs1,vs2) with
| (S n, v1::vss1, v2::vss2) => mops_assert_le (C1,n) (C2,n) v1 v2 t ++ 
                               (if ble_nat v1 v2 then mops_hb_check C1 C2 vss1 vss2 n t
                               else [])
| _ => []
end.

Lemma mops_hb_check_step : forall C1 C2 v1 v2 vs1 vs2 n t,
 mops_hb_check C1 C2 (v1::vs1) (v2::vs2) (S n) t =
 mops_assert_le (C1,n) (C2,n) v1 v2 t ++
 if ble_nat v1 v2 then mops_hb_check C1 C2 vs1 vs2 n t else [].
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
   exec_star (Some P) G (events_assert_le (C1,n) (C2,n) t)
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
   exec_star (Some P) G (events_assert_le (C1,n) (C2,n) t)
             (mops_assert_le (C1,n) (C2,n) v1 v2 t) 
             (Some (P1++(t,hb_check C1 C2 n tmp1 tmp2++rest)::P2))
             (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
Proof.
  intros.
  rewrite Hhb_heck_step.
  rewrite hb_check_step.
  eapply assert_le_pass_spec; eauto; clarify.
Qed.
    
Fixpoint first_gt l1 l2 z :=
match (z,l1,l2) with
| (S n, x1::xs1, x2::xs2) => if ble_nat x1 x2 then first_gt xs1 xs2 n else Some (x1,x2) 
| _   => None
end.

Lemma first_gt_step: forall x1 x2 xs1 xs2 n,
first_gt (x1::xs1) (x2::xs2) (S n) = if ble_nat x1 x2 then first_gt xs1 xs2 n else Some (x1,x2).
Proof.
  intros. eauto.
Qed.

Lemma hb_check_fail_spec_n: forall n C1 C2 t tmp1 tmp2 P G P1 P2 rest v1 v2 vs1 vs2
 (Hhb_check_spec: P= P1++(t,hb_check C1 C2 (S n) tmp1 tmp2++rest)::P2) 
 (Htmp: tmp1 <> tmp2) (Hvs1: length vs1 = S n) (Hvs2: length vs2 = S n) 
 (Hfirst_gt: first_gt vs1 vs2 (S n)= Some (v1,v2)),
 exec_star (Some P) G (events_hb_check C1 C2 vs1 vs2 (S n) t)
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
   +apply nble_nat_implies_nle in cond. eauto.
   
  - rewrite H3, H5, first_gt_step in Hfirst_gt. 
    destruct (ble_nat x x0) eqn:Hxx0; eauto.
    +rewrite H3,H5. 
     rewrite events_hb_check_step, mops_hb_check_step.
     rewrite Hhb_check_spec, Hxx0,  hb_check_step.
     eapply exec_star_trans.
     *apply assert_le_pass_spec; clarify.
      apply ble_nat_implies_le in Hxx0. eauto.
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
     apply nble_nat_implies_nle in Hxx0. eauto.
Qed.
       
     
     
 
  

(* Since everything is a nat, we can use C + t as the t component of C. *)
Definition load_handler t x C R (W : var) z tmp1 tmp2 := 
  hb_check W C z tmp1 tmp2 ++
  move (C + t, t) (R + x, t) tmp1.
  
Definition store_handler t x C (R:var) W z tmp1 tmp2 := 
  hb_check W C z tmp1 tmp2 ++
  hb_check R C z tmp1 tmp2 ++
  move (C + t, t) (W + x, t) tmp1.
Definition lock_handler t l C L z tmp1 tmp2 :=
  max_vc (C+t) (L+l) z tmp1 tmp2.
  
Definition unlock_handler t l (C : var (* start of thread VCs *))
  (L : var (* start of lock VCs *)) z tmp1 tmp2 :=
  max_vc (L + l) (C + t) z tmp1 tmp2 ++ inc_vc t (C + t) tmp1.
Definition spawn_handler t u C z tmp :=
  set_vc (C + u) (C + t) z tmp ++ inc_vc t (C + t) tmp.
Definition wait_handler t u C z tmp1 tmp2 :=
  max_vc (C + t) (C + u) z tmp1 tmp2.
(* The instrumentation pass is provided locations to store each of the
   race detection state components. *)

Fixpoint instrument_instr (C L R W : var) z tmp1 tmp2 (ins : instr) (t : tid)
  : prog :=
let instrument := fix f p t :=
  match p with
  | [] => []
  | ins::inss => (instrument_instr C L R W z tmp1 tmp2 ins t)++(f inss t)
  end in
(match ins with
 | Load a (x, 0)   => load_handler t x C R W z tmp1 tmp2 ++ [ins]
 | Store (x, 0) e  => store_handler t x C R W z tmp1 tmp2 ++ [ins]
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
