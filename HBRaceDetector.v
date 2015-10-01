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

Lemma exec_star_trans : forall P G P' P'' G' G'' e1 m1 e2 m2,
  exec_star (Some P) G e1 m1 (Some P') G' -> exec_star (Some P') G' e2 m2 (Some P'') G''-> exec_star (Some P) G (e1++e2) (m1++m2) (Some P'') G''.
Proof.
Admitted. 

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
   eapply set_vc_spec_step in Hset_vc.
   rewrite set_vc_step in Hset_vc.
   apply nonempty_list in Hvs.
   inversion Hvs.
   inversion H.
   inversion H0.
   rewrite H1.
   assert (Hd: (x::x0)++[v]=x::(x0++[v])).
   eauto.
   rewrite Hd.
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
Grab Existential Variables.   
   Abort.
 

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

Fixpoint max tgt src tmp1 tmp2 :=
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
  Read t tgt v2
  (*;Write t tgt (nat.max v1 v2)*)
].

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

Lemma max_vc_spec_n : forall src tgt n tmp1 tmp2 P G P1 P2 t rest v1 v2 vss1 vss2

(Hmax_vc: P=P1++(t, max_vc src tgt (S n) tmp1 tmp2 ++ rest)::P2) (Hvs1: length vss1=n) (Hvs2: length vss2=n),
 exec_star (Some P) G
          (events_max_vc src tgt t (S n)) (mops_max_vc src tgt (vss1++[v1]) (vss2++[v2]) t (S n)) (Some (P1++(t,rest)::P2)) (upd_env (upd_env G t tmp1 v1) t tmp2 v2).
  
Definition assert_le (a b : ptr) (tmp1 tmp2:local): prog :=
[
    Load tmp1 a;
    Load tmp2 b;
    Assert_le (V tmp1) (V tmp2)
].

Definition events_assert_le (a b: ptr) (t:tid) : list Lang.operation :=
[
  rd t a;
  rd t b
].

Definition mops_assert_le (a b : ptr) (v1 v2: nat) (t: tid): list conc_op :=
[
  Read t a v1;
  Read t b v2
].


Fixpoint hb_check C1 C2 z tmp1 tmp2 :=
match z with
| 0 => []
| S n =>(assert_le (C1,n) (C2,n) tmp1 tmp2)++ hb_check C1 C2 n tmp1 tmp2
end.

Fixpoint events_hb_check (C1 C2: var) (z:nat) (t:tid) : list Lang.operation :=
match z with
| 0 => []
| S n => events_assert_le (C1,n) (C2,n) t++events_hb_check C1 C2 n t
end.

Fixpoint mops_hb_check (C1 C2: var) (vs1 vs2: list nat) (z:nat) (t:tid) : list conc_op :=
match (z,vs1,vs2) with
| (S n, v1::vss1, v2::vss2) => mops_assert_le (C1,n) (C2,n) v1 v2 t ++ mops_hb_check C1 C2 vss1 vss2 n t
| _ => []
end.

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
