Require Import List.
Require Import CoqEqDec.
Require Import Util.
Require Import VectorClocks.
Require Import Arith.
Require Import Coqlib.
Import ListNotations.

Set Implicit Arguments.

Local Close Scope Z.

Section TSan.
  Context `{Types : VC_base}.

  (* There must be a way to avoid this. *)
  Definition vector_clock := @vector_clock tid.
  Definition operation := @operation tid var lock.

  (* Abstract Pure TSan *)
  Definition state := ((tid -> vector_clock) * (lock -> vector_clock) *
    (var -> list (tid * vector_clock)) *
    (var -> list (tid * vector_clock)))%type.
  Definition s0 : state := (fun t => vc_inc t vc_bot, fun m => vc_bot,
    fun x => [], fun x => []).

  Inductive drop_le V :
    list (tid * vector_clock) -> list (tid * vector_clock) -> Prop :=
  | drop_nil : drop_le V [] []
  | drop_drop t1 V1 Vs Vs' (Hle : vc_le V1 V) (HVs : drop_le V Vs Vs') :
      drop_le V ((t1, V1) :: Vs) Vs'
  | drop_keep t1 V1 Vs Vs' (Hnle : ~vc_le V1 V) (HVs : drop_le V Vs Vs') :
      drop_le V ((t1, V1) :: Vs) ((t1, V1) :: Vs').

  Inductive step : state -> operation -> state -> Prop :=
  | on_read : forall C L R W t x Vs' R'
     (HW : Forall (fun s => vc_le (snd s) (C t)) (W x))
     (HR : drop_le (C t) (R x) Vs') (HR' : R' = upd R x ((t, C t) :: Vs')),
     step (C, L, R, W) (rd t x) (C, L, R', W)
  | on_write : forall C L R W t x R' W'
     (* We must be able to drop all previous reads and writes *)
     (HR : Forall (fun s => vc_le (snd s) (C t)) (R x))
     (HW : Forall (fun s => vc_le (snd s) (C t)) (W x))
     (HR' : R' = upd R x []) (HW' : W' = upd W x []),
     step (C, L, R, W) (wr t x) (C, L, R', W')
  | on_signal : forall C L R W t m L' C' (HL' : L' = upd L m (C t))
      (HC' : C' = upd C t (vc_inc t (C t))),
     step (C, L, R, W) (rel t m) (C', L', R, W)
  | on_wait : forall C L R W t m C' (HC' : C' = upd C t (vc_join (C t) (L m))),
     step (C, L, R, W) (acq t m) (C', L, R, W)
(* Are fork and join handled by signal and wait?
  | fork_step : forall C L R W t u C'
      (HC' : C' = upd (upd C u (vc_join (C u) (C t))) t (vc_inc t (C t))),
     step (C, L, R, W) (fork t u) (C', L, R, W)
  | join_step : forall C L R W t u C'
      (HC' : C' = upd (upd C t (vc_join (C t) (C u))) u (vc_inc u (C u))),
     step (C, L, R, W) (join t u) (C', L, R, W)*).

  Definition step_star := rtc step.

  Definition join_list (ss : list (tid * vector_clock)) :=
    fold_left (fun V s => vc_join V (snd s)) ss vc_bot.

  Lemma join_le_aux : forall V (ss : list (tid * vector_clock)) V0,
    vc_le (fold_left (fun V s => vc_join V (snd s)) ss V0) V <->
    vc_le V0 V /\ Forall (fun s => vc_le (snd s) V) ss.
  Proof.
    induction ss; clarify.
    - split; clarify.
    - rewrite IHss, vc_join_le; split; clarify.
      inversion H2; clarify.
  Qed.

  Lemma vc_bot_le : forall (V : vector_clock), vc_le vc_bot V.
  Proof. unfold vc_bot; repeat intro; omega. Qed.
  Hint Resolve vc_bot_le.

  Lemma join_le : forall V ss, vc_le (join_list ss) V <->
    Forall (fun s => vc_le (snd s) V) ss.
  Proof.
    intros; setoid_rewrite join_le_aux; split; clarify.
  Qed.

  Definition finite (V : vector_clock) :=
    exists l, forall t, ~In t l -> V t = 0.

  Lemma vc_le_thread : forall V V' t, vc_le V V' <-> V t <= V' t /\
    vc_le (upd V t 0) V'.
  Proof.
    split; repeat intro.
    - split; auto; intro; unfold upd; clarify; omega.
    - destruct H as [? Hle]; specialize (Hle t0); unfold upd in *; clarify.
  Qed.
      
  Lemma finite_le_dec : forall V V', finite V -> vc_le V V' \/ ~vc_le V V'.
  Proof.
    intros ??[??].
    generalize dependent V; induction x; intros.
    - left; intro; rewrite H; [omega | auto].
    - destruct (le_dec (V a) (V' a)); [|right; intro; auto].
      specialize (IHx (upd V a 0)); use IHx.
      destruct IHx as [IHx | IHx]; [left | right]; intro.
      + unfold upd in IHx; specialize (IHx t); clarify.
      + contradiction IHx; intro; unfold upd; clarify; omega.
      + unfold upd; clarify; apply H; intro; clarify.
  Qed.

  Lemma finite_drop : forall V l (Hfin : Forall (fun s => finite (snd s)) l),
    exists l', drop_le V l l'.
  Proof.
    induction l; intros.
    - eexists; constructor.
    - inversion Hfin; clarify.
      destruct a as (?, V'); destruct (finite_le_dec V H1).
      + eexists; apply drop_drop; eauto.
      + eexists; apply drop_keep; eauto.
  Qed.        

  Definition TS_sim (s1 : VectorClocks.state) (s2 : state) := match s1, s2 with
    (C1, L1, R1, W1), (C2, L2, R2, W2) => C1 = C2 /\ L1 = L2 /\
    forall x, join_list (R2 x) = R1 x /\ join_list (W2 x) = W1 x /\
      Forall (fun s => finite (snd s)) (R2 x) /\
      Forall (fun s => finite (snd s)) (W2 x) end.

  Lemma TS_sim0 : TS_sim (VectorClocks.s0) s0.
  Proof. clarify. Qed.

  Definition VC_step_star := @VectorClocks.step_star _ _ _
    tid_eq var_eq lock_eq.

  Lemma TS_sim1 : forall s1 tr s1' (Hsteps : VC_step_star s1 tr s1') s2
    (*tr0 (Hroot : VC_step_star s0 tr0 s1) s2 (Hwf : well_formed s2)*)
    (Hsim : TS_sim s1 s2),
    exists s2', step_star s2 tr s2' /\ TS_sim s1' s2'.
  Proof.
    intros ????; induction Hsteps; intros.
    { do 2 eexists; eauto; apply ss_refl. }
    assert (exists s2', step s2 l s2' /\ TS_sim s' s2') as [s2' [Hstep' Hsim']].
    destruct s2 as (((C2, L2), R2), W2).
    clear Hsteps IHHsteps; inversion Hstep; clarify.
    - generalize (Hsim22 x); intros (Hr & Hw & Hfinr & Hfinw).
      rewrite <- Hw, join_le in HW.
      generalize (finite_drop (C2 t) Hfinr); intros [? Hdrop].
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].

(* Would it be safe to have the base algorithm write the whole VC instead of
   just the current thread's time? *)
      unfold join_list in *; simpl.

  Lemma join_drop_le : forall t V l l' (Hdrop : drop_le V l l'),
    join_list ((t, V) :: l') = vc_join 

      unfold join_list; simpl
    - specialize (IHHsteps _ Hsim'); clarify; do 2 eexists; eauto; econstructor;
        eauto.
