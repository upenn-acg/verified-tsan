Require Import List.
Require Import CoqEqDec.
Require Import Util.
Require Import Arith.
Require Import Wf_nat.
Import ListNotations.

Set Implicit Arguments.

Ltac dec_eq := match goal with 
  | |- context[eq_dec ?a ?b] => destruct (eq_dec a b); clarify
  | [H : context[eq_dec ?a ?b] |- _] => destruct (eq_dec a b); clarify end.

Ltac wf_check := unfold ge in *; match goal with
| [H : ?C ?t ?t <= ?C ?u ?t,
   Hwf : forall u t, t <> u -> ?C u t < ?C t t |- _] =>
     specialize (Hwf u t); destruct (eq_dec u t); clarify; try omega
| [H : ?C ?t ?t <= ?L ?m ?t, Hwf : forall m t, ?L m t < ?C t t |- _] =>
     specialize (Hwf m t); omega
end.

Section RTC.
  Variables (S L : Type) (step : S -> L -> S -> Prop).

  Inductive rtc s : list L -> S -> Prop :=
    | ss_refl : rtc s [] s
    | ss_step l s' l' s'' (Hstep : step s l s') (Hsteps : rtc s' l' s'') :
        rtc s (l :: l') s''.

  Lemma rtc_snoc : forall tr s s' a s'' (Hsteps : rtc s tr s')
    (Hstep : step s' a s''), rtc s (tr ++ [a]) s''.
  Proof.
    intros; induction Hsteps; clarify.
    - econstructor; eauto; constructor.
    - econstructor; eauto.
  Qed.

  Lemma rtc_snoc_inv : forall tr s s' a (Hsteps : rtc s (tr ++ [a]) s'),
    exists s'', rtc s tr s'' /\ step s'' a s'.
  Proof.
    induction tr; clarify.
    - inversion Hsteps as [|? ? ? ? ? Hsteps']; clarify.
      inversion Hsteps'; clarify.
      eexists; split; [apply ss_refl | auto].
    - inversion Hsteps as [|? ? ? ? ? Hsteps']; clarify.
      specialize (IHtr _ _ _ Hsteps'); clarify.
      eexists; split; [eapply ss_step; eauto | eauto].
  Qed.

  Lemma rtc_app_inv : forall tr1 tr2 s s', rtc s (tr1 ++ tr2) s' ->
    exists s'', rtc s tr1 s'' /\ rtc s'' tr2 s'.
  Proof.
    induction tr1; clarify.
    - eexists; split; eauto; apply ss_refl.
    - inversion H as [| ? ? ? ? Ha Hsteps]; clarify.
      specialize (IHtr1 _ _ _ Hsteps); clarify.
      eexists; split; [econstructor|]; eauto.
  Qed.

  Lemma rtc_trans : forall s tr s' tr' s'' (Hsteps : rtc s tr s')
    (Hsteps' : rtc s' tr' s''), rtc s (tr ++ tr') s''.
  Proof.
    intros; induction Hsteps; clarify.
    econstructor; eauto.
  Qed.

End RTC.

Class VC_base tid var lock (tid_eq : EqDec_eq tid) (var_eq : EqDec_eq var)
  (lock_eq : EqDec_eq lock).

Section VectorClocks.
  Context `{Types : VC_base}.
  
  (* Basic definitions (Section 2) *)
  Inductive operation :=
  | rd (t : tid) (x : var)
  | wr (t : tid) (x : var)
  | acq (t : tid) (m : lock)
  | rel (t : tid) (m : lock)
  | fork (t : tid) (u : tid)
  | join (t : tid) (u : tid)
  | exit (t : tid).

  Global Instance op_eq : EqDec_eq operation.
  Proof. eq_dec_inst. Qed.

  Definition trace := list operation.

  Definition thread_of a := match a with
  | rd t _ => t
  | wr t _ => t
  | acq t _ => t
  | rel t _ => t
  | fork t _ => t
  | join t _ => t
  | exit t => t
  end.

  Definition locks a m := exists t, a = acq t m \/ a = rel t m.
  Definition fjs a u := exists t, a = fork t u \/ a = join t u.
  Definition writes a x := exists t, a = wr t x.
  Definition accesses a x := exists t, a = rd t x \/ a = wr t x.
  Definition uses_thread a t := thread_of a = t \/ fjs a t.

  Inductive happens_before (tr : trace) i j : Prop := 
  | hb_prog_order a b (Hlt : i < j) (Ha : nth_error tr i = Some a)
      (Hb : nth_error tr j = Some b) (Hthread : thread_of a = thread_of b)
  | hb_locking a b (Hlt : i < j) (Ha : nth_error tr i = Some a)
      (Hb : nth_error tr j = Some b) m (Hlocka : locks a m) (Hlockb : locks b m)
  | hb_fork_join a b (Hlt : i < j) (Ha : nth_error tr i = Some a)
      (Hb : nth_error tr j = Some b)
      u (Hfj : fjs a u /\ thread_of b = u \/ fjs b u /\ thread_of a = u)
  | hb_trans k (Hhb1 : happens_before tr i k) (Hhb2 : happens_before tr k j).

  Lemma hb_app : forall m1 i j m2 (Hhb : happens_before m1 i j),
    happens_before (m1 ++ m2) i j.
  Proof.
    intros; induction Hhb.
    - generalize (nth_error_lt _ _ Ha), (nth_error_lt _ _ Hb); intros.
      eapply hb_prog_order; eauto; rewrite nth_error_app; clarify.
    - generalize (nth_error_lt _ _ Ha), (nth_error_lt _ _ Hb); intros.
      eapply hb_locking; try (rewrite nth_error_app; clarify); eauto.
    - generalize (nth_error_lt _ _ Ha), (nth_error_lt _ _ Hb); intros.
      eapply hb_fork_join; try (rewrite nth_error_app; clarify); eauto.
    - eapply hb_trans; eauto.
  Qed.

  Definition race_free (tr : trace) := forall i j (Hdiff : i <> j) a b 
    (Ha : nth_error tr i = Some a) (Hb : nth_error tr j = Some b)
    x (Hwrites : writes a x) (Haccesses : accesses b x),
    happens_before tr i j \/ happens_before tr j i.

  Definition vector_clock := tid -> nat.
  Definition vc_le (V1 V2 : vector_clock) := forall t, V1 t <= V2 t.
  Definition vc_join (V1 V2 : vector_clock) := fun t => max (V1 t) (V2 t).
  Definition vc_bot : vector_clock := fun t => 0.
  Definition vc_inc t (V : vector_clock) := 
    fun u => if eq_dec u t then S (V t) else V u.
  
  Definition state := ((tid -> vector_clock) * (lock -> vector_clock) *
    (var -> vector_clock) * (var -> vector_clock) * list tid)%type.
  Definition s0 : state := (fun t => vc_inc t vc_bot, fun m => vc_bot,
    fun x => vc_bot, fun x => vc_bot, []).

  Definition upd {A B} {A_eq : EqDec_eq A} (f : A -> B) x v y := 
    if eq_dec x y then v else f y.

  Inductive step : state -> operation -> state -> Prop :=
  | read_upd : forall C L R W X t x R' (Hlive : ~In t X)
     (HW : vc_le (W x) (C t)) (HR' : R' = upd R x (upd (R x) t (C t t))),
     step (C, L, R, W, X) (rd t x) (C, L, R', W, X)
  | write_upd : forall C L R W X t x W' (Hlive : ~In t X)
     (HW : vc_le (W x) (C t)) (HR : vc_le (R x) (C t))
     (HW' : W' = upd W x (upd (W x) t (C t t))),
     step (C, L, R, W, X) (wr t x) (C, L, R, W', X)
  | acquire : forall C L R W X t m C' (Hlive : ~In t X)
     (HC' : C' = upd C t (vc_join (C t) (L m))),
     step (C, L, R, W, X) (acq t m) (C', L, R, W, X)
  | release : forall C L R W X t m L' C' (Hlive : ~In t X)
      (HL' : L' = upd L m (C t)) (HC' : C' = upd C t (vc_inc t (C t))),
     step (C, L, R, W, X) (rel t m) (C', L', R, W, X)
  | fork_step : forall C L R W X t u C' (Hlive : ~In t X)
      (HC' : C' = upd (upd C u (vc_join (C u) (C t))) t (vc_inc t (C t))),
     step (C, L, R, W, X) (fork t u) (C', L, R, W, X)
  | join_step : forall C L R W X t u C' (Hlive : ~In t X) (Hdone : In u X)
      (HC' : C' = upd C t (vc_join (C t) (C u))),
     step (C, L, R, W, X) (join t u) (C', L, R, W, X)
  | exit_step : forall C L R W X t (Hlive : ~In t X),
     step (C, L, R, W, X) (exit t) (C, L, R, W, t :: X).

  Definition step_star := rtc step.

  (* Correctness *)

  (* Supporting definitions and lemmas *)
  Definition well_formed (s : state) := let '(C, L, R, W, X) := s in
    (forall u t, t <> u -> ~In t X -> C u t < C t t) /\
    (forall m t, ~In t X -> L m t < C t t) /\
    (forall x t, ~In t X -> R x t <= C t t) /\
    (forall x t, ~In t X -> W x t <= C t t).

  (* Lemma 1 *)
  Lemma wf0 : well_formed s0.
  Proof.
    unfold well_formed, s0; repeat split; intros; unfold vc_inc, vc_bot;
      clarify.
  Qed.

  Definition max_lt := Nat.max_lub_lt.

  Lemma lt_max_l : forall n m p, p < n -> p < max n m.
  Proof. intros; rewrite Nat.max_lt_iff; auto. Qed.

  Lemma lt_max_r : forall n m p, p < m -> p < max n m.
  Proof. intros; rewrite Nat.max_lt_iff; auto. Qed.

  Lemma le_max_l : forall n m p, p <= n -> p <= max n m.
  Proof. intros; etransitivity; eauto; apply Max.le_max_l. Qed.

  Lemma le_max_r : forall n m p, p <= m -> p <= max n m.
  Proof. intros; etransitivity; eauto; apply Max.le_max_r. Qed.

  Ltac join_solve := match goal with
    | [|- vc_join ?a ?b ?c < ?d] => unfold vc_join; apply max_lt; auto
    | [|- ?d < vc_join ?a ?b ?c] => unfold vc_join; first 
        [apply lt_max_l; auto | apply lt_max_r; auto]
    | [|- ?d <= vc_join ?a ?b ?c] => unfold vc_join; first 
        [apply le_max_l; auto | apply le_max_r; auto]
    | [|- context[vc_inc ?t ?V ?u]] => unfold vc_inc; destruct (eq_dec u t);
        clarify; solve [apply Lt.lt_S; auto]
    end.

  Lemma wf_preservation s s' a (Hwf : well_formed s) (Hstep : step s a s') : 
    well_formed s'.
  Proof.
    destruct s as ((((C, L), R), W), X); 
      destruct Hwf as [Hthreads [Hlocks [Hread Hwrite]]]; 
      inversion Hstep; clarify; unfold upd; repeat dec_eq;
      repeat split; intros; repeat dec_eq; repeat join_solve.
    apply Hthreads; auto; intro; clarify.
  Qed.

  Corollary step_star_wf s s' tr (Hwf : well_formed s) 
    (Hsteps : step_star s tr s') : well_formed s'.
  Proof.
    induction Hsteps; auto.
    apply IHHsteps; eapply wf_preservation; eauto.
  Qed.

  Definition clock_of (s : state) := match s with (C, _, _, _, _) => C end.
  Definition lock_of (s : state) := match s with (_, L, _, _, _) => L end.
  Definition read_of (s : state) := match s with (_, _, R, _, _) => R end.
  Definition write_of (s : state) := match s with (_, _, _, W, _) => W end.
  Definition exited_of (s : state) := match s with (_, _, _, _, X) => X end.

  Lemma clock_mono : forall s s' tr (Hsteps : step_star s tr s') u t,
    clock_of s u t <= clock_of s' u t.
  Proof.
    intros; induction Hsteps; auto.
    inversion Hstep; unfold upd, vc_inc, vc_join in *; clarify; dec_eq;
      try omega; eapply Max.max_lub_l; eauto.
  Qed.

  Lemma hb_cons : forall tr i j a, happens_before tr i j ->
    happens_before (a :: tr) (S i) (S j).
  Proof.
    intros; induction H; clarify.
    - eapply hb_prog_order; eauto.
    - eapply hb_locking; eauto.
    - eapply hb_fork_join; eauto.
    - eapply hb_trans; eauto.
  Qed.

  Lemma max_lt_l : forall i j, i < max i j -> max i j = j.
  Proof. intros; generalize (Max.max_spec i j); intros [? | ?]; omega. Qed.

  Lemma max_lt_r : forall i j, j < max i j -> max i j = i.
  Proof. intros; generalize (Max.max_spec i j); intros [? | ?]; omega. Qed.

  Inductive feasible tr := feasibleI
    (Hacq : forall i t m (Hi : nth_error tr i = Some (acq t m))
       j t' (Hlt : j < i) (Hj : nth_error tr j = Some (acq t' m)),
       exists k, j < k < i /\ nth_error tr k = Some (rel t' m))
    (Hrel : forall i t m (Hi : nth_error tr i = Some (rel t m)),
       exists j, j < i /\ nth_error tr j = Some (acq t m) /\
       forall k, j < k < i -> forall t', nth_error tr k <> Some (rel t' m))
    (Hfork : forall i t u (Hi : nth_error tr i = Some (fork t u)), t <> u /\
       forall j a (Hlt : j < i) (Hj : nth_error tr j = Some a),
       ~uses_thread a u)
    (Hexit : forall i t (Hi : nth_error tr i = Some (exit t))
       j a (Hlt : i < j) (Hj : nth_error tr j = Some a),
       uses_thread a t -> exists u, u <> t /\ a = join u t)
    (Hjoin : forall i t u (Hi : nth_error tr i = Some (join t u)),
       exists j, j < i /\ nth_error tr j = Some (exit u)).

  Lemma feasible_snoc : forall tr a, feasible (tr ++ [a]) -> feasible tr.
  Proof.
    intros; inversion H; constructor; intros; generalize (nth_error_lt _ _ Hi);
      try (generalize (nth_error_lt _ _ Hj)); intros.
    - specialize (Hacq i t m); rewrite nth_error_app in Hacq; clarify.
      specialize (Hacq j); rewrite nth_error_app in Hacq; clarify.
      specialize (Hacq _ Hlt Hj); destruct Hacq as [k ?]; exists k; clarify.
      rewrite nth_error_app in *; clarify; omega.
    - specialize (Hrel i t m); rewrite nth_error_app in Hrel; use Hrel;
        destruct Hrel as [j Hrel]; exists j; clarify.
      rewrite nth_error_app in *; destruct (lt_dec j (length tr));
        [clarify | exfalso; omega].
      specialize (Hrel22 k); rewrite nth_error_app in Hrel22; clarify; omega.
    - specialize (Hfork i t u); rewrite nth_error_app in Hfork; clarify.
      specialize (Hfork2 j); rewrite nth_error_app in Hfork2; clarify; omega.
    - specialize (Hexit i t); rewrite nth_error_app in Hexit; clarify.
      specialize (Hexit j a0); rewrite nth_error_app in Hexit; clarify.
    - specialize (Hjoin i t u); rewrite nth_error_app in Hjoin; clarify.
      rewrite nth_error_app in *; destruct (lt_dec x (length tr));
        [eauto | omega].
  Qed.

  Lemma lock_no_rel : forall s tr s' m (Hsteps : step_star s tr s')
    (Hno_rel : Forall (fun a => forall t, a <> rel t m) tr),
    lock_of s' m = lock_of s m.
  Proof.
    intros; induction Hsteps; clarify.
    inversion Hno_rel as [| ? ? Ha]; clarify.
    inversion Hstep; clarify.
    unfold upd in *; clarify.
    specialize (Ha t); clarify.
  Qed.

  Lemma feasible_le : forall s tr s' (Hsteps : step_star s tr s') m t t'
    (Hfeasible : feasible (tr ++ [rel t m])),
    lock_of s' m t' <= clock_of s' t t'.
  Proof.
    intros.
    inversion Hfeasible; clear Hfeasible Hacq Hfork Hjoin.
    specialize (Hrel (length tr)); rewrite nth_error_split in Hrel;
      specialize (Hrel _ _ eq_refl); destruct Hrel as [j Hj].
    rewrite nth_error_app in Hj; clarify.
    generalize (nth_error_split' _ _ Hj21); intros [l1 [l2 ?]]; clarify.
    generalize (rtc_app_inv _ _ Hsteps); intros [s'' Hs'']; clarify.
    inversion Hs''2 as [| ? ? ? ? Hacq Hsteps'']; clarify.
    generalize (clock_mono Hsteps'' t t'); clarify.
    etransitivity; [|eauto].
    inversion Hacq; unfold upd, vc_join, vc_inc in *; clarify.
    generalize (lock_no_rel(m := m) Hs''2); intro Heq; clarify; rewrite Heq.
    apply le_max_r; auto.
    { constructor; clarify.
      rewrite Forall_forall; intros ? Hin ?.
      generalize (in_nth_error _ _ Hin); intros [k Hk].
      specialize (Hj22 (length l1 + S k)); rewrite app_length in Hj22.
      use Hj22; [|omega].
      rewrite <- app_assoc, nth_error_app, lt_dec_plus_r, minus_plus in Hj22;
        clarify.
      specialize (Hj22 t0); rewrite nth_error_app, Hk2 in Hj22; intro; clarify.
    }
  Qed.

  Lemma hb_lt : forall m i j, happens_before m i j -> i < j.
  Proof.
    intros; induction H; clarify; omega.
  Qed.

  Definition hbe m i j := happens_before m i j \/ i = j.

  Lemma hbe_app : forall m1 i j m2, hbe m1 i j -> hbe (m1 ++ m2) i j.
  Proof. unfold hbe; clarify; left; apply hb_app; auto. Qed.

  Lemma hbe_trans : forall m i j k, hbe m i j -> hbe m j k ->
    hbe m i k.
  Proof. unfold hbe; clarify; left; eapply hb_trans; eauto. Qed.

  Lemma hb_hbe_trans : forall m i j k, happens_before m i j -> hbe m j k ->
    happens_before m i k.
  Proof. unfold hbe; clarify; eapply hb_trans; eauto. Qed.

  Lemma hbe_hb_trans : forall m i j k, hbe m i j -> happens_before m j k ->
    happens_before m i k.
  Proof. unfold hbe; clarify; eapply hb_trans; eauto. Qed.

  Lemma hb_suffix : forall l1 l2 i j (Hhb : happens_before (l1 ++ l2) i j)
    (Hgt : length l1 <= i), happens_before l2 (i - length l1) (j - length l1).
  Proof.
    intros.
    generalize (hb_lt Hhb); intro.
    destruct (lt_dec i (length l1)); [omega|].
    destruct (lt_dec j (length l1)); [omega|].
    induction Hhb; try (rewrite nth_error_app in *); clarify.
    - eapply hb_prog_order; eauto; omega.
    - eapply hb_locking; eauto; omega.
    - eapply hb_fork_join; eauto; omega.
    - generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
      eapply hb_trans; [apply IHHhb1 | apply IHHhb2]; omega.
  Qed.
  
  Lemma fork_join_hb : forall tr (Hfeasible : feasible tr) i j t t' u
    (Hlt : i < j) (Hi : nth_error tr i = Some (fork t u))
    (Hj : nth_error tr j = Some (join t' u)), happens_before tr i j.
  Proof.
    intros; inversion Hfeasible.
    exploit Hjoin; eauto; intros (k & ? & Hk).
    apply hb_trans with (k := k).
    - destruct (lt_dec i k).
      + eapply hb_fork_join; eauto.
        left; unfold fjs; clarify; eauto.
      + destruct (eq_dec i k); clarsimp.
        specialize (Hexit _ _ Hk i); exploit Hexit; eauto.
        * omega.
        * unfold uses_thread, fjs; eauto.
        * clarify.
    - eapply hb_fork_join; eauto.
      right; unfold fjs; clarify; eauto.
  Qed.

  Definition writes_thread a t := thread_of a = t \/ exists u, a = fork u t.

  Corollary write_use_hb : forall tr (Hfeasible : feasible tr) i j a b
    (Hlt : i < j) (Hi : nth_error tr i = Some a) (Hj : nth_error tr j = Some b)
    t (Ha : writes_thread a t) (Hb : uses_thread b t), happens_before tr i j.
  Proof.
    intros; destruct Ha, Hb as [? | Hfj].
    - eapply hb_prog_order; eauto; clarify.
    - eapply hb_fork_join; eauto.
    - clarify; eapply hb_fork_join; eauto.
      left; clarify; unfold fjs; eauto.
    - destruct Hfj as [t' [? | ?]]; clarify.
      + inversion Hfeasible.
        specialize (Hfork _ _ _ Hj); clarify.
        exploit Hfork2; eauto; unfold uses_thread, fjs; clarify; eauto.
      + eapply fork_join_hb; eauto.
  Qed.

  Corollary write_use_hb' : forall tr0 tr (Hfeasible : feasible (tr0 ++ tr))
    i j a b
    (Hlt : i < j) (Hi : nth_error tr i = Some a) (Hj : nth_error tr j = Some b)
    t (Ha : writes_thread a t) (Hb : uses_thread b t), happens_before tr i j.
  Proof.
    intros.
    apply (plus_lt_compat_l _ _ (length tr0)) in Hlt; exploit write_use_hb;
      eauto.
    - rewrite nth_error_app, lt_dec_plus_r, minus_plus; auto.
    - rewrite nth_error_app, lt_dec_plus_r, minus_plus; auto.
    - intro; exploit hb_suffix; eauto; [omega|].
      do 2 rewrite minus_plus; auto.
  Qed.

  (* Soundness *)
  Lemma clocks_hb_core : forall tr0 tr (Hfeasible : feasible (tr0 ++ tr))
    s (Hwf : well_formed s) s' (Hsteps : step_star s tr s')
    t (Hlive : ~In t (exited_of s)),
    (forall u, u <> t -> clock_of s t t <= clock_of s' u t ->
       exists i j e d, nth_error tr i = Some e /\ nth_error tr j = Some d /\
       writes_thread d u /\ uses_thread e t /\ hbe tr i j) /\
    (forall m, clock_of s t t <= lock_of s' m t ->
       exists i j e d, nth_error tr i = Some e /\ nth_error tr j = Some d /\
       locks d m /\ uses_thread e t /\ hbe tr i j).
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; clarify.
      destruct s' as ((((?, ?), ?), ?), ?); destruct Hwf as [Hclock [Hlock _]].
      split; clarify.
      - specialize (Hclock u t); clarify; omega.
      - specialize (Hlock m t); clarify; omega. }
    generalize (rtc_snoc_inv _ _ Hsteps); intros [s'' [Htr Hx]].
    rewrite app_assoc in Hfeasible; exploit feasible_snoc; eauto; clarify.
    rewrite <- app_assoc in Hfeasible.
    specialize (IHtr _ Hwf _ Htr t).
    generalize (step_star_wf Hwf Htr); intro Hwf'.
    split; [intros ? Ht Hclock | intros ? Hlock]; clarify.
    - destruct (le_dec (clock_of s t t) (clock_of s'' u t)).
      { specialize (IHtr1 _ Ht); use IHtr1;
          destruct IHtr1 as (i & j & ? & ? & Hi & Hj & ?); exists i, j; clarify.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        repeat rewrite nth_error_app; clarify; repeat eexists; eauto.
        apply hbe_app; auto. }
      inversion Hx; clarify; unfold upd, vc_join, vc_inc in Hclock; clarify.
      + generalize (Max.max_spec (C u t) (L m t)); intros [[? Hmax] | [? Hmax]];
          rewrite Hmax in *; try omega.
        specialize (IHtr2 _ Hclock).
        destruct IHtr2 as (i & j & ? & ? & Hi & Hj & ?).
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        exists i, (length tr); rewrite nth_error_split; rewrite nth_error_app;
          unfold writes_thread, uses_thread; clarify; repeat eexists; eauto.
        eapply hbe_trans; [apply hbe_app; eauto|].
        left; eapply hb_locking; unfold locks; try (rewrite nth_error_split);
          try (rewrite nth_error_app); clarify; eauto.
      + destruct (eq_dec t0 u); clarify.
        generalize (Max.max_spec (C u t) (C t0 t));
          intros [[? Hmax] | [? Hmax]]; rewrite Hmax in *; try omega.
        destruct (eq_dec t0 t); subst.
        { exists (length tr), (length tr); rewrite nth_error_split;
            repeat eexists; eauto.
          * unfold writes_thread; eauto.
          * unfold uses_thread; auto.
          * unfold hbe; auto. }
        specialize (IHtr1 _ n1); use IHtr1.
        destruct IHtr1 as (i & j & ? & ? & Hi & Hj & Huse & ?); clarify.
        exists i, (length tr); rewrite nth_error_split.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        rewrite nth_error_app; clarify; repeat eexists; eauto.
        * unfold writes_thread; eauto.
        * eapply hbe_trans; [apply hbe_app; eauto|].
          left; eapply write_use_hb'; try (rewrite nth_error_split);
            try (rewrite nth_error_app); unfold uses_thread; clarify; eauto.
      + destruct (eq_dec u0 u); clarify.
        generalize (Max.max_spec (C u t) (C u0 t));
          intros [[? Hmax] | [? Hmax]]; rewrite Hmax in *; try omega.
        destruct (eq_dec u0 t); subst.
        { exists (length tr), (length tr); rewrite nth_error_split;
            repeat eexists; eauto.
          * unfold writes_thread; auto.
          * unfold uses_thread, fjs; eauto.
          * unfold hbe; auto. }
        specialize (IHtr1 _ n1); use IHtr1.
        destruct IHtr1 as (i & j & ? & ? & Hi & Hj & Huse & ?); clarify.
        exists i, (length tr); rewrite nth_error_split.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        rewrite nth_error_app; clarify; repeat eexists; eauto.
        * unfold writes_thread; auto.
        * eapply hbe_trans; [apply hbe_app; eauto|].
          left; eapply write_use_hb'; try (rewrite nth_error_split);
            try (rewrite nth_error_app); clarify; eauto.
          unfold uses_thread, fjs; eauto. 
    - destruct (le_dec (clock_of s t t) (lock_of s'' m t)).
      { specialize (IHtr2 m); use IHtr2;
          destruct IHtr2 as (i & j & ? & ? & Hi & Hj & ?); exists i, j; clarify.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        unfold locks in *; clarify.
        repeat rewrite nth_error_app; clarify; repeat eexists; eauto.
        apply hbe_app; auto. }
      inversion Hx; clarify; unfold upd, vc_join, vc_inc in Hlock; clarify.
      destruct (eq_dec t0 t); subst.
      + exists (length tr), (length tr); rewrite nth_error_split;
          repeat eexists; eauto.
        * unfold uses_thread; auto.
        * unfold hbe; auto.
      + specialize (IHtr1 _ n0); use IHtr1.
        destruct IHtr1 as (i & j & ? & ? & Hi & Hj & ?); clarify.
        exists i, (length tr); rewrite nth_error_split.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        rewrite nth_error_app; clarify; repeat eexists; eauto.
        eapply hbe_trans; [apply hbe_app; eauto|].
        left; eapply write_use_hb'; try (rewrite nth_error_split);
          try (rewrite nth_error_app); unfold uses_thread; clarify; eauto.
  Qed.

  Lemma clocks_hb sa a tr sb b : forall
    tr0 (Hfeasible : feasible (tr0 ++ a :: tr ++ [b])) 
    (Hwf : well_formed sa) (Hsteps : step_star sa (a :: tr) sb)
    t (Ht : t = thread_of a) u (Hu : u = thread_of b)
    (Hlive : ~In t (exited_of sa))
    (Hclock_lt : clock_of sa t t <= clock_of sb u t),
    happens_before (a :: tr ++ [b]) 0 (S (length tr)).
  Proof.
    intros.
    destruct (eq_dec u t).
    - subst; symmetry in e; eapply hb_prog_order; eauto; clarify.
      apply nth_error_split.
    - generalize (feasible_snoc (tr0 ++ a :: tr) b); intro Hfeasible';
        use Hfeasible'; [|clarsimp].
      generalize (clocks_hb_core _ Hfeasible' Hwf Hsteps t Hlive);
        intros [Hhb _].
      specialize (Hhb _ n Hclock_lt).
      destruct Hhb as (i & j & e & d & Hi & Hj & ?); clarify.
      generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
      eapply hbe_hb_trans; [|eapply hbe_hb_trans].
      + unfold hbe; destruct (eq_dec 0 i); eauto.
        left; eapply write_use_hb'; clarify; eauto.
        * omega.
        * destruct i; clarify; rewrite nth_error_app; clarify; omega.
        * unfold writes_thread; auto.
      + assert (hbe ((a :: tr) ++ [b]) i j) by (apply hbe_app; auto);
          clarify; eauto.
      + eapply write_use_hb'; eauto.
        * destruct j; clarify.
          rewrite <- Nat.succ_lt_mono, nth_error_app in *; clarify.
        * apply nth_error_split.
        * unfold uses_thread; auto.
  Qed.

  Lemma hb_app' : forall m2 i j m1, happens_before m2 i j ->
    happens_before (m1 ++ m2) (length m1 + i) (length m1 + j).
  Proof.
    intros; induction H.
    - eapply hb_prog_order; eauto; try omega; rewrite nth_error_app,
        lt_dec_plus_r, minus_plus; auto.
    - eapply hb_locking; try omega; try (rewrite nth_error_app,
        lt_dec_plus_r, minus_plus); eauto.
    - eapply hb_fork_join; try omega; try (rewrite nth_error_app,
        lt_dec_plus_r, minus_plus); eauto.
    - eapply hb_trans; eauto.
  Qed.

  Lemma feasible_app : forall tr tr2 (Hfeasible : feasible (tr ++ tr2)),
    feasible tr.
  Proof.
    induction tr2 using rev_ind; clarsimp.
    rewrite app_assoc in Hfeasible; exploit feasible_snoc; eauto.
  Qed.

  Lemma clocks_hb' tr1 sa a tr2 sb b tr3 : forall
    (Hfeasible : feasible (tr1 ++ a :: tr2 ++ b :: tr3))
    (Hwf : well_formed sa) (Hsteps : step_star sa (a :: tr2) sb)
    t (Ht : t = thread_of a) u (Hu : u = thread_of b)
    (Hlive : ~In t (exited_of sa))
    (Hclock_lt : clock_of sa t t <= clock_of sb u t),
    happens_before (tr1 ++ a :: tr2 ++ b :: tr3)
                   (length tr1) (length tr1 + S (length tr2)).
  Proof.
    intros.
    generalize (feasible_app (tr1 ++ a :: tr2 ++ [b]) tr3); intro Hfeasible';
      use Hfeasible'; [|clarsimp].
    generalize (clocks_hb _ _ Hfeasible' Hwf Hsteps Ht Hu Hlive Hclock_lt);
      intro Hhb.
    generalize (hb_app tr3 (hb_app' tr1 Hhb)); clarsimp.
  Qed.

  Definition race_free' (tr : trace) := forall i j (Hdiff : i < j) a b 
    (Ha : nth_error tr i = Some a) (Hb : nth_error tr j = Some b)
    x (Hwrites : writes a x \/ writes b x) 
    (Haccesses : accesses a x /\ accesses b x),
    happens_before tr i j.

  Lemma writes_accesses : forall a x, writes a x -> accesses a x.
  Proof.
    unfold writes, accesses; clarify; eauto.
  Qed.

  Lemma race_free_alt tr : race_free tr <-> race_free' tr.
  Proof.
    split; repeat intro.
    - destruct Hwrites as [Hwrites | Hwrites].
      + destruct (eq_dec i j); [omega|].
        specialize (H _ _ n _ _ Ha Hb _ Hwrites); clarify.
        generalize (hb_lt H); omega.
      + destruct (eq_dec j i); [omega|].
        specialize (H _ _ n _ _ Hb Ha _ Hwrites); clarify.
        generalize (hb_lt H); omega.
    - destruct (lt_dec i j).
      + specialize (H _ _ l _ _ Ha Hb x); clarify.
        generalize (writes_accesses Hwrites); clarify.
      + assert (j < i) as Hlt by omega.
        specialize (H _ _ Hlt _ _ Hb Ha x); clarify.
        generalize (writes_accesses Hwrites); clarify.
  Qed.

  Definition writesb a x := match a with wr _ y => beq x y | _ => false end.

  Opaque minus.

  Definition last_write tr x := find_index (fun a => writesb a x) (rev tr).

  Lemma write_own' : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hwrite : write_of s x t = clock_of s t t) (Hlive : ~In t (exited_of s)),
    vc_le (write_of s x) (clock_of s t) /\ vc_le (read_of s x) (clock_of s t).
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; split; intro; clarify. }
    generalize (rtc_snoc_inv _ _ Hsteps); intros [s' [Htr Hs']].
    generalize (step_star_wf wf0 Htr); intro Hwf.
    specialize (IHtr _ x0 t Htr).
    inversion Hs'; clarify.
    - unfold upd in *; clarify.
      intro; clarify.
      destruct (eq_dec t1 t); clarify.
      specialize (HW t); specialize (Hwf1 t1 t); clarify; omega.
    - unfold upd in *; clarify.
      destruct (eq_dec t0 t); [split; intro|]; clarify.
      specialize (HW t); specialize (Hwf1 t0 t); clarify; omega.
    - unfold upd in *; clarify.
      unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
      split; intro; join_solve.
      { specialize (Hwf21 m t); clarify; omega. }
    - unfold upd, vc_inc in *; clarify.
      specialize (Hwf222 x0 t); clarify; omega.
    - unfold upd, vc_inc in *; clarify.
      destruct (eq_dec t0 t); clarify.
      + specialize (Hwf222 x0 t); clarify; omega.
      + unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
        split; intro; join_solve.
        { specialize (Hwf1 t0 t); clarify; omega. }
    - unfold upd in *; clarify.
      unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
      split; intro; join_solve.
      { destruct (eq_dec u t); clarify.
        specialize (Hwf1 u t); clarify; omega. }
  Qed.

  Corollary write_own : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hwrite : write_of s x t = clock_of s t t) (Hlive : ~In t (exited_of s)),
    vc_le (write_of s x) (clock_of s t).
  Proof. apply write_own'. Qed.

  Lemma write_mono : forall s tr s' x (Hsteps : step_star s tr s'),
    vc_le (write_of s x) (write_of s' x).
  Proof.
    intros; induction Hsteps; intro; clarify.
    etransitivity; [|eapply IHHsteps].
    inversion Hstep; clarify.
    unfold upd; clarify.
  Qed.

  Lemma read_mono : forall s tr s' x (Hsteps : step_star s tr s')
    (Hwf : well_formed s), vc_le (read_of s x) (read_of s' x).
  Proof.
    intros; induction Hsteps; intro; clarify.
    generalize (wf_preservation Hwf Hstep); intro.
    etransitivity; [|apply IHHsteps; auto].
    inversion Hstep; clarify.
    unfold upd; clarify.
  Qed.

  Lemma write_result : forall s t x s' (Hstep : step s (wr t x) s'),
    write_of s' x t = clock_of s t t /\ clock_of s' t = clock_of s t.
  Proof.
    intros; inversion Hstep; unfold upd in *; clarify.
  Qed.

  Lemma write_after_write : forall tr s i j x t u (Hfeasible : feasible tr)
    (Hsteps : step_star s0 tr s) (Hlt : i < j)
    (Hi : nth_error tr i = Some (wr t x)) (Hj : nth_error tr j = Some (wr u x)),
     happens_before tr i j.
  Proof.
    intros.
    assert (tr = firstn i tr ++ wr t x :: firstn (j - S i) (skipn (S i) tr) ++
      wr u x :: skipn (S j) tr) as Htr.
    { rewrite <- (firstn_skipn i tr) at 1; erewrite skipn_n; eauto.
      rewrite <- (firstn_skipn (j - S i) (skipn (S i) tr)) at 1.
      rewrite skipn_skipn, le_plus_minus_r; [|auto].
      erewrite (skipn_n j); eauto. }
    generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
    assert (i = length (firstn i tr)) as Hi'.
    { rewrite List.firstn_length, Min.min_l; auto; omega. }
    assert (j = length (firstn i tr) + S (length (firstn (j - S i)
      (skipn (S i) tr)))) as Hj'.
    { repeat rewrite List.firstn_length; rewrite skipn_length.
      repeat rewrite Min.min_l; omega. }
    rewrite Hi', Hj'; rewrite Htr at 1; clear Hi' Hj'.
    rewrite Htr in Hsteps, Hfeasible; clear Htr.
    generalize (rtc_app_inv _ _ Hsteps); intros (? & ? & Hsteps').
    rewrite app_comm_cons in Hsteps'; generalize (rtc_app_inv _ _ Hsteps');
      intros (? & Hstepsi & Hstepsj).
    eapply clocks_hb'; eauto.
    { eapply step_star_wf; eauto; apply wf0. }
    { inversion Hstepsi; clarify.
      inversion Hstep; auto. }
    inversion Hstepsi as [|? ? ? ? Hstepi Htr2]; clarify.
    inversion Hstepsj as [|? ? ? ? Hstepj ?]; clarify.
    generalize (write_result Hstepi), (write_result Hstepj);
      intros [Hwi Hci] [Hwj Hcj].
    rewrite <- Hcj in *; etransitivity; [|eapply write_own; eauto].
    generalize (rtc_snoc _ _ Htr2 Hstepj); intro.
    etransitivity; [|eapply write_mono; eauto]; clarsimp.
    { eapply rtc_snoc; [|eauto].
      eapply rtc_trans; eauto. }
    { inversion Hstepj; auto. }
  Qed.

  Lemma read_own : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hwrite : read_of s x t = clock_of s t t) (Hlive : ~In t (exited_of s)),
    vc_le (write_of s x) (clock_of s t).
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; intro; clarify. }
    generalize (rtc_snoc_inv _ _ Hsteps); intros [s' [Htr Hs']].
    generalize (step_star_wf wf0 Htr); intro Hwf.
    specialize (IHtr _ x0 t Htr).
    inversion Hs'; clarify.
    - unfold upd in *; clarify.
    - unfold upd in *; clarify.
      intro; clarify.
      destruct (eq_dec t t1); clarify.
      specialize (HR t); specialize (Hwf1 t1 t); clarify; omega.
    - unfold upd in *; clarify.
      unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
      intro; join_solve.
      { specialize (Hwf21 m t); clarify; omega. }
    - unfold upd, vc_inc in *; clarify.
      specialize (Hwf221 x0 t); clarify; omega.
    - unfold upd, vc_inc in *; clarify.
      destruct (eq_dec t0 t); clarify.
      + specialize (Hwf221 x0 t); clarify; omega.
      + unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
        intro; join_solve.
        { specialize (Hwf1 t0 t); clarify; omega. }
    - unfold upd in *; clarify.
      unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
      intro; join_solve.
      { destruct (eq_dec u t); clarify.
        specialize (Hwf1 u t); clarify; omega. }
  Qed.
  
  Lemma read_result : forall s t x s' (Hstep : step s (rd t x) s'),
    read_of s' x t = clock_of s t t /\ clock_of s' t = clock_of s t.
  Proof.
    intros; inversion Hstep; unfold upd in *; clarify.
  Qed.

  Lemma read_after_write : forall tr s i j x t u (Hfeasible : feasible tr)
    (Hsteps : step_star s0 tr s) (Hlt : i < j)
    (Hi : nth_error tr i = Some (wr t x)) (Hj : nth_error tr j = Some (rd u x)),
    happens_before tr i j.
  Proof.
    intros.
    assert (tr = firstn i tr ++ wr t x :: firstn (j - S i) (skipn (S i) tr) ++
      rd u x :: skipn (S j) tr) as Htr.
    { rewrite <- (firstn_skipn i tr) at 1; erewrite skipn_n; eauto.
      rewrite <- (firstn_skipn (j - S i) (skipn (S i) tr)) at 1.
      rewrite skipn_skipn, le_plus_minus_r; [|auto].
      erewrite (skipn_n j); eauto. }
    generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
    assert (i = length (firstn i tr)) as Hi'.
    { rewrite List.firstn_length, Min.min_l; auto; omega. }
    assert (j = length (firstn i tr) + S (length (firstn (j - S i)
      (skipn (S i) tr)))) as Hj'.
    { repeat rewrite List.firstn_length; rewrite skipn_length.
      repeat rewrite Min.min_l; omega. }
    rewrite Hi', Hj'; rewrite Htr at 1; clear Hi' Hj'.
    rewrite Htr in Hsteps, Hfeasible; clear Htr.
    generalize (rtc_app_inv _ _ Hsteps); intros (? & ? & Hsteps').
    rewrite app_comm_cons in Hsteps'; generalize (rtc_app_inv _ _ Hsteps');
      intros (? & Hstepsi & Hstepsj).
    eapply clocks_hb'; eauto.
    { eapply step_star_wf; eauto; apply wf0. }
    { inversion Hstepsi; clarify.
      inversion Hstep; auto. }
    inversion Hstepsi as [|? ? ? ? Hstepi Htr2]; clarify.
    inversion Hstepsj as [|? ? ? ? Hstepj ?]; clarify.
    generalize (write_result Hstepi), (read_result Hstepj);
      intros [Hwi Hci] [Hwj Hcj].
    rewrite <- Hcj in *; etransitivity; [|eapply read_own; eauto].
    generalize (rtc_snoc _ _ Htr2 Hstepj); intro.
    etransitivity; [|eapply write_mono; eauto]; clarsimp.
    { eapply rtc_snoc; [|eauto].
      eapply rtc_trans; eauto. }
    { inversion Hstepj; auto. }
  Qed.

  Lemma write_after_read : forall tr s i j x t u (Hfeasible : feasible tr)
    (Hsteps : step_star s0 tr s) (Hlt : i < j)
    (Hi : nth_error tr i = Some (rd t x)) (Hj : nth_error tr j = Some (wr u x)),
    happens_before tr i j.
  Proof.
    intros.
    assert (tr = firstn i tr ++ rd t x :: firstn (j - S i) (skipn (S i) tr) ++
      wr u x :: skipn (S j) tr) as Htr.
    { rewrite <- (firstn_skipn i tr) at 1; erewrite skipn_n; eauto.
      rewrite <- (firstn_skipn (j - S i) (skipn (S i) tr)) at 1.
      rewrite skipn_skipn, le_plus_minus_r; [|auto].
      erewrite (skipn_n j); eauto. }
    generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
    assert (i = length (firstn i tr)) as Hi'.
    { rewrite List.firstn_length, Min.min_l; auto; omega. }
    assert (j = length (firstn i tr) + S (length (firstn (j - S i)
      (skipn (S i) tr)))) as Hj'.
    { repeat rewrite List.firstn_length; rewrite skipn_length.
      repeat rewrite Min.min_l; omega. }
    rewrite Hi', Hj'; rewrite Htr at 1; clear Hi' Hj'.
    rewrite Htr in Hsteps, Hfeasible; clear Htr.
    generalize (rtc_app_inv _ _ Hsteps); intros (? & ? & Hsteps').
    rewrite app_comm_cons in Hsteps'; generalize (rtc_app_inv _ _ Hsteps');
      intros (? & Hstepsi & Hstepsj).
    eapply clocks_hb'; eauto.
    { eapply step_star_wf; eauto; apply wf0. }
    { inversion Hstepsi; clarify.
      inversion Hstep; auto. }
    inversion Hstepsi as [|? ? ? ? Hstepi Htr2]; clarify.
    inversion Hstepsj as [|? ? ? ? Hstepj ?]; clarify.
    generalize (read_result Hstepi), (write_result Hstepj);
      intros [Hwi Hci] [Hwj Hcj].
    rewrite <- Hcj in *; etransitivity; [|eapply write_own'; eauto].
    generalize (rtc_snoc _ _ Htr2 Hstepj); intro.
    etransitivity; [|eapply read_mono; eauto]; clarsimp.
    { eapply (step_star_wf wf0).
      eapply rtc_snoc; eauto. }
    { eapply rtc_snoc; [|eauto].
      eapply rtc_trans; eauto. }
    { inversion Hstepj; auto. }
  Qed.

  Theorem Soundness tr : feasible tr -> forall s', step_star s0 tr s' ->
    race_free tr.
  Proof.
    intros; rewrite race_free_alt; repeat intro; clarify.
    unfold writes in *; destruct Haccesses1 as [t [H1 | H1]],
      Haccesses2 as [u [H2 | H2]]; clarify.
    - eapply write_after_read; eauto.
    - eapply read_after_write; eauto.
    - eapply write_after_write; eauto.
  Qed.

  (* Completeness *)
  Definition K a s := match a with
  | join t u => let C := clock_of s in
      upd C t (vc_join (C t) (C u))
  | acq t m => let C := clock_of s in let L := lock_of s in
      upd C t (vc_join (C t) (L m))
  | _ => clock_of s
  end.

  Lemma K_lower : forall a s t t', clock_of s t t' <= K a s t t'.
  Proof.
    intros; destruct a; clarify; unfold upd, vc_join, vc_inc; clarify.
    - apply Max.le_max_l.
    - apply Max.le_max_l.
  Qed.

  Lemma K_upper : forall a s s' (Hstep : step s a s') t t',
    K a s t t' <= clock_of s' t t'.
  Proof.
    intros.
    generalize (clock_mono (ss_step _ _ Hstep (ss_refl _ _)) t t'); intro.
    destruct a; clarify; inversion Hstep; clarify.
  Qed.

  Lemma acq_rel_clock : forall s t m tr s'
    (Hsteps : step_star s (acq t m :: tr ++ [rel t m]) s'),
    vc_le (clock_of s t) (lock_of s' m).
  Proof.
    intros.
    inversion Hsteps as [|? ? ? ? Ha Htr]; clarify.
    inversion Ha; clarify.
    generalize (rtc_snoc_inv _ _ Htr); intros [s'' [Htr' Hx]].
    inversion Hx; clarify.
    unfold upd; clarify.
    generalize (ss_step _ _ Ha Htr'); intro Hsteps'.
    generalize (clock_mono Hsteps'); unfold vc_le; auto.
  Qed.

  Lemma lock_mono : forall s tr s' tr' s'' (Hsteps : step_star s tr s')
    (Hsteps' : step_star s' tr' s'') m t (Hfeasible : feasible (tr ++ tr')),
    lock_of s' m t <= lock_of s'' m t.
  Proof.
    induction tr' using rev_ind; clarify.
    { inversion Hsteps'; clarify. }
    generalize (rtc_snoc_inv _ _ Hsteps'); intros [sx [Htr' Hx]].
    specialize (IHtr' _ Hsteps Htr' m t).
    rewrite app_assoc in Hfeasible; generalize (feasible_snoc _ _ Hfeasible);
      clarify.
    inversion Hx; unfold upd, vc_inc, vc_join in *; clarify.
    generalize (rtc_trans Hsteps Htr'); intro Htr.
    generalize (feasible_le Htr m t0 t Hfeasible); clarify; omega.
  Qed.

  Lemma fork_irrefl : forall tr i t (Hfeasible : feasible tr),
    nth_error tr i <> Some (fork t t).
  Proof.
    repeat intro; inversion Hfeasible.
    exploit Hfork; eauto; clarify.
  Qed.

  Lemma join_irrefl : forall tr i t (Hfeasible : feasible tr),
    nth_error tr i <> Some (join t t).
  Proof.
    repeat intro; inversion Hfeasible.
    specialize (Hjoin _ _ _ H); clarify.
    specialize (Hexit _ _ Hjoin2 _ _ Hjoin1 H); unfold uses_thread in Hexit;
      clarify.
    inversion Hexit2; clarify.
  Qed.

  (* Note that this formulation specifically does *not* require that b be able
     to take a step. This is vital for use in the completeness theorem. *)
  Lemma hb_clocks : forall s tr1 sa (Hsteps1 : step_star s tr1 sa)
    a sa' (Hstepa : step sa a sa') tr2 sb (Hsteps2 : step_star sa' tr2 sb)
    b t (Ht : t = thread_of a) u (Hu : u = thread_of b) tr3
    (Hhb : happens_before (tr1 ++ a :: tr2 ++ b :: tr3) (length tr1) 
             (length tr1 + S (length tr2)))
    (Hfeasible : feasible (tr1 ++ a :: tr2 ++ b :: tr3)),
    vc_le (K a sa t) (K b sb u).
  Proof.
    repeat intro.
    destruct (eq_dec t u).
    { rewrite e; etransitivity; [apply K_upper; eauto|].
      etransitivity; [|apply K_lower].
      eapply clock_mono; eauto. }
    remember (length tr1 + S (length tr2)) as j; remember (length tr1) as i;
      remember (tr1 ++ a :: tr2 ++ b :: tr3) as tr.
    generalize dependent tr1; generalize dependent tr2;
      generalize dependent tr3; generalize dependent a; generalize dependent b;
      generalize dependent u; revert sa sa' sb t.
    induction Hhb; clarify.
    - rewrite nth_error_split in Ha; clarify.
      rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hb; clarify.
      rewrite nth_error_split in Hb; clarify.
    - rewrite nth_error_split in Ha; clarify.
      rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hb; clarify.
      rewrite nth_error_split in Hb; clarify.
      (* Consider: given feasible, this reduces to the case in which
         a releases and b acquires. *)
      destruct Hlocka as [t Hlocka], Hlockb as [u Hlockb].
      assert (exists l1 sr sr' l2 sc l3, a :: tr2 ++ [b] = l1 ++ rel t m :: l2
        ++ acq u m :: l3 /\ step_star sa l1 sr /\ step sr (rel t m) sr' /\
        step_star sr' l2 sc /\
        (l3 = [] /\ sc = sb \/ step_star sc (acq u m :: removelast l3) sb))
        as (l1 & sr & sr' & l2 & sc & l3 & Hra).
      { inversion Hfeasible; clear Hfork Hjoin.
        destruct Hlockb; clarify.
        + destruct Hlocka; clarify.
          * specialize (Hacq (length tr1 + S (length tr2))).
            rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hacq;
              simpl in Hacq; rewrite nth_error_split in Hacq.
            specialize (Hacq _ _ eq_refl (length tr1) t);
              rewrite nth_error_split in Hacq; use Hacq; use Hacq.
            destruct Hacq as [k Hk]; clarify.
            rewrite nth_error_app in Hk2; destruct (lt_dec k (length tr1));
              [omega|].
            destruct (k - length tr1) eqn: Hminus; clarify.
            rewrite nth_error_app in Hk2; destruct (lt_dec n1 (length tr2));
              [|omega].
            generalize (nth_error_split' _ _ Hk2); intros [l1 [l2 ?]];
              clarify.
            generalize (rtc_app_inv _ _ Hsteps2); intros [sr [? Hsr]].
            inversion Hsr; clarify.
            exists (acq t m :: l1), sr, s', l2, sb, []; clarsimp.
            econstructor; eauto.
          * exists [], sa, sa', tr2, sb, []; clarify; apply ss_refl.
        + specialize (Hrel (length tr1 + S (length tr2))).
          rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hrel;
            simpl in Hrel; rewrite nth_error_split in Hrel;
            specialize (Hrel _ _ eq_refl).
          destruct Hrel as [j Hj]; clarify.
          destruct Hlocka; clarify.
          * destruct (lt_dec j (length tr1)).
            { specialize (Hacq (length tr1)); rewrite nth_error_split in Hacq.
              specialize (Hacq _ _ eq_refl j u); clarify.
              specialize (Hj22 x); use Hj22; [|omega].
              specialize (Hj22 u); clarify. }
            specialize (Hacq _ _ _ Hj21 (length tr1) t).
            rewrite nth_error_app in Hj21; clarify.
            use Hacq; [|destruct (eq_dec j (length tr1)); clarsimp; omega].
            rewrite nth_error_split in Hacq; use Hacq.
            destruct Hacq as [k Hk]; clarify.
            rewrite nth_error_app in Hk2; destruct (lt_dec k (length tr1));
              [omega|].
            destruct (j - length tr1) as [|j'] eqn: Hminus; clarify.
            destruct (k - length tr1) as [|k'] eqn: Hminus'; clarify.
            rewrite nth_error_app in Hj21; destruct (lt_dec j' (length tr2));
              [|omega].
            generalize (nth_error_split' _ _ Hj21); intros [l0 [l3 ?]];
              clarify.
            rewrite <- app_assoc in Hk2; rewrite nth_error_app in Hk2;
              destruct (lt_dec k' (length l0)); [|omega].
            generalize (nth_error_split' _ _ Hk2); intros [l01 [l2 ?]]; clarify.
            generalize (rtc_app_inv _ _ Hsteps2); intros [sc [Hsc ?]].
            generalize (rtc_app_inv _ _ Hsc); intros [sr [? Hsr]].
            inversion Hsr; clarify.
            exists (acq t m :: l01), sr, s', l2, sc, (l3 ++ [rel u m]);
              clarsimp.
            split; [econstructor; eauto | clarify].
            rewrite removelast_snoc; auto.
          * rewrite nth_error_app in Hj21; destruct (lt_dec j (length tr1)).
            { specialize (Hj22 (length tr1)); clarify.
              rewrite nth_error_split in Hj22; specialize (Hj22 t); clarify. }
            destruct (j - length tr1) eqn: Hminus; clarify.
            rewrite nth_error_app in Hj21; destruct (lt_dec n1 (length tr2));
              [|omega].
            generalize (nth_error_split' _ _ Hj21); intros [l2 [l3 ?]];
              clarify.
            generalize (rtc_app_inv _ _ Hsteps2); intros [sc [? Hsc]].
            exists [], sa, sa', l2, sc, (l3 ++ [rel u m]); clarsimp.
            split; [apply ss_refl | clarify].
            rewrite removelast_snoc; auto. }
      transitivity (K (rel t m) sr t t0); [|transitivity (K (acq u m) sc u t0)].
      + destruct Hlocka; clarify.
        * destruct l1; clarify.
          inversion Hra21 as [|? ? ? ? Ha Hl1]; clarify.
          generalize (clock_mono Hl1 t t0); inversion Ha; clarify.
        * eapply clock_mono; eauto.
      + simpl; unfold upd, vc_join; clarify.
        generalize (rtc_snoc _ _ Hra21 Hra221); intro Hsteps.
        generalize (rtc_trans Hsteps1 Hsteps); intro Hsteps'.
        generalize (lock_mono Hsteps' Hra2221 m t0); intro Hlock.
        etransitivity; [|apply Max.le_max_r].
        etransitivity; [|apply Hlock].
        inversion Hra221; clarify; unfold upd; clarify.
        { assert ((tr1 ++ l1 ++ [rel t m]) ++ l2 =
            firstn (length tr1 + length l1 + S (length l2))
            (tr1 ++ a :: tr2 ++ b :: tr3)) as Heq.
          { assert (a :: tr2 ++ b :: tr3 = (a :: tr2 ++ [b]) ++ tr3) as Heq
              by clarsimp; rewrite Heq, Hra1; clarsimp.
            rewrite <- plus_assoc, minus_plus; clarsimp.
            rewrite firstn_length', firstn_length'; try omega.
            rewrite not_le_minus_0; [|omega]; simpl; rewrite app_nil_r; auto. }
          rewrite Heq; rewrite <- (firstn_skipn (length tr1 + length l1 +
            S (length l2))) in Hfeasible; eapply feasible_app; eauto. }
      + clarify.
        destruct Hra2222 as [? | Hacq]; clarify.
        * assert (rel u m = acq u m); clarify.
          eapply app_inj_tail.
          instantiate (2 := a :: tr2).
          instantiate (1 := l1 ++ rel t m :: l2).
          clarsimp.
        * inversion Hacq as [|? ? ? ? Hstep Hl3]; clarify.
          generalize (clock_mono Hl3 u t0); inversion Hstep; clarify.
          etransitivity; eauto.
          unfold upd, vc_join in *; clarify.
          apply Max.le_max_l.
    - rewrite nth_error_split in Ha; clarify.
      rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hb; clarify.
      rewrite nth_error_split in Hb; clarify.
      destruct Hfj as [[[t Hfj] ?] | [[t Hfj] ?]].
      + destruct Hfj; clarify; inversion Hstepa; clarify.
        * generalize (clock_mono Hsteps2 (thread_of b) t0);
          unfold upd, vc_join; clarify.
          destruct (eq_dec t (thread_of b)); clarify.
          etransitivity; [apply Max.le_max_r|].
          etransitivity; [eauto | apply K_lower; auto].
        * (* A thread doesn't act after it's joined. *)
          inversion Hfeasible.
          specialize (Hjoin (length tr1)); rewrite nth_error_split in Hjoin.
          specialize (Hjoin _ _ eq_refl); clarify.
          specialize (Hexit _ _ Hjoin2 (length tr1 + S (length tr2))).
          rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hexit.
          simpl in Hexit; rewrite nth_error_split in Hexit;
            specialize (Hexit b); use Hexit; [clarify | omega].
          unfold uses_thread in Hexit; clarify.
          rewrite Hexit2 in *; clarify.
      + destruct Hfj; clarify.
        * (* A thread doesn't act before it's forked. *)
          inversion Hfeasible.
          specialize (Hfork (length tr1 + S (length tr2)));
            rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hfork;
            clarify; rewrite nth_error_split in Hfork.
          specialize (Hfork _ _ eq_refl); clarify.
          specialize (Hfork2 (length tr1) a).
          rewrite nth_error_split in Hfork2; clarify.
          unfold uses_thread in Hfork2; contradiction Hfork2; auto.
        * unfold upd, vc_join, vc_inc; clarify.
          etransitivity; [|apply Max.le_max_r].
          etransitivity; [apply K_upper; eauto|].
          eapply clock_mono; eauto.
    - generalize (hb_lt Hhb1), (hb_lt Hhb2); intros Hlti Hltj.
      destruct k; [omega | clarify].
      rewrite <- plus_n_Sm in Hltj; rewrite <- Nat.succ_lt_mono in Hltj.
      generalize (nth_error_succeeds tr2); intro Hk.
      specialize (Hk (k - length tr1)); use Hk; [|omega].
      destruct Hk as [c Hk].
      generalize (nth_error_split' _ _ Hk); intros [l1 [l2 ?]]; clarify.
      generalize (rtc_app_inv _ _ Hsteps2); intros [sc [Hl1 Hstepsc]].
      inversion Hstepsc as [|? sc' ? ? Hstepc Hl2]; clarify.
      transitivity (K c sc (thread_of c) t0).
      + destruct (eq_dec (thread_of a) (thread_of c)).
        { rewrite e; etransitivity; [apply K_upper; eauto|].
          etransitivity; [|apply K_lower].
          eapply clock_mono; eauto. }
        eapply IHHhb1; eauto; clarsimp; omega.
      + destruct (eq_dec (thread_of c) (thread_of b)).
        { rewrite e; etransitivity; [apply K_upper; eauto|].
          etransitivity; [|apply K_lower].
          eapply clock_mono; eauto. }
        generalize (ss_step _ _ Hstepa Hl1); intro Hstepsa.
        generalize (rtc_trans Hsteps1 Hstepsa); intro.
        eapply IHHhb2; eauto; clarsimp; omega.
  Qed.

  Lemma hb_prefix : forall i j l1 l2 (Hlt : j < length l1)
    (Hhb : happens_before (l1 ++ l2) i j), happens_before l1 i j.
  Proof.
    intros.
    generalize (hb_lt Hhb); intro.
    assert (i < length l1) by omega.
    induction Hhb; try (rewrite nth_error_app in *); clarify.
    - eapply hb_prog_order; eauto.
    - eapply hb_locking; eauto.
    - eapply hb_fork_join; eauto.
    - generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
      eapply hb_trans; [apply IHHhb1 | apply IHHhb2]; omega.
  Qed.

  Lemma rf_app : forall tr tr', race_free' (tr ++ tr') -> race_free' tr.
  Proof.
    repeat intro.
    generalize (nth_error_lt _ _ Ha), (nth_error_lt _ _ Hb); intros.
    eapply hb_prefix; auto; eapply H; eauto; rewrite nth_error_app; clarify.
  Qed.

  Lemma hb_clocks' sa a tr sb b : forall (Hwf : well_formed sa)
    (Hsteps : step_star sa (a :: tr) sb) tr0 s (Hsteps0 : step_star s tr0 sa)
    (Hfeasible : feasible (tr0 ++ a :: tr ++ [b]))
    t (Ht : t = thread_of a) u (Hu : u = thread_of b)
    (Hhb : happens_before (a :: tr ++ [b]) 0 (S (length tr)))
    x (Ha : accesses a x) y (Hb : accesses b y),
    vc_le (clock_of sa t) (clock_of sb u).
  Proof.
    intros.
    inversion Hsteps as [|? ? ? ? Hstepa Htr]; clarify.
    generalize (hb_app' tr0 Hhb); intro Hhb'; clarsimp.
    generalize (hb_clocks Hsteps0 Hstepa Htr _ eq_refl eq_refl _ Hhb');
      clarify.
    destruct Ha as [? [? | ?]], Hb as [? [? | ?]]; clarify.
  Qed.

  Lemma writesb_writes : forall a x, writesb a x = true <-> writes a x.
  Proof.
    destruct a; split; clarify; unfold writes, beq in *; clarify; eauto 2.
    inversion H; clarify.
  Qed.

  Lemma no_writes : forall s tr s' x (Hsteps : step_star s tr s')
    (Hno : Forall (fun a => ~writes a x) tr), write_of s' x = write_of s x.
  Proof.
    intros; induction Hsteps; clarify.
    inversion Hno as [|? ? Ha ?]; clarify.
    unfold writes in *; inversion Hstep; clarify.
    unfold upd in *; clarify.
    contradiction Ha; eauto.
  Qed.

  Opaque skipn.

  Lemma access_write : forall tr s a x (Hsteps : step_star s0 tr s)
    (Hrf : race_free' (tr ++ [a])) (Haccesses : accesses a x)
    (Hfeasible : feasible (tr ++ [a])),
    vc_le (write_of s x) (clock_of s (thread_of a)).
  Proof.
    intros.
    destruct (last_write tr x) eqn: Hfind; clarify.
    - unfold last_write in Hfind; rewrite find_index_spec in Hfind; clarify.
      generalize (nth_error_rev' _ _ Hfind1); intro Hnth.
      generalize (nth_error_lt _ _ Hnth); intro Hlt.
      specialize (Hrf _ _ Hlt); rewrite nth_error_split, nth_error_app in Hrf;
        clarify.
      specialize (Hrf _ _ Hnth eq_refl x).
      rewrite writesb_writes in Hfind21.
      generalize (writes_accesses Hfind21); clarify.
      rewrite <- (firstn_skipn (length tr - n - 1) tr) in Hrf at 1;
        rewrite <- app_assoc in Hrf.
      generalize (List.firstn_length (length tr - n - 1) tr);
        rewrite Min.min_l; [intro Hlen | omega].
      generalize (hb_suffix _ _ Hrf); rewrite Hlen, minus_diag.
      rewrite <- (skipn_length (length tr - n - 1)); intro Hhb'; clarify.
      rewrite <- (firstn_skipn (length tr - n - 1) tr) in Hsteps, Hfeasible.
      erewrite skipn_n in Hsteps, Hfeasible, Hhb'; eauto.
      generalize (rtc_app_inv _ _ Hsteps); intros [s' [Hs' Hs]].
      generalize (step_star_wf wf0 Hs'); intro Hwf'.
      rewrite <- app_assoc in Hfeasible.
      generalize (hb_clocks' Hwf' Hs Hs' Hfeasible eq_refl eq_refl Hhb' H
        Haccesses); intro Hle.
      intro; etransitivity; [|apply Hle].
      destruct Hfind21 as [u ?]; subst.
      inversion Hs as [|? ? ? ? Hstep Hnone]; clarify.
      generalize (write_result Hstep); intros [Hw' Hc'].
      generalize (rtc_snoc _ _ Hs' Hstep); intro Hs'0.
      rewrite <- Hc' in *; generalize (write_own _ _ Hs'0 Hw'); intro Hle'.
      use Hle'; [|inversion Hstep; auto].
      etransitivity; [|apply Hle'].
      erewrite no_writes; eauto.
      rewrite Forall_forall; intros ? Hin.
      generalize (in_nth_error _ _ Hin); intros [j Hj]; clarify.
      rewrite skipn_length, skipn_nth in *.
      rewrite <- writesb_writes, Bool.not_true_iff_false; eapply Hfind22;
        [|apply nth_error_rev; eauto].
      generalize (nth_error_lt _ _ Hfind1); rewrite rev_length; intro Hn.
      clear - Hn Hj1; rewrite plus_comm, Nat.sub_add_distr,
        (Nat.sub_succ_r (length tr)).
      rewrite minus_distr, Nat.add_1_r; simpl; [| omega | omega].
      rewrite minus_distr, minus_diag; [| omega | omega].
      destruct n; omega.
    - unfold last_write in Hfind; rewrite find_index_fail in Hfind.
      erewrite no_writes; eauto; [intro; clarify|].
      rewrite Forall_rev in Hfind; eapply Forall_impl; eauto; clarify.
      intro; rewrite <- writesb_writes in *; clarify.
  Qed.

  Lemma read_step : forall s a s' tr s'' x t (Hstep : step s a s')
    (Hwf : well_formed s) (Hsteps : step_star s' tr s'')
    (Hle : vc_le (read_of s x) (clock_of s'' t))
    (Hrf : accesses a x ->
       happens_before (a :: tr ++ [wr t x]) 0 (S (length tr)))
    tr0 s0 (Hsteps0 : step_star s0 tr0 s)
    (Hfeasible : feasible (tr0 ++ a :: tr ++ [wr t x])),
    vc_le (read_of s' x) (clock_of s'' t).
  Proof.
    intros; intro u.
    inversion Hstep; clarify; unfold upd; clarify.
    assert (accesses (rd u x) x) as Haccess by (unfold accesses; eauto);
      clarify.
    generalize (ss_step _ _ Hstep Hsteps); intro Hsteps'.
    assert (well_formed (C, L, R, W, X)) as Hwf by (split; auto).
    generalize (hb_clocks' Hwf Hsteps' Hsteps0 Hfeasible eq_refl eq_refl Hrf
      Haccess); intro Hle'; eapply Hle'.
    unfold accesses; eauto.
  Qed.

  Lemma write_read_aux : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hread : forall tr1 sa a sa' tr2, tr = tr1 ++ a :: tr2 ->
       step_star s0 tr1 sa -> step sa a sa' -> step_star sa' tr2 s ->
       vc_le (read_of sa' x) (clock_of s t)),
    vc_le (read_of s x) (clock_of s t).
  Proof.
    intros.
    destruct (eq_dec tr []).
    { subst; inversion Hsteps; intro; clarify. }
    rewrite (app_removelast_last (wr t x)) in Hsteps; auto.
    generalize (rtc_snoc_inv _ _ Hsteps); clarify.
    eapply Hread; eauto; try (apply ss_refl).
    apply app_removelast_last; auto.
  Qed.

  Lemma write_read : forall tr s t x (Hsteps : step_star s0 tr s)
    (Hrf : forall i a, nth_error tr i = Some a -> accesses a x ->
       happens_before (tr ++ [wr t x]) i (length tr))
    (Hfeasible : feasible (tr ++ [wr t x])),
    vc_le (read_of s x) (clock_of s t).
  Proof.
    intros; eapply write_read_aux; eauto.
    induction tr1 using rev_ind; intros sa a sa' tr2 ? H0 Ha Htr2; clarify.
    - inversion H0; clarify.
      eapply read_step; eauto.
      + apply wf0.
      + intro; clarify.
      + apply Hrf; auto.
    - generalize (rtc_snoc_inv _ _ H0); intros [sx [Htr Hx]].
      rewrite <- app_assoc in IHtr1; simpl in IHtr1;
        specialize (IHtr1 _ _ _ _ eq_refl Htr Hx).
      generalize (ss_step _ _ Ha Htr2); clarify.
      eapply read_step; eauto.
      + eapply (step_star_wf wf0); eauto.
      + specialize (Hrf (length (tr1 ++ [x0])) a);
          rewrite nth_error_split in Hrf; clarify.
        rewrite (app_length (tr1 ++ [x0])) in Hrf.
        rewrite <- app_assoc in Hrf; generalize (hb_suffix _ _ Hrf);
          clarsimp.
      + clarsimp.
  Qed.

  Lemma exited_exit : forall tr s (Hsteps : step_star s0 tr s) t,
    In t (exited_of s) <-> In (exit t) tr.
  Proof.
    induction tr using rev_ind; clarify.
    - inversion Hsteps; clarify; reflexivity.
    - exploit rtc_snoc_inv; eauto; intros (? & Hsteps' & Hstep).
      specialize (IHtr _ Hsteps' t); rewrite in_app, <- IHtr.
      inversion Hstep; split; clarify.
      inversion H; auto.
  Qed.
    
  Lemma next_live : forall tr a (Hfeasible : feasible (tr ++ [a]))
    s (Hsteps : step_star s0 tr s), ~In (thread_of a) (exited_of s).
  Proof.
    repeat intro.
    rewrite exited_exit in *; eauto.
    exploit in_nth_error; eauto; intros (k & ? & ?).
    inversion Hfeasible.
    exploit Hexit; eauto.
    { rewrite nth_error_app; clarify; eauto. }
    { apply nth_error_split. }
    { unfold uses_thread; auto. }
    intros (? & ? & Heq); rewrite Heq in *; clarify.
  Qed.
    
  Theorem Completeness tr : feasible tr -> race_free tr ->
    exists s, step_star s0 tr s.
  Proof.
    setoid_rewrite race_free_alt; induction tr using rev_ind;
      intros Hfeasible Hrf.
    { eexists; apply ss_refl. }
    generalize (feasible_snoc _ _ Hfeasible); clarify.
    generalize (rf_app _ _ Hrf); intro; use IHtr; destruct IHtr as [s Htr].
    assert (exists s', step s x s') as [s' ?];
      [|eexists; eapply rtc_snoc; eauto].
    destruct s as ((((C, L), R), W), X).
    generalize (step_star_wf wf0 Htr); intro Hwf.
    generalize (next_live _ Hfeasible Htr); simpl; intro.
    destruct x; try (eexists; econstructor; eauto; fail).
    - eexists; eapply read_upd; eauto.
      generalize (access_write(x := x) Htr Hrf); intro HW; clarify; apply HW;
        unfold accesses; eauto.
    - eexists; eapply write_upd; eauto.
      + generalize (access_write(x := x) Htr Hrf); intro HW; clarify; apply HW;
          unfold accesses; eauto.
      + generalize (write_read(x := x) t Htr); intro HR; clarify; apply HR;
          auto.
        intros ? ? Hnth ?.
        generalize (nth_error_lt _ _ Hnth); intro.
        eapply Hrf; auto.
        * rewrite nth_error_app; clarify; eauto 2.
        * apply nth_error_split.
        * unfold writes; eauto.
        * unfold accesses; eauto.
    - eexists; econstructor; eauto.
      inversion Hfeasible.
      specialize (Hjoin _ _ _ (nth_error_split _ _ _)); clarify.
      rewrite nth_error_app in *; clarify.
      exploit nth_error_in; eauto.
      rewrite <- exited_exit; eauto; clarify.
  Qed.

  Theorem Correctness tr (Hfeasible : feasible tr) :
    race_free tr <-> exists s, step_star s0 tr s.
  Proof.
    split.
    - apply Completeness; auto.
    - intros [? ?]; eapply Soundness; eauto.
  Qed.

End VectorClocks.