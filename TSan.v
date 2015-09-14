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

  (* TSan actually corresponds to a slightly different base VC algorithm from
     FastTrack - one in which reads and writes store their entire VC, rather
     than just the timestamp of the thread involved. *)
  Inductive step : @state tid var lock -> operation ->
    @state tid var lock -> Prop :=
  | read_upd : forall C L R W t x R' (HW : vc_le (W x) (C t))
     (HR' : R' = upd R x (vc_join (R x) (C t))),
     step (C, L, R, W) (rd t x) (C, L, R', W)
  | write_upd : forall C L R W t x R' W' (HW : vc_le (W x) (C t))
     (HR : vc_le (R x) (C t)) (HR' : R' = upd R x (C t))
     (HW : W' = upd W x (C t)),
     step (C, L, R, W) (wr t x) (C, L, R', W')
  | acquire : forall C L R W t m C' (HC' : C' = upd C t (vc_join (C t) (L m))),
     step (C, L, R, W) (acq t m) (C', L, R, W)
  | release : forall C L R W t m L' C' (HL' : L' = upd L m (C t))
      (HC' : C' = upd C t (vc_inc t (C t))),
     step (C, L, R, W) (rel t m) (C', L', R, W)
  | fork_step : forall C L R W t u C'
      (HC' : C' = upd (upd C u (vc_join (C u) (C t))) t (vc_inc t (C t))),
     step (C, L, R, W) (fork t u) (C', L, R, W)
  | join_step : forall C L R W t u C'
      (HC' : C' = upd (upd C t (vc_join (C t) (C u))) u (vc_inc u (C u))),
     step (C, L, R, W) (join t u) (C', L, R, W).

  Definition step_star := rtc step.

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
    destruct s as (((C, L), R), W); 
      destruct Hwf as [Hthreads [Hlocks [Hread Hwrite]]]; 
      inversion Hstep; clarify; unfold upd; repeat dec_eq;
      repeat split; intros; repeat dec_eq; repeat join_solve.
    - setoid_rewrite Nat.max_lub_iff; clarify.
      destruct (eq_dec t0 t); clarify.
      specialize (Hthreads _ _ n); omega.
    - destruct (eq_dec t0 t); clarify.
      specialize (Hthreads _ _ n); omega.
    - destruct (eq_dec t0 t); clarify.
      specialize (Hthreads _ _ n); omega.
  Qed.

  Corollary step_star_wf s s' tr (Hwf : well_formed s) 
    (Hsteps : step_star s tr s') : well_formed s'.
  Proof.
    induction Hsteps; auto.
    apply IHHsteps; eapply wf_preservation; eauto.
  Qed.

  Lemma clock_mono : forall s s' tr (Hsteps : step_star s tr s') u t,
    clock_of s u t <= clock_of s' u t.
  Proof.
    intros; induction Hsteps; auto.
    inversion Hstep; unfold upd, vc_inc, vc_join in *; clarify; dec_eq;
      try omega; eapply Max.max_lub_l; eauto.
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

  (* Soundness *)
  Lemma clocks_hb_core : forall tr s (Hwf : well_formed s) s'
    (Hsteps : step_star s tr s') t,
    (forall u, u <> t -> clock_of s t t <= clock_of s' u t ->
       exists i j e d, nth_error tr i = Some e /\ nth_error tr j = Some d /\
       uses_thread d u /\ uses_thread e t /\ hbe tr i j) /\
    (forall m, clock_of s t t <= lock_of s' m t ->
       exists i j e d, nth_error tr i = Some e /\ nth_error tr j = Some d /\
       locks d m /\ uses_thread e t /\ hbe tr i j).
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; clarify.
      destruct s' as (((?, ?), ?), ?); destruct Hwf as [Hclock [Hlock _]].
      split; clarify.
      - specialize (Hclock u t); clarify; omega.
      - specialize (Hlock m t); omega. }
    generalize (rtc_snoc_inv _ _ Hsteps); intros [s'' [Htr Hx]].
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
          unfold uses_thread; clarify; repeat eexists; eauto.
        eapply hbe_trans; [apply hbe_app; eauto|].
        left; eapply hb_locking; unfold locks; try (rewrite nth_error_split);
          try (rewrite nth_error_app); clarify; eauto.
      + destruct (eq_dec t0 u); clarify.
        generalize (Max.max_spec (C u t) (C t0 t));
          intros [[? Hmax] | [? Hmax]]; rewrite Hmax in *; try omega.
        destruct (eq_dec t0 t); subst.
        { exists (length tr), (length tr); rewrite nth_error_split;
            repeat eexists; eauto.
          * unfold uses_thread, fjs; eauto.
          * unfold uses_thread; auto.
          * unfold hbe; auto. }
        specialize (IHtr1 _ n1); use IHtr1.
        destruct IHtr1 as (i & j & ? & ? & Hi & Hj & ?); clarify.
        exists i, (length tr); rewrite nth_error_split.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        rewrite nth_error_app; clarify; repeat eexists; eauto.
        * unfold uses_thread, fjs; eauto.
        * eapply hbe_trans; [apply hbe_app; eauto|].
          left; eapply hb_fork_join; auto; try (rewrite nth_error_split);
            try (rewrite nth_error_app); clarify; eauto.
          unfold uses_thread; auto.
      + destruct (eq_dec u0 u); clarify.
        generalize (Max.max_spec (C u t) (C u0 t));
          intros [[? Hmax] | [? Hmax]]; rewrite Hmax in *; try omega.
        destruct (eq_dec u0 t); subst.
        { exists (length tr), (length tr); rewrite nth_error_split;
            repeat eexists; eauto.
          * unfold uses_thread; auto.
          * unfold uses_thread, fjs; eauto.
          * unfold hbe; auto. }
        specialize (IHtr1 _ n1); use IHtr1.
        destruct IHtr1 as (i & j & ? & ? & Hi & Hj & ?); clarify.
        exists i, (length tr); rewrite nth_error_split.
        generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
        rewrite nth_error_app; clarify; repeat eexists; eauto.
        * unfold uses_thread, fjs; eauto.
        * eapply hbe_trans; [apply hbe_app; eauto|].
          left; eapply hb_fork_join; auto; try (rewrite nth_error_split);
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
        left; eapply hb_fork_join; auto; try (rewrite nth_error_split);
          try (rewrite nth_error_app); clarify; eauto.
        unfold uses_thread; auto.
  Qed.
  (* This seems to be the core of the relationship between vector clocks and
     the happens-before order. Does it appear in the literature? *)

  Lemma clocks_hb sa a tr sb b : forall (Hwf : well_formed sa)
    (Hsteps : step_star sa (a :: tr) sb)
    t (Ht : t = thread_of a) u (Hu : u = thread_of b)
    (Hclock_lt : clock_of sa t t <= clock_of sb u t),
    happens_before (a :: tr ++ [b]) 0 (S (length tr)).
  Proof.
    intros.
    destruct (eq_dec u t).
    - subst; symmetry in e; eapply hb_prog_order; eauto; clarify.
      apply nth_error_split.
    - generalize (clocks_hb_core Hwf Hsteps t); intros [Hhb _].
      specialize (Hhb _ n Hclock_lt).
      destruct Hhb as (i & j & e & d & Hi & Hj & ?); clarify.
      generalize (nth_error_lt _ _ Hi), (nth_error_lt _ _ Hj); intros.
      eapply hbe_hb_trans; [|eapply hbe_hb_trans].
      + unfold hbe; destruct (eq_dec 0 i); eauto.
        left; eapply hb_fork_join; clarify; eauto.
        * omega.
        * destruct i; clarify; rewrite nth_error_app; clarify; omega.
        * unfold uses_thread; auto.
      + assert (hbe ((a :: tr) ++ [b]) i j) by (apply hbe_app; auto);
          clarify; eauto.
      + eapply hb_fork_join; clarify.
        * instantiate (1 := d); destruct j; clarify.
          rewrite <- Nat.succ_lt_mono, nth_error_app in *; clarify.
        * apply nth_error_split.
        * eauto.
        * unfold uses_thread; auto.
  Qed.

  Lemma clocks_hb' tr1 sa a tr2 sb b tr3 : forall (Hwf : well_formed sa)
    (Hsteps : step_star sa (a :: tr2) sb)
    t (Ht : t = thread_of a) u (Hu : u = thread_of b)
    (Hclock_lt : clock_of sa t t <= clock_of sb u t),
    happens_before (tr1 ++ a :: tr2 ++ b :: tr3)
                   (length tr1) (length tr1 + S (length tr2)).
  Proof.
    intros; generalize (clocks_hb _ Hwf Hsteps Ht Hu Hclock_lt); intro Hhb.
    generalize (hb_app tr3 (hb_app' tr1 Hhb)); clarsimp.
  Qed.

  Lemma write_own' : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hwrite : write_of s x t = clock_of s t t),
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
      setoid_rewrite Nat.max_lub_iff; clarify.
      destruct (eq_dec t t0); clarify.
      specialize (Hwf1 _ _ n); specialize (HW t).
      destruct (eq_dec t1 t); clarify; omega.
    - unfold upd in *; clarify.
      destruct (eq_dec t t0); [split; intro|]; clarify.
      specialize (Hwf1 _ _ n); omega.
    - unfold upd in *; clarify.
      unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
      split; intro; join_solve.
      { specialize (Hwf21 m t); omega. }
    - unfold upd, vc_inc in *; clarify.
      specialize (Hwf222 x0 t); omega.
    - unfold upd, vc_inc in *; clarify.
      destruct (eq_dec t0 t); clarify.
      + specialize (Hwf222 x0 t); omega.
      + unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
        split; intro; join_solve.
        { specialize (Hwf1 t0 t); clarify; omega. }
    - unfold upd, vc_inc in *; clarify.
      destruct (eq_dec u t); clarify.
      + specialize (Hwf222 x0 t); omega.
      + unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
        split; intro; join_solve.
        { specialize (Hwf1 u t); clarify; omega. }
  Qed.

  Corollary write_own : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hwrite : write_of s x t = clock_of s t t),
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
    inversion Hstep; clarify; unfold upd; clarify.
    apply Max.le_max_l.
  Qed.

  Lemma write_result : forall s t x s' (Hstep : step s (wr t x) s'),
    write_of s' x t = clock_of s t t /\ clock_of s' t = clock_of s t.
  Proof.
    intros; inversion Hstep; unfold upd in *; clarify.
  Qed.

  Lemma write_after_write : forall tr s i j x t u
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
    rewrite Htr in Hsteps; clear Htr.
    generalize (rtc_app_inv _ _ Hsteps); intros (? & ? & Hsteps').
    rewrite app_comm_cons in Hsteps'; generalize (rtc_app_inv _ _ Hsteps');
      intros (? & Hstepsi & Hstepsj).
    eapply clocks_hb'; eauto.
    { eapply step_star_wf; eauto; apply wf0. }
    inversion Hstepsi as [|? ? ? ? Hstepi Htr2]; clarify.
    inversion Hstepsj as [|? ? ? ? Hstepj ?]; clarify.
    generalize (write_result Hstepi), (write_result Hstepj);
      intros [Hwi Hci] [Hwj Hcj].
    rewrite <- Hcj in *; etransitivity; [|eapply write_own; eauto].
    generalize (rtc_snoc _ _ Htr2 Hstepj); intro.
    etransitivity; [|eapply write_mono; eauto]; clarsimp.
    { eapply rtc_snoc; [|eauto].
      eapply rtc_trans; eauto. }
  Qed.

  Lemma read_own : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hwrite : read_of s x t = clock_of s t t),
    vc_le (write_of s x) (clock_of s t).
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; intro; clarify. }
    generalize (rtc_snoc_inv _ _ Hsteps); intros [s' [Htr Hs']].
    generalize (step_star_wf wf0 Htr); intro Hwf.
    specialize (IHtr _ x0 t Htr).
    inversion Hs'; clarify.
    - unfold upd in *; clarify.
      destruct (eq_dec t t0); clarify.
      specialize (Hwf1 _ _ n).
      generalize (Max.max_spec (R x0 t) (C t0 t)); intros [[? Hmax] | [? Hmax]];
        setoid_rewrite Hmax in Hwrite; [omega | clarify].
    - unfold upd in *; clarify.
      intro; clarify.
      destruct (eq_dec t t0); clarify.
      specialize (Hwf1 _ _ n); specialize (HR t); omega.
    - unfold upd in *; clarify.
      unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
      intro; join_solve.
      { specialize (Hwf21 m t); omega. }
    - unfold upd, vc_inc in *; clarify.
      specialize (Hwf221 x0 t); omega.
    - unfold upd, vc_inc in *; clarify.
      destruct (eq_dec t0 t); clarify.
      + specialize (Hwf221 x0 t); omega.
      + unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
        intro; join_solve.
        { specialize (Hwf1 t0 t); clarify; omega. }
    - unfold upd, vc_inc in *; clarify.
      destruct (eq_dec u t); clarify.
      + specialize (Hwf221 x0 t); omega.
      + unfold vc_join in Hwrite; rewrite Max.max_l in Hwrite; clarify.
        intro; join_solve.
        { specialize (Hwf1 u t); clarify; omega. }
  Qed.
  
  Lemma read_result : forall s t x s' (Hstep : step s (rd t x) s')
    (Hwf : well_formed s),
    read_of s' x t = clock_of s t t /\ clock_of s' t = clock_of s t.
  Proof.
    intros; inversion Hstep; unfold upd in *; clarify.
    setoid_rewrite Max.max_r; auto.
  Qed.

  Lemma read_after_write : forall tr s i j x t u
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
    rewrite Htr in Hsteps; clear Htr.
    generalize (rtc_app_inv _ _ Hsteps); intros (? & ? & Hsteps').
    rewrite app_comm_cons in Hsteps'; generalize (rtc_app_inv _ _ Hsteps');
      intros (? & Hstepsi & Hstepsj).
    eapply clocks_hb'; eauto.
    { eapply step_star_wf; eauto; apply wf0. }
    inversion Hstepsi as [|? ? ? ? Hstepi Htr2]; clarify.
    inversion Hstepsj as [|? ? ? ? Hstepj ?]; clarify.
    generalize (step_star_wf wf0 H1); intro Hwf0.
    exploit step_star_wf; eauto; intro Hwf1.
    generalize (write_result Hstepi), (read_result Hstepj Hwf1);
      intros [Hwi Hci] [Hwj Hcj].
    rewrite <- Hcj in *; etransitivity; [|eapply read_own; eauto].
    generalize (rtc_snoc _ _ Htr2 Hstepj); intro.
    etransitivity; [|eapply write_mono; eauto]; clarsimp.
    { eapply rtc_snoc; [|eauto].
      eapply rtc_trans; eauto. }
  Qed.

  Lemma write_after_read : forall tr s i j x t u
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
    rewrite Htr in Hsteps; clear Htr.
    generalize (rtc_app_inv _ _ Hsteps); intros (? & ? & Hsteps').
    rewrite app_comm_cons in Hsteps'; generalize (rtc_app_inv _ _ Hsteps');
      intros (? & Hstepsi & Hstepsj).
    eapply clocks_hb'; eauto.
    { eapply step_star_wf; eauto; apply wf0. }
    inversion Hstepsi as [|? ? ? ? Hstepi Htr2]; clarify.
    inversion Hstepsj as [|? ? ? ? Hstepj ?]; clarify.
    generalize (step_star_wf wf0 H1); intro Hwf0.
    generalize (read_result Hstepi Hwf0), (write_result Hstepj);
      intros [Hwi Hci] [Hwj Hcj].
    rewrite <- Hcj in *; etransitivity; [|eapply write_own'; eauto].
    generalize (rtc_snoc _ _ Htr2 Hstepj); intro.
    etransitivity; [|eapply read_mono; eauto]; clarsimp.
    { eapply (step_star_wf wf0).
      eapply rtc_snoc; eauto. }
    { eapply rtc_snoc; [|eauto].
      eapply rtc_trans; eauto. }
  Qed.

  Theorem Soundness tr : forall s', step_star s0 tr s' -> race_free tr.
  Proof.
    intros; rewrite race_free_alt; repeat intro; clarify.
    unfold writes in *; destruct Haccesses1 as [t [H1 | H1]],
      Haccesses2 as [u [H2 | H2]]; clarify.
    - eapply write_after_read; eauto.
    - eapply read_after_write; eauto.
    - eapply write_after_write; eauto.
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
              rewrite nth_error_split in Hj22; specialize (Hj22 t);
                contradiction Hj22; auto. }
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
          setoid_rewrite Heq; rewrite <- (firstn_skipn (length tr1 + length l1 +
            S (length l2))) in Hfeasible; eapply feasible_app; eauto. }
      + clarify.
        destruct Hra2222 as [? | Hacq]; clarify.
        * setoid_rewrite (split_app [] _ a) in Hra1;
            rewrite (split_app l1), app_assoc, app_assoc in Hra1.
          exploit app_inj_tail; eauto; clarify.
        * inversion Hacq as [|? ? ? ? Hstep Hl3]; clarify.
          generalize (clock_mono Hl3 u t0); inversion Hstep; clarify.
          etransitivity; eauto.
          unfold upd, vc_join in *; clarify.
          apply Max.le_max_l.
    - rewrite nth_error_split in Ha; clarify.
      rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hb; clarify.
      rewrite nth_error_split in Hb; clarify.
      destruct Ha0 as [? | Hfj]; [destruct Hb0 as [? | Hfj]; clarsimp|];
        unfold fjs in *; destruct Hfj as [u Hfj].
      + destruct Hfj; clarify.
        * (* A thread doesn't act before it's forked. *)
          inversion Hfeasible.
          specialize (Hfork (length tr1 + S (length tr2)));
            rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hfork;
            clarify; rewrite nth_error_split in Hfork.
          specialize (Hfork _ _ eq_refl (length tr1) a);
            rewrite nth_error_split in Hfork; clarify.
          unfold uses_thread in Hfork.
          use Hfork; [contradiction Hfork; clarify | omega].
        * unfold upd, vc_join, vc_inc; clarify.
          destruct (eq_dec (thread_of a) u); clarify.
          etransitivity; [|apply Max.le_max_r].
          etransitivity; [apply K_upper; eauto|].
          eapply clock_mono; eauto.
      + destruct Hfj; clarify; inversion Hstepa; clarify.
        * destruct Hb0 as [? | Hfj]; clarify.
          { generalize (clock_mono Hsteps2 (thread_of b) t0);
              unfold upd, vc_join; clarify.
            destruct (eq_dec u (thread_of b)); clarify.
            etransitivity; [apply Max.le_max_r|].
            etransitivity; [eauto | apply K_lower; auto]. }
          destruct Hfj as [v [? | ?]]; clarify.
          { (* A thread isn't forked twice. *)
            inversion Hfeasible.
            specialize (Hfork (length tr1 + S (length tr2)));
              rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hfork;
              clarify; rewrite nth_error_split in Hfork.
            specialize (Hfork _ _ eq_refl (length tr1) (fork u t));
              rewrite nth_error_split in Hfork; clarify. 
            use Hfork; [contradiction Hfork; clarify | omega].
            unfold uses_thread, fjs; eauto. }
          generalize (clock_mono Hsteps2 t t0).
          unfold upd, vc_join, vc_inc; clarify.
          destruct (eq_dec u t); clarify.
          { generalize (fork_irrefl(t := t) (length tr1) Hfeasible);
              rewrite nth_error_split; intro X; contradiction X; auto. }
          destruct (eq_dec t v); clarify.
          { generalize (join_irrefl(t := v) (length tr1 + S (length tr2))
              Hfeasible); rewrite nth_error_app, lt_dec_plus_r, minus_plus;
              simpl; rewrite nth_error_split; intro X; contradiction X; auto. }
          etransitivity; [apply Max.le_max_r|].
          etransitivity; eauto; apply Max.le_max_r.
        * (* Nor does it act after it joins. *)
          inversion Hfeasible.
          specialize (Hjoin (length tr1)); rewrite nth_error_split in Hjoin.
          specialize (Hjoin _ _ eq_refl (length tr1 + S (length tr2)));
            rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hjoin.
          simpl in Hjoin; rewrite nth_error_split in Hjoin;
            specialize (Hjoin b); use Hjoin; [clarify | omega].
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
      generalize (hb_suffix _ _ Hrf); setoid_rewrite Hlen; rewrite minus_diag.
      rewrite <- (skipn_length (length tr - n - 1)); intro Hhb'; clarify.
      rewrite <- (firstn_skipn (length tr - n - 1) tr) in Hsteps, Hfeasible.
      erewrite skipn_n in Hsteps, Hfeasible, Hhb'; eauto.
      erewrite (skipn_n (length tr - n - 1)) in Hhb'; eauto.
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
      rewrite minus_distr, Nat.add_1_r; simpl; [| omega |].
      rewrite minus_distr, minus_diag; [| omega | apply lt_le_weak; auto].
      destruct n; omega.
      { generalize (lt_not_le _ _ Hn); rewrite <- Nat.sub_0_le.
        destruct (length tr - n) eqn: Hminus; setoid_rewrite Hminus;
          [clarify | omega]. }
    - unfold last_write in Hfind; rewrite find_index_fail in Hfind.
      erewrite no_writes; eauto; [intro; clarify|].
      rewrite Forall_rev in Hfind; eapply Forall_impl; eauto; clarify.
      intro X; setoid_rewrite <- writesb_writes in X; clarify.
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
    - assert (accesses (rd(lock := lock) t0 x) x) as Haccess
        by (unfold accesses; eauto); clarify.
      generalize (ss_step _ _ Hstep Hsteps); intro Hsteps'.
      setoid_rewrite Nat.max_lub_iff; clarify.
      assert (well_formed (C, L, R, W)) as Hwf by (split; auto).
      generalize (hb_clocks' Hwf Hsteps' Hsteps0 Hfeasible eq_refl eq_refl Hrf
        Haccess); intro Hle'; eapply Hle'.
      unfold accesses; eauto.
    - assert (accesses (wr(lock := lock) t0 x) x) as Haccess
        by (unfold accesses; eauto); clarify.
      generalize (ss_step _ _ Hstep Hsteps); intro Hsteps'.
      assert (well_formed (C, L, R, W)) as Hwf by (split; auto).
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
    setoid_rewrite (app_removelast_last (wr t x)) in Hsteps; auto.
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
    destruct s as (((C, L), R), W).
    generalize (step_star_wf wf0 Htr); intro Hwf.
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
  Qed.

  Theorem Correctness tr (Hfeasible : feasible tr) :
    race_free tr <-> exists s, step_star s0 tr s.
  Proof.
    split.
    - apply Completeness; auto.
    - intros [? ?]; eapply Soundness; eauto.
  Qed.

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

  Inductive TS_step : state -> operation -> state -> Prop :=
  | on_read : forall C L R W t x Vs' R'
     (HW : Forall (fun s => vc_le (snd s) (C t)) (W x))
     (HR : drop_le (C t) (R x) Vs') (HR' : R' = upd R x ((t, C t) :: Vs')),
     TS_step (C, L, R, W) (rd t x) (C, L, R', W)
  | on_write : forall C L R W t x R' W'
     (* We must be able to drop all previous reads and writes *)
     (HR : Forall (fun s => vc_le (snd s) (C t)) (R x))
     (HW : Forall (fun s => vc_le (snd s) (C t)) (W x))
     (HR' : R' = upd R x [(t, C t)]) (HW' : W' = upd W x [(t, C t)]),
     TS_step (C, L, R, W) (wr t x) (C, L, R', W')
  | on_signal : forall C L R W t m L' C' (HL' : L' = upd L m (C t))
      (HC' : C' = upd C t (vc_inc t (C t))),
     TS_step (C, L, R, W) (rel t m) (C', L', R, W)
  | on_wait : forall C L R W t m C' (HC' : C' = upd C t (vc_join (C t) (L m))),
     TS_step (C, L, R, W) (acq t m) (C', L, R, W)
(* Are fork and join handled by signal and wait?*)
  | on_fork : forall C L R W t u C'
      (HC' : C' = upd (upd C u (vc_join (C u) (C t))) t (vc_inc t (C t))),
     TS_step (C, L, R, W) (fork t u) (C', L, R, W)
  | on_join : forall C L R W t u C'
      (HC' : C' = upd (upd C t (vc_join (C t) (C u))) u (vc_inc u (C u))),
     TS_step (C, L, R, W) (join t u) (C', L, R, W).

  Definition TS_step_star := rtc TS_step.

  Fixpoint join_list (ss : list (tid * vector_clock)) :=
    match ss with
    | [] => vc_bot
    | (_, V) :: rest => vc_join V (join_list rest)
    end.

  Lemma vc_bot_le : forall (V : vector_clock), vc_le vc_bot V.
  Proof. unfold vc_bot; repeat intro; omega. Qed.
  Hint Resolve vc_bot_le.

  Lemma join_le : forall V ss, vc_le (join_list ss) V <->
    Forall (fun s => vc_le (snd s) V) ss.
  Proof.
    induction ss.
    - split; clarify.
    - destruct a; simpl.
      rewrite vc_join_le, IHss; split; clarify.
      inversion H; clarify.
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
    (forall t, finite (C1 t)) /\ (forall m, finite (L1 m)) /\
    forall x, vc_eq (join_list (R2 x)) (R1 x) /\
              vc_eq (join_list (W2 x)) (W1 x) /\
              Forall (fun s => finite (snd s)) (R2 x) /\
              Forall (fun s => finite (snd s)) (W2 x) end.

  Import RelationClasses.
  Instance vc_eq_refl : Reflexive (@vc_eq tid).
  Proof. repeat intro; auto. Qed.
  Hint Resolve vc_eq_refl.

  Instance vc_eq_trans : Transitive (@vc_eq tid).
  Proof. repeat intro; etransitivity; eauto. Qed.

  Instance vc_eq_sym : Symmetric (@vc_eq tid).
  Proof. repeat intro; auto. Qed.

  Instance vc_eq_eq : Equivalence (@vc_eq tid).
  Proof.
    constructor; [apply vc_eq_refl | apply vc_eq_sym | apply vc_eq_trans].
  Qed.

  Lemma finite_bot : finite vc_bot.
  Proof.
    exists []; clarify.
  Qed.
  Hint Resolve finite_bot.

  Lemma finite_inc : forall V t, finite V -> finite (vc_inc t V).
  Proof.
    intros ??[??].
    exists (t :: x); unfold vc_inc; clarify.
    contradiction H0; auto.
  Qed. 
  Hint Resolve finite_inc.

  Lemma TS_sim0 : TS_sim (VectorClocks.s0) s0.
  Proof. clarify. Qed.

  Lemma vc_join_assoc : forall (V1 V2 V3 : vector_clock),
    vc_eq (vc_join (vc_join V1 V2) V3) (vc_join V1 (vc_join V2 V3)).
  Proof.
    repeat intro; symmetry; apply Max.max_assoc.
  Qed.

  Lemma vc_join_sym : forall (V1 V2 : vector_clock),
    vc_eq (vc_join V1 V2) (vc_join V2 V1).
  Proof.
    repeat intro; apply Max.max_comm.
  Qed.

  Import Morphisms.
  Instance join_proper : Proper (vc_eq ==> vc_eq ==> vc_eq) (@vc_join tid).
  Proof.
    repeat intro; unfold vc_join; clarsimp.
  Qed.

  Lemma vc_absorb : forall (V V' : vector_clock), vc_le V V' ->
    vc_eq (vc_join V V') V'.
  Proof.
    repeat intro; apply Max.max_r; auto.
  Qed.

  Lemma join_drop_le : forall V l l' (Hdrop : drop_le V l l'),
    vc_eq (vc_join V (join_list l')) (vc_join (join_list l) V).
  Proof.
    intros; induction Hdrop; clarify.
    - rewrite vc_join_sym; auto.
    - rewrite IHHdrop, (vc_join_sym V1), vc_join_assoc, (vc_absorb Hle); auto.
    - rewrite (vc_join_sym V1); rewrite <- vc_join_assoc, IHHdrop.
      rewrite (vc_join_sym V1); repeat rewrite vc_join_assoc.
      rewrite (vc_join_sym V); auto.
  Qed.
  
  Instance vc_le_proper : Proper (vc_eq ==> vc_eq ==> iff) (@vc_le tid).
  Proof.
    repeat intro; split; repeat intro;
      specialize (H1 t); rewrite H, H0 in *; auto.
  Qed.

  Lemma drop_finite : forall V l l' (Hdrop : drop_le V l l')
    (Hfin : Forall (fun s => finite (snd s)) l),
    Forall (fun s => finite (snd s)) l'.
  Proof.
    intros; induction Hdrop; clarify.
    - inversion Hfin; clarify.
    - inversion Hfin; clarify.
  Qed.
  Hint Resolve drop_finite.

  Lemma drop_all : forall V Vs (Hle : Forall (fun s => vc_le (snd s) V) Vs),
    drop_le V Vs [].
  Proof.
    induction Vs; intros.
    - constructor.
    - inversion Hle; clarify.
      destruct a; constructor; auto.
  Qed.

  Lemma join_id_l : forall (V : vector_clock), vc_eq (vc_join vc_bot V) V.
  Proof.
    repeat intro; auto.
  Qed.

  Lemma join_id_r : forall (V : vector_clock), vc_eq (vc_join V vc_bot) V.
  Proof.
    repeat intro; setoid_rewrite Max.max_0_r; auto.
  Qed.

  Lemma finite_join : forall V V' (Hfin : finite V) (Hfin' : finite V'),
    finite (vc_join V V').
  Proof.
    intros ?? [x Hfin] [x' Hfin'].
    exists (x ++ x'); intros; rewrite in_app in *.
    specialize (Hfin t); specialize (Hfin' t); unfold vc_join; clarsimp.
  Qed.

  Lemma TS_sim1 : forall s1 tr s1' (Hsteps : step_star s1 tr s1') s2
    (*tr0 (Hroot : VC_step_star s0 tr0 s1) s2 (Hwf : well_formed s2)*)
    (Hsim : TS_sim s1 s2),
    exists s2', TS_step_star s2 tr s2' /\ TS_sim s1' s2'.
  Proof.
    intros ????; induction Hsteps; intros.
    { do 2 eexists; eauto; apply ss_refl. }
    assert (exists s2', TS_step s2 l s2' /\ TS_sim s' s2')
      as [s2' [Hstep' Hsim']].
    destruct s2 as (((C2, L2), R2), W2).
    clear Hsteps IHHsteps; inversion Hstep; clarify.
    - generalize (Hsim2222 x); intros (Hr & Hw & Hfinr & Hfinw).
      rewrite <- Hw, join_le in HW.
      generalize (finite_drop (C2 t) Hfinr); intros [? Hdrop].
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite <- Hr; split; [apply join_drop_le|]; clarify.
      constructor; eauto.
    - generalize (Hsim2222 x); intros (Hr & Hw & Hfinr & Hfinw).
      rewrite <- Hw, join_le in HW.
      rewrite <- Hr, join_le in HR.
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite join_id_r; clarify.
      split; constructor; eauto.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      apply finite_join; auto.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      split; clarify.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      apply finite_join; auto.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      apply finite_join; auto.
    - specialize (IHHsteps _ Hsim'); clarify; do 2 eexists; eauto; econstructor;
        eauto.
  Qed.

  Lemma TS_sim2 : forall s2 tr s2' (Hsteps : TS_step_star s2 tr s2') s1
    (*tr0 (Hroot : VC_step_star s0 tr0 s1) s2 (Hwf : well_formed s2)*)
    (Hsim : TS_sim s1 s2),
    exists s1', step_star s1 tr s1' /\ TS_sim s1' s2'.
  Proof.
    intros ????; induction Hsteps; intros.
    { do 2 eexists; eauto; apply ss_refl. }
    assert (exists s1', step s1 l s1' /\ TS_sim s1' s')
      as [s1' [Hstep' Hsim']].
    destruct s1 as (((C1, L1), R1), W1).
    clear Hsteps IHHsteps; inversion Hstep; clarify.
    - generalize (Hsim2222 x); intros (Hr & Hw & Hfinr & Hfinw).
      rewrite <- join_le, Hw in HW.
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite join_drop_le, Hr; clarify.
      constructor; eauto.
    - generalize (Hsim2222 x); intros (Hr & Hw & Hfinr & Hfinw).
      rewrite <- join_le, Hw in HW.
      rewrite <- join_le, Hr in HR.
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite join_id_r; clarify.
      split; constructor; eauto.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      split; clarify.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      apply finite_join; auto.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      apply finite_join; auto.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      apply finite_join; auto.
    - specialize (IHHsteps _ Hsim'); clarify; do 2 eexists; eauto; econstructor;
        eauto.
  Qed.

  Corollary TS_iff : forall tr, (exists s, TS_step_star s0 tr s) <->
      exists s, step_star VectorClocks.s0 tr s.
  Proof.
    split; intros [s Hs].
    - generalize (TS_sim2 Hs _ TS_sim0); clarify; eauto.
    - generalize (TS_sim1 Hs _ TS_sim0); clarify; eauto.
  Qed.

  Theorem TS_Correctness tr (Hfeasible : feasible tr) :
    race_free tr <-> exists s, TS_step_star s0 tr s.
  Proof.
    rewrite TS_iff; apply Correctness; auto.
  Qed.

End TSan.