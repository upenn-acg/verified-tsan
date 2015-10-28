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
     (HW : Forall (fun s => vc_le s (C t)) (map snd (W x)))
     (HR : drop_le (C t) (R x) Vs') (HR' : R' = upd R x ((t, C t) :: Vs')),
     TS_step (C, L, R, W) (rd t x) (C, L, R', W)
  | on_write : forall C L R W t x R' W'
     (* We must be able to drop all previous reads and writes *)
     (HR : Forall (fun s => vc_le s (C t)) (map snd (R x)))
     (HW : Forall (fun s => vc_le s (C t)) (map snd (W x)))
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

  Fixpoint join_list (ss : list vector_clock) :=
    match ss with
    | [] => vc_bot
    | V :: rest => vc_join V (join_list rest)
    end.

  Lemma vc_bot_le : forall (V : vector_clock), vc_le vc_bot V.
  Proof. unfold vc_bot; repeat intro; omega. Qed.
  Hint Resolve vc_bot_le.

  Lemma join_le : forall V ss, vc_le (join_list ss) V <->
    Forall (fun s => vc_le s V) ss.
  Proof.
    induction ss.
    - split; clarify.
    - simpl; rewrite vc_join_le, IHss; split; clarify.
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

  Definition finite_state (s : state) := match s with (C, L, W, R) =>
    (forall t, finite (C t)) /\ (forall m, finite (L m)) /\
    (forall x, Forall (fun s => finite (snd s)) (R x) /\
               Forall (fun s => finite (snd s)) (W x)) end.

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

  Lemma finite_s0 : finite_state s0.
  Proof. clarify. Qed.

  Lemma drop_finite : forall V l l' (Hdrop : drop_le V l l')
    (Hfin : Forall (fun s => finite (snd s)) l),
    Forall (fun s => finite (snd s)) l'.
  Proof.
    intros; induction Hdrop; clarify.
    - inversion Hfin; clarify.
    - inversion Hfin; clarify.
  Qed.
  Hint Resolve drop_finite.

  Lemma finite_join : forall V V' (Hfin : finite V) (Hfin' : finite V'),
    finite (vc_join V V').
  Proof.
    intros ?? [x Hfin] [x' Hfin'].
    exists (x ++ x'); intros; rewrite in_app in *.
    specialize (Hfin t); specialize (Hfin' t); unfold vc_join; clarsimp.
  Qed.

  Lemma finite_step : forall s a s' (Hstep : TS_step s a s')
    (Hfin : finite_state s), finite_state s'.
  Proof.
    intros; inversion Hstep; clarify.
    - specialize (Hfin22 x0); unfold upd; clarify.
      constructor; clarify.
      eapply drop_finite; eauto.
    - unfold upd; clarify.
      split; constructor; clarify.
    - unfold upd; repeat split; clarify; apply Hfin22.
    - unfold upd; clarify.
      apply finite_join; auto.
    - unfold upd; clarify.
      apply finite_join; auto.
    - unfold upd; clarify.
      apply finite_join; auto.
  Qed.

  Corollary finite_step_star : forall s tr s' (Hsteps : TS_step_star s tr s')
    (Hfin : finite_state s), finite_state s'.
  Proof.
    intros; induction Hsteps; clarify; eapply IHHsteps, finite_step; eauto.
  Qed.

  Definition TS_sim (s1 : VectorClocks.state) (s2 : state) := match s1, s2 with
    (C1, L1, R1, W1), (C2, L2, R2, W2) => C1 = C2 /\ L1 = L2 /\
    forall x, vc_eq (join_list (map snd (R2 x))) (R1 x) /\
              vc_eq (join_list (map snd (W2 x))) (W1 x) end.

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
    vc_eq (vc_join V (join_list (map snd l')))
          (vc_join (join_list (map snd l)) V).
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

  Lemma TS_sim1 : forall s1 tr s1' (Hsteps : step_star s1 tr s1')
    s2 (Hfin : finite_state s2) (Hsim : TS_sim s1 s2),
    exists s2', TS_step_star s2 tr s2' /\ TS_sim s1' s2'.
  Proof.
    intros ????; induction Hsteps; intros.
    { do 2 eexists; eauto; apply ss_refl. }
    assert (exists s2', TS_step s2 l s2' /\ TS_sim s' s2')
      as [s2' [Hstep' Hsim']].
    destruct s2 as (((C2, L2), R2), W2).
    clear Hsteps IHHsteps; inversion Hstep; clarify.
    - generalize (Hsim22 x); intros (Hr & Hw).
      rewrite <- Hw, join_le in HW.
      generalize (Hfin22 x); intros (Hfinw & Hfinr).
      generalize (finite_drop (C2 t) Hfinr); intros [? Hdrop].
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite <- Hr; apply join_drop_le; auto.
    - generalize (Hsim22 x); intros (Hr & Hw).
      rewrite <- Hw, join_le in HW.
      rewrite <- Hr, join_le in HR.
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite join_id_r; clarify.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - exploit finite_step; eauto; intro Hfin'.
      specialize (IHHsteps _ Hfin' Hsim'); clarify; do 2 eexists; eauto;
        econstructor; eauto.
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
    - generalize (Hsim22 x); intros (Hr & Hw).
      rewrite <- join_le, Hw in HW.
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite join_drop_le, Hr; clarify.
    - generalize (Hsim22 x); intros (Hr & Hw).
      rewrite <- join_le, Hw in HW.
      rewrite <- join_le, Hr in HR.
      do 2 eexists; [econstructor; eauto | unfold upd; clarify].
      rewrite join_id_r; clarify.
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - do 2 eexists; [econstructor; eauto | unfold upd; clarify].
    - specialize (IHHsteps _ Hsim'); clarify; do 2 eexists; eauto; econstructor;
        eauto.
  Qed.

  Corollary TS_iff : forall tr, (exists s, TS_step_star s0 tr s) <->
      exists s, step_star VectorClocks.s0 tr s.
  Proof.
    split; intros [s Hs].
    - generalize (TS_sim2 Hs _ TS_sim0); clarify; eauto.
    - generalize (TS_sim1 Hs _ finite_s0 TS_sim0); clarify; eauto.
  Qed.

  Theorem TS_Correctness tr (Hfeasible : feasible tr) :
    race_free tr <-> exists s, TS_step_star s0 tr s.
  Proof.
    rewrite TS_iff; apply Correctness; auto.
  Qed.

  Section Lockset.

  (* Abstract Hybrid TSan *)
  Variable (is_cond_var : lock -> bool).  

  Record segment := { th : tid; vc : vector_clock; ls : list lock }.

  Definition h_state := ((tid -> vector_clock * list lock) *
   (lock -> vector_clock) * (var -> list segment) * (var -> list segment))%type.

  Definition h_s0 : h_state := (fun t => (vc_inc t vc_bot, []), fun m => vc_bot,
    fun x => [], fun x => []).

  Definition make_seg C t := {| th := t; vc := fst (C t); ls := snd (C t) |}.

  Inductive drop_seg V : list segment -> list segment -> Prop :=
  | s_drop_nil : drop_seg V [] []
  | s_drop_drop s ss ss' (Hle : vc_le (vc s) V) (HVs : drop_seg V ss ss') :
      drop_seg V (s :: ss) ss'
  | s_drop_keep s ss ss' (Hnle : ~vc_le (vc s) V) (HVs : drop_seg V ss ss') :
      drop_seg V (s :: ss) (s :: ss').

  Definition upd_vc (C : tid -> vector_clock * list lock) t V :=
    upd C t (V, snd (C t)).

  Inductive hTS_step : h_state -> operation -> h_state -> Prop :=
  | h_on_read : forall C L R W t x ss' R' (HR : drop_seg (fst (C t)) (R x) ss')
     (HR' : R' = upd R x (make_seg C t :: ss'))
     (HW : Forall (fun sr => Forall (fun sw => vc_le (vc sw) (vc sr) \/
        exists m, In m (ls sw) /\ In m (ls sr)) (W x)) (R' x)),
     hTS_step (C, L, R, W) (rd t x) (C, L, R', W)
  | h_on_write : forall C L R W t x ssr' ssw' R' W'
     (HR : drop_seg (fst (C t)) (R x) ssr')
     (HR' : R' = upd R x (make_seg C t :: ssr'))
     (HW : drop_seg (fst (C t)) (W x) ssw')
     (HW' : W' = upd W x (make_seg C t :: ssw'))
     (HWW : Forall (fun sw1 => Forall (fun sw2 => sw1 = sw2 \/
        exists m, In m (ls sw1) /\ In m (ls sw2)) (W' x)) (W' x))
     (HWR : Forall (fun sr => Forall (fun sw => vc_le (vc sw) (vc sr) \/
        exists m, In m (ls sw) /\ In m (ls sr)) (W' x)) (R' x)),
     hTS_step (C, L, R, W) (wr t x) (C, L, R', W')
  | h_on_signal : forall C L R W t m L' C' (Hcond : is_cond_var m = true)
      (HL' : L' = upd L m (fst (C t)))
      (HC' : C' = upd_vc C t (vc_inc t (fst (C t)))),
     hTS_step (C, L, R, W) (rel t m) (C', L', R, W)
  | h_on_wait : forall C L R W t m C' (Hcond : is_cond_var m = true)
      (HC' : C' = upd_vc C t (vc_join (fst (C t)) (L m))),
     hTS_step (C, L, R, W) (acq t m) (C', L, R, W)
  | h_on_lock : forall C L R W t m C' (Hlock : is_cond_var m = false)
      (HC' : C' = upd C t (fst (C t), m :: snd (C t)))
      (* Is this okay? *) (Hfree : forall t, ~In m (snd (C t))),
     hTS_step (C, L, R, W) (acq t m) (C', L, R, W)
  | h_on_unlock : forall C L R W t m C' (Hlock : is_cond_var m = false)
      (HC' : C' = upd C t (vc_inc t (fst (C t)),
        filter (fun m' => negb (beq m' m)) (snd (C t))))
      (**) (Hheld : In m (snd (C t)) /\ forall t', In m (snd (C t')) -> t' = t),
     hTS_step (C, L, R, W) (rel t m) (C', L, R, W)
  | h_on_fork : forall C L R W t u C'
      (HC' : C' = upd_vc (upd_vc C u (vc_join (fst (C u)) (fst (C t))))
        t (vc_inc t (fst (C t)))),
     hTS_step (C, L, R, W) (fork t u) (C', L, R, W)
  | h_on_join : forall C L R W t u C'
      (HC' : C' = upd_vc (upd_vc C t (vc_join (fst (C t)) (fst (C u))))
        u (vc_inc u (fst (C u)))),
     hTS_step (C, L, R, W) (join t u) (C', L, R, W).

  Definition hTS_step_star := rtc hTS_step.

  Definition In_seg seg (s : h_state) := match s with (C, L, R, W) =>
    C (th seg) = (vc seg, ls seg) \/ exists x, In seg (R x) \/ In seg (W x) end.

  Definition h_well_formed (s : h_state) := match s with (C, L, R, W) =>
    (forall u t, t <> u -> fst (C u) t < fst (C t) t) /\
    (forall m t, L m t < fst (C t) t) /\
    (forall s x t, In s (R x) ->
       (vc s t < fst (C t) t \/ vc_le (vc s) (fst (C t)))) /\
    (forall s x t, In s (W x) ->
       (vc s t < fst (C t) t \/ vc_le (vc s) (fst (C t)))) /\
    (forall t, finite (fst (C t))) /\ (forall m, finite (L m)) /\
    (forall x, Forall (fun s => finite (vc s)) (R x) /\
               Forall (fun s => finite (vc s)) (W x)) /\
    (forall m, if is_cond_var m then forall seg, In_seg seg s -> ~In m (ls seg)
       else vc_eq (L m) vc_bot) /\
    (forall t1 t2 m, In m (snd (C t1)) -> In m (snd (C t2)) -> t1 = t2)
  end.

  Lemma h_wf0 : h_well_formed h_s0.
  Proof.
    unfold h_well_formed, h_s0; repeat split; intros; clarify;
      unfold vc_inc, vc_bot; clarify.
  Qed.

  Lemma drop_seg_in : forall V ss ss' s (Hdrop : drop_seg V ss ss'),
    In s ss' -> In s ss.
  Proof.
    intros; induction Hdrop; clarify.
  Qed.

  Instance vc_le_refl : Reflexive (vc_le(tid := tid)).
  Proof. repeat intro; auto. Qed.
  Hint Resolve vc_le_refl.

  Lemma vc_join_le_l : forall (V1 V2 : vector_clock), vc_le V1 (vc_join V1 V2).
  Proof.
    repeat intro; apply Max.le_max_l.
  Qed.

  Lemma drop_seg_finite : forall V ss ss' (Hdrop : drop_seg V ss ss')
    (Hfin : Forall (fun s => finite (vc s)) ss),
    Forall (fun s => finite (vc s)) ss'.
  Proof.
    intros; induction Hdrop; clarify; inversion Hfin; clarify.
  Qed.

  Lemma in_seg_upd : forall C L R W seg t e, In_seg seg (upd C t e, L, R, W) ->
    seg = {| th := t; vc := fst e; ls := snd e |} \/
    In_seg seg (C, L, R, W).
  Proof.
    clarify.
    unfold upd in *; clarify.
    left; destruct seg; clarify.
  Qed.

  Lemma in_seg_wf : forall C L R W seg t (Hwf : h_well_formed (C, L, R, W))
    (Hin : In_seg seg (C, L, R, W)),
    vc seg t < fst (C t) t \/ vc_le (vc seg) (fst (C t)).
  Proof.
    clarify.
    destruct Hin; clarify.
    - destruct (eq_dec t (th seg)); clarsimp.
      specialize (Hwf1 _ _ n); clarsimp.
    - destruct H; [eapply Hwf221 | eapply Hwf2221]; eauto.
  Qed.

  Lemma h_wf_step s s' a (Hwf : h_well_formed s) (Hstep : hTS_step s a s') : 
    h_well_formed s'.
  Proof.
    destruct s as (((C, L), R), W); 
      destruct Hwf as (Hthreads & Hlocks & Hread & Hwrite & Hfin);
      inversion Hstep; unfold upd in *; clarify.
    - split; clarify; [|split; clarify].
      + specialize (Hread s x0 t0); clarify.
        destruct H; clarify.
        * destruct (eq_dec t0 t); clarify.
        * exploit drop_seg_in; eauto.
      + split; [constructor|]; clarify; [|apply Hfin221].
        eapply drop_seg_finite; eauto; apply Hfin221.
      + specialize (Hfin2221 m); clarify.
        destruct (eq_dec x x0); clarify; eauto.
        apply Hfin2221; destruct H as [[? | ?] | ?]; clarify; eauto.
        * destruct (C t); auto.
        * exploit drop_seg_in; eauto.
    - split; [|split; clarify; [|split]]; clarify.
      + specialize (Hread s x0 t0); clarify.
        destruct H; clarify.
        * destruct (eq_dec t0 t); clarify.
        * exploit (drop_seg_in s HR); eauto.
      + specialize (Hwrite s x0 t0); clarify.
        destruct H; clarify.
        * destruct (eq_dec t0 t); clarify.
        * exploit drop_seg_in; eauto.
      + split; constructor; clarify; eapply drop_seg_finite; eauto;
          apply Hfin221.
      + specialize (Hfin2221 m); clarify.
        destruct (eq_dec x x0); clarify; eauto.
        apply Hfin2221; destruct H as [[? | ?] | [? | ?]]; clarify.
        * destruct (C t); auto.
        * exploit (drop_seg_in seg HR); eauto.
        * destruct (C t); auto.
        * exploit drop_seg_in; eauto.
    - unfold upd_vc in *; repeat split; clarify.
      + specialize (Hthreads _ _ H); unfold upd.
        destruct (eq_dec t u), (eq_dec t t0); unfold vc_inc; clarify.
      + specialize (Hlocks m0 t0); unfold upd.
        destruct (eq_dec m m0), (eq_dec t t0); unfold vc_inc; clarify.
      + specialize (Hread _ _ t0 H); unfold upd, vc_inc; clarify.
        right; intro; clarify.
      + specialize (Hwrite _ _ t0 H); unfold upd, vc_inc; clarify.
        right; intro; clarify.
      + unfold upd; clarify.
      + apply Hfin221.
      + apply Hfin221.
      + specialize (Hfin2221 m0); destruct (is_cond_var m0) eqn: Hm; clarify.
        unfold upd in *; clarify.
        specialize (Hfin2221 (make_seg C (th seg))); clarify.
        apply Hfin2221; destruct (C (th seg)); auto.
      + unfold upd in *; destruct (eq_dec t t1), (eq_dec t t2); clarify; eauto.
    - unfold upd_vc in *; repeat split; clarify.
      + specialize (Hthreads _ _ H); specialize (Hlocks m t0); unfold upd.
        destruct (eq_dec t u), (eq_dec t t0); unfold vc_join; clarify.
        * rewrite Nat.max_lub_lt_iff; auto.
        * rewrite Nat.max_lt_iff; auto.
      + specialize (Hlocks m0 t0); unfold upd.
        destruct (eq_dec m m0), (eq_dec t t0); unfold vc_join; clarify.
        * rewrite Nat.max_lt_iff; auto.
        * rewrite Nat.max_lt_iff; auto.
      + specialize (Hread _ _ t0 H); unfold upd, vc_join; clarify.
        rewrite Nat.max_lt_iff; clarify.
        right; etransitivity; eauto; apply vc_join_le_l.
      + specialize (Hwrite _ _ t0 H); unfold upd, vc_join; clarify.
        rewrite Nat.max_lt_iff; clarify.
        right; etransitivity; eauto; apply vc_join_le_l.
      + unfold upd; clarify.
        apply finite_join; auto.
      + apply Hfin221.
      + apply Hfin221.
      + specialize (Hfin2221 m0); destruct (is_cond_var m0) eqn: Hm; clarify.
        unfold upd in *; clarify.
        specialize (Hfin2221 (make_seg C (th seg))); clarify.
        apply Hfin2221; destruct (C (th seg)); auto.
      + unfold upd in *; destruct (eq_dec t t1), (eq_dec t t2); clarify; eauto.
    - repeat split; clarify.
      + specialize (Hthreads _ _ H).
        destruct (eq_dec t u), (eq_dec t t0); clarify.
      + specialize (Hread _ _ t0 H); clarify.
      + specialize (Hwrite _ _ t0 H); clarify.
      + apply Hfin221.
      + apply Hfin221.
      + specialize (Hfin2221 m0); destruct (is_cond_var m0) eqn: Hm; clarify.
        intro; destruct (eq_dec m m0); clarify.
        specialize (Hfin2221 (make_seg C (th seg))); clarify.
        use Hfin2221; clarify; destruct (C (th seg)); auto.
      + unfold upd in *; destruct (eq_dec t t1), (eq_dec t t2); clarify; eauto.
        * destruct H; clarify; eauto.
          specialize (Hfree t2); clarify.
        * destruct H0; clarify; eauto.
          specialize (Hfree t1); clarify.
    - repeat split; clarify.
      + specialize (Hthreads _ _ H).
        destruct (eq_dec t u), (eq_dec t t0); unfold vc_inc; clarify.
      + unfold vc_inc; specialize (Hlocks m0 t0); clarify.
      + unfold vc_inc; specialize (Hread _ _ t0 H); clarify.
        left; apply le_lt_n_Sm; auto.
      + unfold vc_inc; specialize (Hwrite _ _ t0 H); clarify.
        left; apply le_lt_n_Sm; auto.
      + apply Hfin221.
      + apply Hfin221.
      + specialize (Hfin2221 m0); destruct (is_cond_var m0) eqn: Hm; clarify.
        rewrite filter_In; intro; destruct (eq_dec m m0); clarify.
        specialize (Hfin2221 (make_seg C (th seg))); clarify.
        use Hfin2221; clarify; destruct (C (th seg)); auto.
      + unfold upd in *; destruct (eq_dec t t1), (eq_dec t t2); clarify;
          try (rewrite filter_In in *; clarify); eauto.
    - unfold upd_vc in *; repeat split; clarify.
      + generalize (Hthreads _ _ H); intro; unfold upd.
        destruct (eq_dec t u0), (eq_dec u t); unfold vc_inc, vc_join; clarify;
          destruct (eq_dec t0 u0), (eq_dec u0 t0); clarify.
        * rewrite Nat.max_lt_iff; auto.
        * destruct (eq_dec u u0), (eq_dec t t0); clarify;
            try (rewrite Nat.max_lub_lt_iff); try (rewrite Nat.max_lt_iff);
            clarify.
      + specialize (Hlocks m t0); unfold upd.
        destruct (eq_dec t t0); unfold vc_inc, vc_join; clarify.
        rewrite Nat.max_lt_iff; auto.
      + specialize (Hread _ _ t0 H); unfold upd.
        destruct (eq_dec t t0); unfold vc_inc, vc_join; clarify.
        * right; intro; clarify.
        * rewrite Nat.max_lt_iff; clarify.
          right; etransitivity; eauto; apply vc_join_le_l.          
      + specialize (Hwrite _ _ t0 H); unfold upd.
        destruct (eq_dec t t0); unfold vc_inc, vc_join; clarify.
        * right; intro; clarify.
        * rewrite Nat.max_lt_iff; clarify.
          right; etransitivity; eauto; apply vc_join_le_l.
      + unfold upd; clarify.
        apply finite_join; auto.
      + apply Hfin221.
      + apply Hfin221.
      + specialize (Hfin2221 m); clarify.
        specialize (Hfin2221 (make_seg C (th seg))); use Hfin2221.
        unfold upd in *; destruct (eq_dec t (th seg)), (eq_dec u (th seg));
          clarsimp.
        { destruct (C (th seg)); auto. }
      + unfold upd in *; destruct (eq_dec t t1), (eq_dec t t2); clarify;
          destruct (eq_dec u t1), (eq_dec u t2); clarify; eauto.
    - unfold upd_vc in *; repeat split; clarify.
      + generalize (Hthreads _ _ H); intro; unfold upd.
        destruct (eq_dec u u0); unfold vc_inc, vc_join; clarify;
          destruct (eq_dec t0 u0), (eq_dec u0 t0); clarify.
        * rewrite Nat.max_lt_iff; auto.
        * destruct (eq_dec t u0), (eq_dec u t0); clarify;
            try (rewrite Nat.max_lub_lt_iff); try (rewrite Nat.max_lt_iff);
            clarify.
      + specialize (Hlocks m t0); unfold upd.
        destruct (eq_dec u t0); unfold vc_inc, vc_join; clarify.
        rewrite Nat.max_lt_iff; auto.
      + specialize (Hread _ _ t0 H); unfold upd.
        destruct (eq_dec u t0); unfold vc_inc, vc_join; clarify.
        * right; intro; clarify.
        * rewrite Nat.max_lt_iff; clarify.
          right; etransitivity; eauto; apply vc_join_le_l.          
      + specialize (Hwrite _ _ t0 H); unfold upd.
        destruct (eq_dec u t0); unfold vc_inc, vc_join; clarify.
        * right; intro; clarify.
        * rewrite Nat.max_lt_iff; clarify.
          right; etransitivity; eauto; apply vc_join_le_l.          
      + unfold upd; clarify.
        apply finite_join; auto.
      + apply Hfin221.
      + apply Hfin221.
      + specialize (Hfin2221 m); clarify.
        specialize (Hfin2221 (make_seg C (th seg))); use Hfin2221.
        unfold upd in *; destruct (eq_dec t (th seg)), (eq_dec u (th seg));
          clarsimp.
        { destruct (C (th seg)); auto. }
      + unfold upd in *; destruct (eq_dec u t1), (eq_dec u t2); clarify;
          destruct (eq_dec t t1), (eq_dec t t2); clarify; eauto.
  Qed.

  Corollary hTS_step_star_wf s s' tr (Hwf : h_well_formed s) 
    (Hsteps : hTS_step_star s tr s') : h_well_formed s'.
  Proof.
    induction Hsteps; auto.
    apply IHHsteps; eapply h_wf_step; eauto.
  Qed.

  Lemma vc_le_antisym : forall (V1 V2 : vector_clock)
    (H1 : vc_le V1 V2) (H2 : vc_le V2 V1), vc_eq V1 V2.
  Proof.
    repeat intro; specialize (H1 t); specialize (H2 t); omega.
  Qed.

  Lemma vc_join_le_r : forall (V1 V2 : vector_clock), vc_le V2 (vc_join V1 V2).
  Proof.
    repeat intro; apply Max.le_max_r.
  Qed.

  Lemma drop_le_in_iff : forall V Vs Vs' V1 (Hdrop : drop_le V Vs Vs'),
    In V1 Vs' <-> In V1 Vs /\ ~vc_le (snd V1) V.
  Proof.
    intros; induction Hdrop; split; clarify; rewrite IHHdrop in *; clarify.
  Qed.    

  Lemma drop_seg_in_iff : forall V ss ss' s (Hdrop : drop_seg V ss ss'),
    In s ss' <-> In s ss /\ ~vc_le (vc s) V.
  Proof.
    intros; induction Hdrop; split; clarify; rewrite IHHdrop in *; clarify.
  Qed.

  Lemma map_upd_none : forall A (A_eq : EqDec_eq A) B (f g : A -> B) x l
    (Hnone : Forall (fun y => y <> x) l),
    map (fun y => if eq_dec x y then f y else g y) l = map g l.
  Proof.
    induction l; clarify.
    inversion Hnone; clarsimp.
  Qed.

  Instance vc_inc_proper : Proper (eq ==> vc_eq ==> vc_eq) vc_inc.
  Proof.
    repeat intro; unfold vc_inc; clarify.
  Qed.

  Lemma join_le' : forall Vs t x, join_list Vs t <= x <->
    Forall (fun V => V t <= x) Vs.
  Proof.
    induction Vs; split; clarify; unfold vc_join in *;
      rewrite Nat.max_lub_iff in *.
    - constructor; clarify; rewrite IHVs in *; auto.
    - rewrite IHVs; inversion H; clarify.
  Qed.

  (* Interestingly, this isn't needed for the correctness of TS itself. *)
  Definition TS_well_formed (s : state) := match s with (C, L, _, _) =>
    (forall t u, t <> u -> C u t < C t t) /\ (forall m t, L m t < C t t) end.

  Lemma TS_wf0 : TS_well_formed s0.
  Proof.
    split; clarify; unfold vc_inc, vc_bot; clarify.
  Qed.

  Lemma TS_wf_step : forall s a s' (Hstep : TS_step s a s')
    (Hwf : TS_well_formed s), TS_well_formed s'.
  Proof.
    intros; inversion Hstep; clarify.
    - split; unfold upd; clarify.
      + specialize (Hwf1 _ _ H); destruct (eq_dec t u), (eq_dec t t0);
          unfold vc_inc; clarify; omega.
      + specialize (Hwf2 m0 t0); destruct (eq_dec m m0), (eq_dec t t0);
          unfold vc_inc; clarify; omega.
    - split; unfold upd; clarify.
      + specialize (Hwf1 _ _ H); destruct (eq_dec t u), (eq_dec t t0);
          unfold vc_join; clarify.
        * rewrite Nat.max_lub_lt_iff; auto.
        * rewrite Nat.max_lt_iff; auto.
      + specialize (Hwf2 m0 t0); setoid_rewrite Nat.max_lt_iff; auto.
    - split; unfold upd; clarify.
      + destruct (eq_dec t u0), (eq_dec t t0); unfold vc_inc, vc_join; clarify.
        * destruct (eq_dec t0 u0); clarify.
          rewrite Nat.max_lt_iff; auto.
        * specialize (Hwf1 _ _ H); clarify.
          rewrite Nat.max_lub_lt_iff; auto.
        * destruct (eq_dec u u0), (eq_dec u t0); clarify.
          { rewrite Nat.max_lub_lt_iff; auto. }
          { rewrite Nat.max_lt_iff; auto. }
      + specialize (Hwf2 m t0); destruct (eq_dec t t0); unfold vc_join, vc_inc; 
          clarify.
        rewrite Nat.max_lt_iff; auto.
    - split; unfold upd; clarify.
      + destruct (eq_dec u u0), (eq_dec u t0); unfold vc_inc, vc_join; clarify.
        * destruct (eq_dec t0 u0); clarify.
          rewrite Nat.max_lt_iff; auto.
        * specialize (Hwf1 _ _ H); clarify.
          rewrite Nat.max_lub_lt_iff; auto.
        * destruct (eq_dec t u0), (eq_dec t t0); clarify.
          { rewrite Nat.max_lub_lt_iff; auto. }
          { rewrite Nat.max_lt_iff; auto. }
      + specialize (Hwf2 m t0); destruct (eq_dec u t0); unfold vc_join, vc_inc; 
          clarify.
        rewrite Nat.max_lt_iff; auto.
  Qed.

  Corollary TS_wf_step_star : forall s tr s' (Hsteps : TS_step_star s tr s')
    (Hwf : TS_well_formed s), TS_well_formed s'.
  Proof.
    intros; induction Hsteps; clarify; eapply IHHsteps, TS_wf_step; eauto.
  Qed.

  Lemma vc_inc_le : forall (V : vector_clock) t, vc_le V (vc_inc t V).
  Proof.
    repeat intro; unfold vc_inc; clarify.
  Qed.

  Lemma vc_join_mono : forall (V1 V2 V1' V2' : vector_clock)
    (Hle1 : vc_le V1 V1') (Hle2 : vc_le V2 V2'),
    vc_le (vc_join V1 V2) (vc_join V1' V2').
  Proof.
    intros; etransitivity; [apply vc_join_mono_l | apply vc_join_mono_r]; auto.
  Qed.

  Definition hTS_sim (s1 : h_state) (s2 : state) := match s1, s2 with
    (C1, L1, R1, W1), (C2, L2, R2, W2) =>
    (forall t, vc_le
      (join_list (fst (C1 t) :: map (fun m => L2 m) (snd (C1 t)))) (C2 t)) /\
    (forall t, fst (C1 t) t = C2 t t) /\ (forall m, vc_le (L1 m) (L2 m)) /\
    (forall m t, In m (snd (C1 t)) -> vc_le (L2 m) (C2 t)) /\
    (forall x t V,
     (In (t, V) (R2 x) -> exists s, In s (R1 x) /\ th s = t /\ vc_le (vc s) V /\
        (forall t', (vc s t <= fst (C1 t') t -> vc_le V (C2 t')) /\
           forall m, In m (ls s) -> In m (snd (C1 t')) -> vc_le V (C2 t')) /\
        (forall m, vc s t <= L1 m t -> vc_le V (L2 m)) /\
        (forall m, In m (ls s) -> In m (snd (C1 t)) \/ vc_le V (L2 m))) /\
     (In (t, V) (W2 x) -> exists s, In s (W1 x) /\ th s = t /\ vc_le (vc s) V /\
        (forall t', (vc s t <= fst (C1 t') t -> vc_le V (C2 t')) /\
           forall m, In m (ls s) -> In m (snd (C1 t')) -> vc_le V (C2 t')) /\
        (forall m, vc s t <= L1 m t -> vc_le V (L2 m)) /\
        (forall m, In m (ls s) -> In m (snd (C1 t)) \/ vc_le V (L2 m))))
  end.

  Lemma hTS_sim0 : hTS_sim h_s0 s0.
  Proof.
    repeat split; clarify.
    rewrite join_id_r; auto.
  Qed.
  
  Lemma filter_join_le : forall A f f' (l : list A),
    vc_le (join_list (map f (filter f' l))) (join_list (map f l)).
  Proof.
    induction l; clarify.
    destruct (f' a); clarify.
    - apply vc_join_mono_r; auto.
    - etransitivity; eauto; apply vc_join_le_r.
  Qed.

  Lemma vc_inc_mono : forall (V1 V2 : vector_clock) t, vc_le V1 V2 ->
    vc_le (vc_inc t V1) (vc_inc t V2).
  Proof.
    repeat intro; unfold vc_inc; clarify.
    specialize (H t); omega.
  Qed.

  Lemma hTS_sim1 : forall s1 tr s1' (Hsteps : hTS_step_star s1 tr s1')
    (Hwf : h_well_formed s1) s2 (Hsim : hTS_sim s1 s2)
    (Hwft : TS_well_formed s2) (Hfin : finite_state s2),
    exists s2', TS_step_star s2 tr s2' /\ hTS_sim s1' s2'.
  Proof.
    intros ????; induction Hsteps; intros.
    { do 2 eexists; eauto; apply ss_refl. }
    assert (exists s2', TS_step s2 l s2' /\ hTS_sim s' s2')
      as [s2' [Hstep' Hsim']].
    destruct s as (((C1, L1), R1), W1), s2 as (((C2, L2), R2), W2).
    destruct Hwf as (Hclock & Hlock & Hread & Hwrite & Hcfin & Hlfin &
      Hrwfin & Hcond & Hsep).
    destruct Hsim as (Hclock_le & Hthread & Hlock_le & Hhold & Hrw).
    clear Hsteps IHHsteps; inversion Hstep; clarify.
    - specialize (Hfin22 x); destruct Hfin22 as [_ ?].
      exploit finite_drop; eauto; clarify.
      do 2 eexists; [econstructor; eauto | clarify].
      + rewrite upd_new in HW; inversion HW as [|?? HC]; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[t' V] [? Hin]]; subst.
        specialize (Hrw x t' V); clarify.
        specialize (HC _ Hrw21); clarify.
        destruct HC; clarify.
        * apply Hrw22221; auto.
        * eapply Hrw22221; eauto.
      + repeat split; clarify.
        * specialize (Hrw x1 t0 V).
          unfold upd in *; destruct (eq_dec x x1); clarify;
            [|do 2 eexists; eauto].
          destruct H1; clarify.
          { do 2 eexists; eauto; clarify.
            split; [etransitivity; [apply vc_join_le_l | apply Hclock_le]|].
            repeat split; clarify.
            { destruct (eq_dec t0 t'); clarify.
              specialize (Hclock _ _ n); omega. }
            { specialize (Hsep t0 t' m); clarify. }
            { specialize (Hlock m t0); omega. } }
          rewrite drop_le_in_iff in H1; eauto; clarify.
          assert (In x ss').
          { rewrite drop_seg_in_iff; eauto; clarify.
            intro Hle; contradiction H12; apply Hrw12221; auto. }
          do 2 eexists; eauto.
        * apply Hrw; auto.
    - do 2 eexists; [econstructor; eauto | clarify].
      + repeat rewrite upd_new in HWR; inversion HWR as [|??? HR']; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[t' V] [? Hin]]; subst.
        specialize (Hrw x t' V); clarify.
        specialize (Hrwfin x); destruct Hrwfin as [Hfinr _].
        rewrite Forall_forall in Hfinr; specialize (Hfinr _ Hrw11).
        destruct (finite_le_dec (fst (C1 t)) Hfinr).
        * apply Hrw12221; auto.
        * exploit HR'.
          { rewrite drop_seg_in_iff; eauto. }
          rewrite Forall_forall; intro HR''.
          specialize (HR'' (make_seg C1 t)); clarify.
          specialize (Hread _ _ t Hrw11); clarify.
          assert (~vc_le (fst (C1 t)) (vc x0)).
          { intro Hle; specialize (Hle t); exploit le_not_lt; eauto. }
          clarify; eapply Hrw12221; eauto.
      + repeat rewrite upd_new in HWW; inversion HWW as [|??? HW']; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[t' V] [? Hin]]; subst.
        specialize (Hrw x t' V); clarify.
        specialize (Hrwfin x); destruct Hrwfin as [_ Hfinw].
        rewrite Forall_forall in Hfinw; specialize (Hfinw _ Hrw21).
        destruct (finite_le_dec (fst (C1 t)) Hfinw).
        * apply Hrw22221; auto.
        * exploit HW'.
          { rewrite drop_seg_in_iff; eauto. }
          rewrite Forall_forall; intro HW''.
          specialize (HW'' (make_seg C1 t)); clarify.
          destruct HW''; clarify.
          { contradiction H; auto. }
          eapply Hrw22221; eauto.
      + repeat split; clarify.
        * specialize (Hrw x0 t0 V).
          unfold upd in *; destruct (eq_dec x x0); clarify;
            [|do 2 eexists; eauto].
          do 2 eexists; eauto; clarify.
          split; [etransitivity; [apply vc_join_le_l | apply Hclock_le]|].
          repeat split; clarify.
          { destruct (eq_dec t0 t'); clarify.
            specialize (Hclock _ _ n); omega. }
          { specialize (Hsep t0 t' m); clarify. }
          { specialize (Hlock m t0); omega. }
        * specialize (Hrw x0 t0 V).
          unfold upd in *; destruct (eq_dec x x0); clarify;
            [|do 2 eexists; eauto].
          do 2 eexists; eauto; clarify.
          split; [etransitivity; [apply vc_join_le_l | apply Hclock_le]|].
          repeat split; clarify.
          { destruct (eq_dec t0 t'); clarify.
            specialize (Hclock _ _ n); omega. }
          { specialize (Hsep t0 t' m); clarify. }
          { specialize (Hlock m t0); omega. }
    - do 2 eexists; [econstructor; eauto | clarify].
      repeat split; clarify.
      + assert (Forall (fun m0 => m0 <> m) (snd (C1 t0))).
        { rewrite Forall_forall; repeat intro; subst.
          specialize (Hcond m); clarify.
          specialize (Hcond (make_seg C1 t0)); use Hcond; clarify.
          destruct (C1 t0); auto. }
        unfold upd_vc, upd; destruct (eq_dec t t0);
          rewrite (map_upd_none _ _ (fun m => L2 m)); clarify.
        intro t; unfold vc_inc, vc_join; destruct (eq_dec t t0);
          [subst | apply Hclock_le; auto].
        rewrite Hthread, Max.max_l; auto.
        rewrite join_le', Forall_forall; intros.
        rewrite in_map_iff in *; clarify.
        specialize (Hwft2 x0 t0); omega.
      + unfold upd_vc, upd, vc_inc; clarify.
      + unfold upd; clarify.
        etransitivity; [apply vc_join_le_l | apply Hclock_le].
      + specialize (Hhold m0 t0); use Hhold; unfold upd_vc, upd in *; clarify.
        destruct (eq_dec m m0); clarify.
        * destruct (eq_dec t t0); clarify; [apply vc_inc_le|].
          specialize (Hcond m0); clarify.
          specialize (Hcond (make_seg C1 t0)); use Hcond; clarify.
          destruct (C1 t0); auto.
        * etransitivity; eauto; apply vc_inc_le.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw12221 t').
          unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          etransitivity; [|apply vc_inc_le].
          apply Hrw122211.
          specialize (Hread _ _ t' Hrw11); clarify.
          unfold vc_inc in H0; clarify; omega.
        * specialize (Hrw12221 t'); clarify.
          specialize (Hrw122212 m0); clarify; use Hrw122212.
          etransitivity; eauto; unfold upd; clarify; apply vc_inc_le.
          { unfold upd_vc, upd in *; clarify. }
        * unfold upd in *; clarify.
          apply Hrw12221; auto.
        * specialize (Hrw122222 m0); clarify.
          unfold upd_vc, upd; destruct Hrw122222; [left | right]; clarify.
          specialize (Hcond m0); clarify.
          specialize (Hcond x0); use Hcond; clarify; eauto.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw22221 t').
          unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          etransitivity; [|apply vc_inc_le].
          apply Hrw222211.
          specialize (Hwrite _ _ t' Hrw21); clarify.
          unfold vc_inc in H0; clarify; omega.
        * specialize (Hrw22221 t'); clarify.
          specialize (Hrw222212 m0); clarify; use Hrw222212.
          etransitivity; eauto; unfold upd; clarify; apply vc_inc_le.
          { unfold upd_vc, upd in *; clarify. }
        * unfold upd in *; clarify.
          apply Hrw22221; auto.
        * specialize (Hrw222222 m0); clarify.
          unfold upd_vc, upd; destruct Hrw222222; [left | right]; clarify.
          specialize (Hcond m0); clarify.
          specialize (Hcond x0); use Hcond; clarify; eauto.
    - do 2 eexists; [econstructor; eauto | clarify].
      repeat split; clarify.
      + unfold upd_vc, upd; clarify.
        rewrite vc_join_assoc, (vc_join_sym (L1 m)).
        rewrite <- vc_join_assoc.
        apply vc_join_mono; auto.
      + unfold upd_vc, upd; clarify.
        setoid_rewrite Max.max_l; auto.
        * specialize (Hlock m t0); omega.
        * specialize (Hwft2 m t0); omega.
      + unfold upd_vc, upd in *; clarify.
        etransitivity; [apply Hhold | apply vc_join_le_l]; auto.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw12221 t').
          unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          setoid_rewrite Nat.max_le_iff in H0; destruct H0.
          { etransitivity; [|apply vc_join_le_l].
            apply Hrw122211; auto. }
          { etransitivity; [|apply vc_join_le_r].
            apply Hrw122221; auto. }
        * unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify;
            [|eapply Hrw12221; eauto].
          specialize (Hrw12221 t'); clarify.
          specialize (Hrw122212 m0); clarify.
          etransitivity; [eauto | apply vc_join_le_l].
        * unfold upd_vc, upd; clarify.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw22221 t').
          unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          setoid_rewrite Nat.max_le_iff in H0; destruct H0.
          { etransitivity; [|apply vc_join_le_l].
            apply Hrw222211; auto. }
          { etransitivity; [|apply vc_join_le_r].
            apply Hrw222221; auto. }
        * unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify;
            [|eapply Hrw22221; eauto].
          specialize (Hrw22221 t'); clarify.
          specialize (Hrw222212 m0); clarify.
          etransitivity; [eauto | apply vc_join_le_l].
        * unfold upd_vc, upd; clarify.
    - do 2 eexists; [econstructor; eauto | clarify].
      repeat split; clarify.
      + unfold upd; clarify.
        rewrite (vc_join_sym (L2 m)); rewrite <- vc_join_assoc.
        apply vc_join_mono_l; auto.
      + unfold upd; clarify.
        setoid_rewrite Max.max_l; auto.
        specialize (Hwft2 m t0); omega.
      + unfold upd in *; clarify.
        destruct H; [clarify; apply vc_join_le_r|].
        etransitivity; [apply Hhold | apply vc_join_le_l]; auto.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw12221 t').
          unfold upd in *; destruct (eq_dec t t'); clarify.
          etransitivity; [|apply vc_join_le_l].
          apply Hrw122211; auto.
        * unfold upd in *; destruct (eq_dec t t'); clarify;
            [|eapply Hrw12221; eauto].
          destruct H1; clarify.
          { specialize (Hrw122222 m0); specialize (Hfree (th x0)); clarify.
            etransitivity; [eauto | apply vc_join_le_r]. }
          { specialize (Hrw12221 t'); clarify.
            specialize (Hrw122212 m0); clarify.
            etransitivity; [eauto | apply vc_join_le_l]. }
        * unfold upd; clarify.
          specialize (Hrw122222 m0); clarify.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw22221 t').
          unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          etransitivity; [|apply vc_join_le_l].
          apply Hrw222211; auto.
        * unfold upd in *; destruct (eq_dec t t'); clarify;
            [|eapply Hrw22221; eauto].
          destruct H1; clarify.
          { specialize (Hrw222222 m0); specialize (Hfree (th x0)); clarify.
            etransitivity; [eauto | apply vc_join_le_r]. }
          { specialize (Hrw22221 t'); clarify.
            specialize (Hrw222212 m0); clarify.
            etransitivity; [eauto | apply vc_join_le_l]. }
        * unfold upd; clarify.
          specialize (Hrw222222 m0); clarify.
    - do 2 eexists; [econstructor; eauto | clarify].
      repeat split; clarify.
      + unfold upd; destruct (eq_dec t t0);
          rewrite (map_upd_none _ _ (fun m => L2 m)); clarify.
        etransitivity; [|apply vc_inc_mono, Hclock_le].
        intro; unfold vc_inc, vc_join; destruct (eq_dec t t0);
          [|clarify; apply vc_join_mono_r, filter_join_le].
        repeat rewrite Max.max_l; auto.
        * rewrite join_le', Forall_forall, Hthread; intros.
          rewrite in_map_iff in *; clarify.
          specialize (Hwft2 x0 t0); omega.
        * rewrite join_le', Forall_forall, Hthread; intros.
          rewrite in_map_iff in *; clarify.
          specialize (Hwft2 x0 t0); omega.
        * apply filter_Forall; unfold negb, beq; clarify.
        * specialize (Hheld2 t0); rewrite Forall_forall; repeat intro; clarify.
      + unfold upd, vc_inc; clarify.
      + unfold upd; clarify.
        etransitivity; eauto.
      + specialize (Hhold m0 t0); unfold upd in *; destruct (eq_dec t t0);
          clarify.
        * rewrite filter_In in *; clarify.
          destruct (eq_dec m m0); [|etransitivity; eauto]; apply vc_inc_le.
        * specialize (Hheld2 t0); clarify.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw12221 t').
          unfold upd in *; destruct (eq_dec t t'); clarify.
          etransitivity; [|apply vc_inc_le].
          unfold vc_inc in *; destruct (eq_dec (th x0) t');
            apply Hrw122211; auto.
          subst; specialize (Hread _ _ (th x0) Hrw11); clarify; omega.
        * unfold upd in *; destruct (eq_dec t t'); clarify;
            [|eapply Hrw12221; eauto].
          etransitivity; [|apply vc_inc_le].
          rewrite filter_In in *; clarify.
          eapply Hrw12221; eauto.
        * unfold upd; clarify.
          etransitivity; [apply Hrw122221 | apply Hhold]; eauto.
        * specialize (Hrw122222 m0); clarify.
          unfold upd; destruct (eq_dec m m0); [right|]; clarify.
          { eapply Hrw12221; eauto. }
          { left; rewrite filter_In; unfold negb, beq; clarify. }
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * specialize (Hrw22221 t').
          unfold upd in *; destruct (eq_dec t t'); clarify.
          etransitivity; [|apply vc_inc_le].
          unfold vc_inc in *; destruct (eq_dec (th x0) t');
            apply Hrw222211; auto.
          subst; specialize (Hwrite _ _ (th x0) Hrw21); clarify; omega.
        * unfold upd in *; destruct (eq_dec t t'); clarify;
            [|eapply Hrw22221; eauto].
          etransitivity; [|apply vc_inc_le].
          rewrite filter_In in *; clarify.
          eapply Hrw22221; eauto.
        * unfold upd; clarify.
          etransitivity; [apply Hrw222221 | apply Hhold]; eauto.
        * specialize (Hrw222222 m0); clarify.
          unfold upd; destruct (eq_dec m m0); [right|]; clarify.
          { eapply Hrw22221; eauto. }
          { left; rewrite filter_In; unfold negb, beq; clarify. }
    - do 2 eexists; [econstructor; eauto | clarify].
      repeat split; clarify.
      + unfold upd_vc, upd; destruct (eq_dec t t0); clarify.
        * intro; unfold vc_join, vc_inc; destruct (eq_dec t t0).
          { rewrite Hthread, Max.max_l; auto.
            rewrite join_le', Forall_forall; intros.
            rewrite in_map_iff in *; clarify.
            specialize (Hwft2 x0 t0); omega. }
          { destruct (eq_dec u t0); clarify; apply Hclock_le. }
        * rewrite vc_join_assoc, (vc_join_sym (fst (C1 t))).
          rewrite <- vc_join_assoc; apply vc_join_mono; auto.
          etransitivity; [apply vc_join_le_l | apply Hclock_le].
      + unfold upd_vc, upd; destruct (eq_dec t t0); unfold vc_inc; clarify.
        setoid_rewrite Max.max_l; auto.
        * specialize (Hclock t t0); clarify; omega.
        * specialize (Hwft1 t0 t); clarify; omega.
      + specialize (Hhold m t0); use Hhold.
        etransitivity; eauto; unfold upd; destruct (eq_dec t t0); clarify;
          [apply vc_inc_le | apply vc_join_le_l].
        { unfold upd_vc, upd in *; destruct (eq_dec t t0); clarify. }
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          { etransitivity; [|apply vc_inc_le].
            unfold vc_inc in *; destruct (eq_dec (th x0) t');
              apply Hrw12221; auto.
            subst; specialize (Hread _ _ (th x0) Hrw11); clarify; omega. }
          { generalize (Hrw12221 t'); clarify.
            setoid_rewrite Nat.max_le_iff in H0; destruct H0.
            { etransitivity; [apply Hrw12221 | apply vc_join_le_l]; auto. }
            { etransitivity; [apply Hrw12221 | apply vc_join_le_r]; auto. } }
        * unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify;
            destruct (eq_dec u t'); clarify.
          { etransitivity; [eapply Hrw12221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw12221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw12221; eauto | apply vc_join_le_l]. }
          { eapply Hrw12221; eauto. }
        * unfold upd_vc, upd; destruct (eq_dec t (th x0)); clarify.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify.
          { etransitivity; [|apply vc_inc_le].
            unfold vc_inc in *; destruct (eq_dec (th x0) t');
              apply Hrw22221; auto.
            subst; specialize (Hwrite _ _ (th x0) Hrw21); clarify; omega. }
          { generalize (Hrw22221 t'); clarify.
            setoid_rewrite Nat.max_le_iff in H0; destruct H0.
            { etransitivity; [apply Hrw22221 | apply vc_join_le_l]; auto. }
            { etransitivity; [apply Hrw22221 | apply vc_join_le_r]; auto. } }
        * unfold upd_vc, upd in *; destruct (eq_dec t t'); clarify;
            destruct (eq_dec u t'); clarify.
          { etransitivity; [eapply Hrw22221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw22221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw22221; eauto | apply vc_join_le_l]. }
          { eapply Hrw22221; eauto. }
        * unfold upd_vc, upd; destruct (eq_dec t (th x0)); clarify.
    - do 2 eexists; [econstructor; eauto | clarify].
      repeat split; clarify.
      + unfold upd_vc, upd; destruct (eq_dec u t0); clarify.
        * intro; unfold vc_join, vc_inc; destruct (eq_dec t1 t0).
          { rewrite Hthread, Max.max_l; auto.
            rewrite join_le', Forall_forall; intros.
            rewrite in_map_iff in *; clarify.
            specialize (Hwft2 x0 t0); omega. }
          { destruct (eq_dec t t0); clarify; apply Hclock_le. }
        * rewrite vc_join_assoc, (vc_join_sym (fst (C1 u))).
          rewrite <- vc_join_assoc; apply vc_join_mono; auto.
          etransitivity; [apply vc_join_le_l | apply Hclock_le].
      + unfold upd_vc, upd; destruct (eq_dec u t0); unfold vc_inc; clarify.
        setoid_rewrite Max.max_l; auto.
        * specialize (Hclock u t0); clarify; omega.
        * specialize (Hwft1 t0 u); clarify; omega.
      + specialize (Hhold m t0); use Hhold.
        etransitivity; eauto; unfold upd; destruct (eq_dec u t0); clarify;
          [apply vc_inc_le | apply vc_join_le_l].
        { unfold upd_vc, upd in *; destruct (eq_dec u t0); clarify. }
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * unfold upd_vc, upd in *; destruct (eq_dec u t'); clarify.
          { etransitivity; [|apply vc_inc_le].
            unfold vc_inc in *; destruct (eq_dec (th x0) t');
              apply Hrw12221; auto.
            subst; specialize (Hread _ _ (th x0) Hrw11); clarify; omega. }
          { generalize (Hrw12221 t'); clarify.
            setoid_rewrite Nat.max_le_iff in H0; destruct H0.
            { etransitivity; [apply Hrw12221 | apply vc_join_le_l]; auto. }
            { etransitivity; [apply Hrw12221 | apply vc_join_le_r]; auto. } }
        * unfold upd_vc, upd in *; destruct (eq_dec u t'); clarify;
            destruct (eq_dec t t'); clarify.
          { etransitivity; [eapply Hrw12221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw12221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw12221; eauto | apply vc_join_le_l]. }
          { eapply Hrw12221; eauto. }
        * unfold upd_vc, upd; destruct (eq_dec u (th x0)); clarify.
      + specialize (Hrw x t0 V); clarify.
        do 2 eexists; eauto; clarify.
        repeat split; clarify.
        * unfold upd_vc, upd in *; destruct (eq_dec u t'); clarify.
          { etransitivity; [|apply vc_inc_le].
            unfold vc_inc in *; destruct (eq_dec (th x0) t');
              apply Hrw22221; auto.
            subst; specialize (Hwrite _ _ (th x0) Hrw21); clarify; omega. }
          { generalize (Hrw22221 t'); clarify.
            setoid_rewrite Nat.max_le_iff in H0; destruct H0.
            { etransitivity; [apply Hrw22221 | apply vc_join_le_l]; auto. }
            { etransitivity; [apply Hrw22221 | apply vc_join_le_r]; auto. } }
        * unfold upd_vc, upd in *; destruct (eq_dec u t'); clarify;
            destruct (eq_dec t t'); clarify.
          { etransitivity; [eapply Hrw22221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw22221; eauto | apply vc_inc_le]. }
          { etransitivity; [eapply Hrw22221; eauto | apply vc_join_le_l]. }
          { eapply Hrw22221; eauto. }
        * unfold upd_vc, upd; destruct (eq_dec u (th x0)); clarify.
    - exploit IHHsteps; eauto.
      { eapply h_wf_step; eauto. }
      { eapply TS_wf_step; eauto. }
      { eapply finite_step; eauto. }
      clarify; do 2 eexists; [econstructor|]; eauto.
  Qed.
          
  Theorem h_Soundness tr (Hfeasible : feasible tr) :
    forall s', hTS_step_star h_s0 tr s' -> race_free tr.
  Proof.
    intros.
    rewrite TS_Correctness; auto.
    generalize (hTS_sim1 H h_wf0 _ hTS_sim0 TS_wf0 finite_s0); clarify; eauto.
  Qed.

  End Lockset.

End TSan.