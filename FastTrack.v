Require Import List.
Require Import CoqEqDec.
Require Import Util.
Require Import Arith.
Require Import Wf_nat.
Import ListNotations.

Set Implicit Arguments.

Section FastTrack.
  Variables (tid var lock : Type) 
    (tid_eq : EqDec_eq tid) (var_eq : EqDec_eq var) (lock_eq : EqDec_eq lock).

  (* Basic definitions (Section 2) *)
  Inductive operation :=
  | rd (t : tid) (x : var)
  | wr (t : tid) (x : var)
  | acq (t : tid) (m : lock)
  | rel (t : tid) (m : lock)
  | fork (t : tid) (u : tid)
  | join (t : tid) (u : tid).

  Instance op_eq : EqDec_eq operation.
  Proof. eq_dec_inst. Qed.

  Definition trace := list operation.

  Definition thread_of a := match a with
  | rd t _ => t
  | wr t _ => t
  | acq t _ => t
  | rel t _ => t
  | fork t _ => t
  | join t _ => t
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
(*      (Hfj : fjs a (thread_of b) \/ fjs b (thread_of a))
    Most of the feasibility conditions of FastTrack serve solely to produce
    the following looser definition of fork-join synchronization. *)
      t (Ha : uses_thread a t) (Hb : uses_thread b t)
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
  

  (* The FastTrack algorithm (Section 3) *)
  Definition epoch := (nat * tid)%type.
  Variable t0 : tid.
  Definition e_bot : epoch := (0, t0).
  Definition e_le (e : epoch) V := match e with (c, t) => c <= V t end.

  Inductive epoch_or_vc := VC (v : vector_clock) | E (e : epoch).
  Definition state := ((tid -> vector_clock) * (lock -> vector_clock) *
    (var -> epoch_or_vc) * (var -> epoch))%type.
  Definition s0 : state := (fun t => vc_inc t vc_bot, fun m => vc_bot,
    fun x => E e_bot, fun x => e_bot).

  Definition upd {A B} {A_eq : EqDec_eq A} (f : A -> B) x v y := 
    if eq_dec x y then v else f y.

  Definition e_of (C : tid -> vector_clock) t : epoch := (C t t, t).

  Inductive step : state -> operation -> state -> Prop :=
  | read_same_epoch : forall C L R W t x (HR :  R x = E (e_of C t)),
     step (C, L, R, W) (rd t x) (C, L, R, W)
  | read_shared : forall C L R W t x V R' (HR : R x = VC V)
      (HW : e_le (W x) (C t)) (HR' : R' = upd R x (VC (upd V t (C t t)))),
     step (C, L, R, W) (rd t x) (C, L, R', W)
  | read_exclusive : forall C L R W t x e R' (HR : R x = E e)
      (Hle : e_le e (C t)) (HW : e_le (W x) (C t))
      (HR' : R' = upd R x (E (e_of C t))),
     step (C, L, R, W) (rd t x) (C, L, R', W)
  | read_share : forall C L R W t x c u V R' (HR : R x = E (c, u))
      (Ht : u <> t) (HW : e_le (W x) (C t))
      (HV : V = upd (upd vc_bot t (C t t)) u c)
      (HR' : R' = upd R x (VC V)),
     step (C, L, R, W) (rd t x) (C, L, R', W)
  | write_same_epoch : forall C L R W t x (HW : W x = e_of C t),
     step (C, L, R, W) (wr t x) (C, L, R, W)
  | write_exclusive : forall C L R W t x e W' (HR : R x = E e)
      (Hle : e_le e (C t)) (HW : e_le (W x) (C t))
      (HW' : W' = upd W x (e_of C t)),
     step (C, L, R, W) (wr t x) (C, L, R, W')
  | write_shared : forall C L R W t x V R' W' (HR : R x = VC V)
      (Hle : vc_le V (C t)) (HW : e_le (W x) (C t))
      (HW' : W' = upd W x (e_of C t)) (HR' : R' = upd R x (E e_bot)),
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

  (* s =>tr s' *)
  Inductive step_star s : trace -> state -> Prop :=
  | ss_refl : step_star s [] s
  | ss_step : forall a s' tr s'', step s a s' -> step_star s' tr s'' ->
      step_star s (a :: tr) s''.

  Definition e_app (e : epoch) u := let (c, t) := e in 
    if eq_dec t u then c else 0.

  Definition app x u := match x with
  | VC V => V u
  | E e => e_app e u
  end.


  (* Correctness (Appendix A) *)
  (* Supporting definitions and lemmas *)
  Definition well_formed (s : state) := match s with (C, L, R, W) =>
    (forall u t, t <> u -> C u t < C t t) /\
    (forall m t, L m t < C t t) /\
    (forall x t, app (R x) t <= C t t) /\
    (forall x t, e_app (W x) t <= C t t) end.

  (* Lemma 1 *)
  Lemma wf0 : well_formed s0.
  Proof.
    unfold well_formed, s0; repeat split; intros; unfold vc_inc, vc_bot;
      clarify.
  Qed.

  Hint Resolve Le.le_0_n.
  Ltac dec_eq := match goal with 
    | |- context[eq_dec ?a ?b] => destruct (eq_dec a b); clarify
    | [H : context[eq_dec ?a ?b] |- _] => destruct (eq_dec a b); clarify end.

  Definition max_lt := NPeano.Nat.max_lub_lt.

  Lemma lt_max_l : forall n m p, p < n -> p < max n m.
  Proof. intros; rewrite NPeano.Nat.max_lt_iff; auto. Qed.

  Lemma lt_max_r : forall n m p, p < m -> p < max n m.
  Proof. intros; rewrite NPeano.Nat.max_lt_iff; auto. Qed.

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

  (* Lemma 2 *)
  Lemma wf_preservation s s' a (Hwf : well_formed s) (Hstep : step s a s') : 
    well_formed s'.
  Proof.
    destruct s as (((C, L), R), W); 
      destruct Hwf as [Hthreads [Hlocks [Hread Hwrite]]]; 
      inversion Hstep; clarify; unfold upd; repeat dec_eq.
    - specialize (Hread x0 t1); rewrite HR in Hread; clarify.
    - specialize (Hread x0 t1); rewrite HR in Hread; clarify.
    - split; intros; repeat dec_eq.
    - repeat split; intros; repeat dec_eq; try join_solve.
    - repeat split; intros; repeat dec_eq; try join_solve.
    - repeat split; intros; repeat dec_eq; repeat join_solve.
    - repeat split; intros; repeat dec_eq; repeat join_solve.
  Qed.

  Corollary step_star_wf s s' tr (Hwf : well_formed s) 
    (Hsteps : step_star s tr s') : well_formed s'.
  Proof.
    induction Hsteps; auto.
    apply IHHsteps; eapply wf_preservation; eauto.
  Qed.

  Lemma step_star_inv : forall tr s s' a s'' (Hsteps : step_star s tr s')
    (Hstep : step s' a s''), step_star s (tr ++ [a]) s''.
  Proof.
    intros; induction Hsteps; clarify.
    - econstructor; eauto; constructor.
    - econstructor; eauto.
  Qed.

  Lemma step_star_rev_inv : forall tr s s' a 
    (Hsteps : step_star s (tr ++ [a]) s'),
    exists s'', step_star s tr s'' /\ step s'' a s'.
  Proof.
    induction tr; clarify.
    - inversion Hsteps as [|? ? ? ? ? Hsteps']; clarify.
      inversion Hsteps'; clarify.
      eexists; split; [apply ss_refl | auto].
    - inversion Hsteps as [|? ? ? ? ? Hsteps']; clarify.
      specialize (IHtr _ _ _ Hsteps'); clarify.
      eexists; split; [eapply ss_step; eauto | eauto].
  Qed.

  Lemma step_star_app_inv : forall tr1 tr2 s s', step_star s (tr1 ++ tr2) s' ->
    exists s'', step_star s tr1 s'' /\ step_star s'' tr2 s'.
  Proof.
    induction tr1; clarify.
    - eexists; split; eauto; apply ss_refl.
    - inversion H as [| ? ? ? ? Ha Hsteps]; clarify.
      specialize (IHtr1 _ _ _ Hsteps); clarify.
      eexists; split; [econstructor|]; eauto.
  Qed.

  Definition clock_of (s : state) := match s with (C, _, _, _) => C end.
  Definition lock_of (s : state) := match s with (_, L, _, _) => L end.
  Definition read_of (s : state) := match s with (_, _, R, _) => R end.
  Definition write_of (s : state) := match s with (_, _, _, W) => W end.

  Lemma clock_mono : forall s s' tr (Hsteps : step_star s tr s') u t,
    clock_of s u t <= clock_of s' u t.
  Proof.
    intros; induction Hsteps; auto.
    inversion H; unfold upd, vc_inc, vc_join in *; clarify; dec_eq; try omega;
      eapply Max.max_lub_l; eauto.
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
    (Hfork : forall i t u (Hi : nth_error tr i = Some (fork t u))
       j a (Hle : j <= i) (Hj : nth_error tr j = Some a), ~uses_thread a u)
    (Hjoin : forall i t u (Hi : nth_error tr i = Some (join t u))
       j a (Hle : i <= j) (Hj : nth_error tr j = Some a), ~uses_thread a u).

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
      specialize (Hfork j); rewrite nth_error_app in Hfork; clarify.
    - specialize (Hjoin i t u); rewrite nth_error_app in Hjoin; clarify.
      specialize (Hjoin j); rewrite nth_error_app in Hjoin; clarify.
  Qed.

  Lemma lock_no_rel : forall s tr s' m (Hsteps : step_star s tr s')
    (Hno_rel : Forall (fun a => forall t, a <> rel t m) tr),
    lock_of s' m = lock_of s m.
  Proof.
    intros; induction Hsteps; clarify.
    inversion Hno_rel as [| ? ? Ha]; clarify.
    inversion H; clarify.
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
    generalize (step_star_app_inv _ _ Hsteps); intros [s'' Hs'']; clarify.
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
      specialize (Hj22 t1); rewrite nth_error_app, Hk2 in Hj22; intro; clarify.
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
    generalize (step_star_rev_inv _ _ Hsteps); intros [s'' [Htr Hx]].
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
      + destruct (eq_dec t1 u); clarify.
        generalize (Max.max_spec (C u t) (C t1 t));
          intros [[? Hmax] | [? Hmax]]; rewrite Hmax in *; try omega.
        destruct (eq_dec t1 t); subst.
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
      destruct (eq_dec t1 t); subst.
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

  (* Lemma 3 *)
  Lemma clocks_hb sa a tr sb b (*sb'*) : forall (Hwf : well_formed sa)
    (Hsteps : step_star sa (a :: tr) sb)(* (Hstep : step sb b sb')*)
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
          rewrite <- NPeano.Nat.succ_lt_mono, nth_error_app in *; clarify.
        * apply nth_error_split.
        * eauto.
        * unfold uses_thread; auto.
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

  Lemma read_clock : forall s t x s' (Hstep : step s (rd t x) s'),
    app (read_of s' x) t = clock_of s' t t.
  Proof.
    intros; inversion Hstep; unfold upd in *; clarsimp.
  Qed.
      
  Lemma write_clock : forall s t x s' (Hstep : step s (wr t x) s'),
    e_app (write_of s' x) t = clock_of s' t t.
  Proof.
    intros; inversion Hstep; unfold upd in *; clarsimp.
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
  
  (* Invariants:
     The read clock is >= all of the clocks of reads performed since the last
     write.
     The write clock is exactly equal to the timestamp of the last write. *)

  Instance epoch_eq : EqDec_eq epoch.
  Proof. eq_dec_inst. Qed.

  Definition writesb a x := match a with wr _ y => beq x y | _ => false end.

  Opaque minus.

  Definition last_write tr x := find_index (fun a => writesb a x) (rev tr).

  Lemma write_last : forall tr s s' x n t (Hsteps : step_star s tr s')
    (Hx : write_of s' x = (n, t)) (Hwf : well_formed s),
    match last_write tr x with
    | Some i => nth_error tr (length tr - i - 1) = Some (wr t x) /\
        exists sw, step_star s (firstn (length tr - i - 1) tr) sw /\
        clock_of sw t t = n /\ step_star sw (skipn (length tr - i - 1) tr) s'
    | None => write_of s x = (n, t)
    end.
  Proof.
    induction tr; intros; inversion Hsteps as [| ? ? ? ? Ha Htr]; clarify.
    generalize (wf_preservation Hwf Ha); intro Hwf'.
    specialize (IHtr _ _ _ _ _ Htr Hx Hwf').
    unfold last_write in *; simpl; rewrite find_index_app;
      destruct (find_index (fun a => writesb a x) (rev tr)) eqn: Hfind.
    - destruct IHtr as [? [sw Hsw]].
      rewrite find_index_spec in Hfind; clarify.
      generalize (nth_error_lt _ _ Hfind1); rewrite rev_length; intro.
      repeat rewrite <- minus_Sn_m; clarify; try omega.
      exists sw; clarify; econstructor; eauto.
    - destruct (writesb a x) eqn: Hwrites; clarify.
      + rewrite rev_length.
        assert (S (length tr) - (length tr + 0) - 1 = 0) as Hz by omega;
          rewrite Hz; clarify.
        destruct a; clarify; unfold beq in *; clarify.
        generalize (write_clock Ha); unfold e_app; clarsimp.
        destruct (eq_dec t t1); clarify.
        exists s; split; [apply ss_refl|].
        inversion Ha; clarify; unfold beq, e_of, upd in *; clarsimp.
        { destruct s'0 as (((?, ?), ?), ?); clarify.
          specialize (Hwf'1 t t1); clarify; omega. }
      + inversion Ha; clarify; unfold beq, upd in *; clarify.
  Qed.

  Lemma ss_trans : forall s tr s' tr' s'' (Hsteps : step_star s tr s')
    (Hsteps' : step_star s' tr' s''), step_star s (tr ++ tr') s''.
  Proof.
    intros; induction Hsteps; clarify.
    econstructor; eauto.
  Qed.

  Lemma write_ge : forall s u x s' n t (Hstep : step s (wr u x) s')
    (Hwrite : write_of s x = (n, t)), clock_of s u t >= n.
  Proof.
    intros; inversion Hstep; unfold e_of in *; clarsimp.
  Qed.

  Lemma write_after_write : forall s tr s' i j x t u
    (Hsteps : step_star s tr s') (Hwf : well_formed s)
    (Hi : nth_error tr i = Some (wr t x)) (Hj : nth_error tr j = Some (wr u x))
    (Hlt : i < j), happens_before tr i j.
  Proof.
    induction tr using rev_ind; clarsimp.
    generalize (step_star_rev_inv _ _ Hsteps); intros [sx [Htr Hx]].
    destruct (lt_dec j (length tr)).
    { rewrite nth_error_app in *; clarify.
      destruct (lt_dec i (length tr)); [|omega].
      specialize (IHtr _ _ _ _ _ _ Htr Hwf Hi Hj Hlt).
      apply hb_app; auto. }
    rewrite nth_error_app in *; clarify.
    destruct (j - length tr) eqn: Hminus; clarsimp.
    assert (j = length tr) by omega; clarify.
    destruct (write_of sx x0) eqn: Hwrite.
    generalize (write_last _ Htr Hwrite Hwf); intro Hlast.
    destruct (last_write tr x0) eqn: Hfind.
    destruct Hlast as [sw Hsw]; clarify.
    eapply hbe_hb_trans.
    - instantiate (1 := length tr - n1 - 1).
      assert (i <= length tr - n1 - 1) as Hle.
      { destruct (le_dec i (length tr - n1 - 1)); auto.
        generalize (nth_error_rev _ _ Hi); intro.
        assert (length tr - i - 1 < n1) by omega.
        unfold last_write in Hfind; rewrite find_index_spec in Hfind;
          clarify.
        specialize (Hfind22 (length tr - i - 1) (wr t x0)); clarify.
        unfold beq in *; clarify. }
      rewrite le_lt_or_eq_iff in Hle; unfold hbe; clarify.
      left; apply hb_app; eapply IHtr; eauto.
    - generalize (write_ge Hx Hwrite); intro Hge.
      generalize (step_star_wf Hwf Hsw1); intro Hwf'.
      rewrite <- (firstn_skipn (length tr - n1 - 1) tr) at 1.
      erewrite skipn_n; erewrite skipn_n in Hsw22; eauto.
      generalize (clocks_hb (wr u x0) Hwf' Hsw22 eq_refl eq_refl);
        intro Hhb; use Hhb.
      generalize (hb_app' (firstn (length tr - n1 - 1) tr) Hhb).
      intro Hhb'; rewrite <- (firstn_skipn (length tr - n1 - 1) tr) at 6.
      erewrite (skipn_n (length tr - n1 - 1)); eauto.
      rewrite List.firstn_length in Hhb' at 1.
      rewrite Min.min_l in Hhb'; [|omega].
      rewrite <- app_assoc, app_length; clarsimp.
    - unfold last_write in Hfind; rewrite find_index_fail in Hfind.
      rewrite Forall_rev, Forall_forall in Hfind.
      generalize (Coqlib.nth_error_in _ _ Hi); intro Hin;
        specialize (Hfind _ Hin); clarify; unfold beq in *; clarify.
  Qed.
  
  Lemma read_ge : forall s u x s' n t (Hstep : step s (rd u x) s')
    (Hwrite : write_of s x = (n, t)), clock_of s u t >= n \/
    read_of s x = E (e_of (clock_of s) u).
  Proof.
    intros; inversion Hstep; clarify; clarsimp.
  Qed.

  Lemma write_own : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hown : write_of s x = e_of (clock_of s) t) u,
    app (read_of s x) u <= clock_of s t u.
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; clarify. }
    generalize (step_star_rev_inv _ _ Hsteps); intros [s' [Htr Hx]].
    specialize (IHtr _ x0 t Htr).
    generalize (step_star_wf wf0 Htr); intro Hwf.
    inversion Hx; clarify; unfold upd, e_of in *; clarsimp.
    - destruct (eq_dec u t); clarify.
      { specialize (Hwf1 u t); clarify; omega. }
    - destruct (eq_dec u t); clarify.
      { specialize (Hwf1 u t); clarify; omega. }
    - specialize (IHtr u0); clarsimp.
      destruct (eq_dec u t); clarify.
      { specialize (Hwf1 u t); clarify; omega. }
    - destruct e; clarify.
    - unfold vc_join in Hown, IHtr; unfold vc_join.
      specialize (Hwf21 m t); rewrite Max.max_l in IHtr; [clarify | omega].
      etransitivity; [apply IHtr | apply NPeano.Nat.le_max_l].
    - unfold vc_inc in Hown; clarify.
      specialize (Hwf222 x0 t); rewrite Hown in *; clarify; omega.
    - destruct (eq_dec t1 t); clarify.
      + unfold vc_inc in Hown; clarify.
        specialize (Hwf222 x0 t); rewrite Hown in *; clarify; omega.
      + unfold vc_join in *.
        specialize (Hwf1 t1 t); rewrite Max.max_l in IHtr; clarify; [|omega].
        etransitivity; [apply IHtr | apply NPeano.Nat.le_max_l].
    - destruct (eq_dec u0 t); clarify.
      + unfold vc_inc in Hown; clarify.
        specialize (Hwf222 x0 t); rewrite Hown in *; clarify; omega.
      + unfold vc_join in *.
        specialize (Hwf1 u0 t); rewrite Max.max_l in IHtr; clarify; [|omega].
        etransitivity; [apply IHtr | apply NPeano.Nat.le_max_l].
  Qed.

  Lemma write_ge' : forall tr s u x s' t (Hsteps : step_star s0 tr s)
    (Hstep : step s (wr u x) s'),
    clock_of s u t >= app (read_of s x) t.
  Proof.
    intros; inversion Hstep; unfold e_of in *; clarsimp.
    - generalize (write_own(t := u) x Hsteps); clarify.
    - destruct e; clarify.
  Qed.
 
  Lemma step_read : forall tr s s' x t (Hsteps : step_star s tr s')
    (Hwf : well_formed s),
    app (read_of s' x) t = app (read_of s x) t \/
    exists tr1 sa a tr2, tr = tr1 ++ a :: tr2 /\ step_star s tr1 sa /\
      clock_of sa (thread_of a) t >= app (read_of s x) t /\ accesses a x /\
      step_star sa (a :: tr2) s'.
  Proof.
    induction tr; intros; inversion Hsteps as [| ? ? ? ? Ha Htr]; clarify.
    generalize (wf_preservation Hwf Ha); intro Hwf'.
    specialize (IHtr _ _ x t Htr Hwf').
    destruct IHtr.
    - destruct (eq_dec (app (read_of s'0 x) t) (app (read_of s x) t));
        clarsimp.
      right; exists []; eexists; eexists; eexists; split; simpl; eauto;
        split; [apply ss_refl|].
      inversion Ha; clarify; unfold accesses, upd in *; clarsimp; repeat split;
        try econstructor; eauto 2.
      + specialize (Hwf221 x t); clarsimp; omega.
      + destruct e; clarify.
    - right; destruct H as (tr1 & sa & b & tr2 & ?); clarify.
      destruct (le_dec (app (read_of s x) t) (app (read_of s'0 x) t)).
      { exists (a :: tr1), sa, b, tr2; clarify.
        split; [econstructor; eauto | clarify; omega]. }
      exists []; eexists; eexists; eexists; clarify.
      split; [apply ss_refl|].
      destruct (eq_dec (app (read_of s x) t) (app (read_of s'0 x) t)); [omega|].
      inversion Ha; clarify; unfold upd in *; clarsimp;
        repeat split; unfold accesses; eauto.
      + specialize (Hwf221 x t); clarsimp.
      + destruct e; clarify.
  Qed.      

  Lemma write_after_read : forall tr s s' i j x t u (Hsteps : step_star s tr s')
    (Hi : nth_error tr i = Some (rd t x)) (Hj : nth_error tr j = Some (wr u x))
    (Hlt : i < j) tr0 (Hroot : step_star s0 tr0 s), happens_before tr i j.
  Proof.
    induction tr; clarsimp.
    inversion Hsteps as [|? ? ? ? Ha Htr]; clarify.
    destruct j; [omega | clarify].
    generalize (step_star_inv Hroot Ha); intro Hsteps'.
    destruct i; clarify; [|apply hb_cons; eapply IHtr; eauto; omega].
    generalize (nth_error_split' _ _ Hj); intros [tr1 [tr2 ?]]; clarify.
    generalize (step_star_app_inv _ _ Htr); intros [sw Hsw]; clarify.
    inversion Hsw2 as [|? ? ? ? Hw Htr2]; clarify.
    generalize (ss_trans Hsteps' Hsw1); intro Hsteps''.
    generalize (write_ge' t Hsteps'' Hw); intro Hge.
    generalize (step_star_wf wf0 Hsteps'); intro Hwf.
    generalize (step_read x t Hsw1 Hwf); intro Hread.
    generalize (read_clock Ha); intro Hclock; rewrite Hclock in *.
    assert (clock_of s'0 = clock_of s) as Heq by (inversion Ha; clarify);
      rewrite Heq in *.
    destruct Hread as [Hclock' | (tr1' & sb & b & tr2' & Hb)].
    - rewrite Hclock' in *.
      generalize (ss_step Ha Hsw1); intro Hsteps0.
      generalize (step_star_wf wf0 Hroot); intro Hwf0.
      generalize (clocks_hb (wr u x) Hwf0 Hsteps0 eq_refl eq_refl); intro Hhb;
        clarify.
      generalize (hb_app tr2 Hhb); clarsimp.
    - clarify.
      eapply hb_trans.
      + rewrite <- app_assoc; instantiate (1 := S (length tr1')); simpl.
        generalize (ss_step Ha Hb21); intro Hsteps1.
        generalize (step_star_wf wf0 Hroot); intro Hwf0.
        generalize (clocks_hb b Hwf0 Hsteps1 eq_refl eq_refl); intro Hhb;
          clarify.
        generalize (hb_app (tr2' ++ wr u x :: tr2) Hhb); clarsimp.
      + apply hb_cons; destruct Hb2221 as [t' [? | ?]]; clarify.
        * eapply IHtr; eauto.
          { rewrite <- app_assoc; simpl; apply nth_error_split. }
          { rewrite app_length; simpl; omega. }
        * eapply write_after_write; eauto.
          { rewrite <- app_assoc; simpl; apply nth_error_split. }
          { rewrite app_length; simpl; omega. }
  Qed.      

  Lemma clock_pos : forall s t u (Hwf : well_formed s) (Hdiff : t <> u),
    clock_of s t t > 0.
  Proof.
    intros (((?, ?), ?), ?); clarify.
    specialize (Hwf1 _ _ Hdiff); omega.
  Qed.

  Lemma read_own : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hown : read_of s x = E (e_of (clock_of s) t)) u,
    e_app (write_of s x) u <= clock_of s t u.
  Proof.
    induction tr using rev_ind; clarify.
    { inversion Hsteps; clarify. }
    generalize (step_star_rev_inv _ _ Hsteps); intros [s' [Htr Hx]].
    specialize (IHtr _ x0 t Htr).
    generalize (step_star_wf wf0 Htr); intro Hwf.
    inversion Hx; clarify; unfold upd, e_of in *; clarsimp.
    - inversion Hown; clarify.
      destruct (W x0); clarify.
    - inversion HR; clarify.
      destruct (eq_dec u t); clarify.
      { specialize (Hwf1 u t); clarify; omega. }
    - inversion Hown; clarify.
      clear H1; destruct (eq_dec u t); clarify.
      { specialize (Hwf1 u t); clarify; omega. }
    - unfold vc_join in *.
      specialize (Hwf21 m t); rewrite Max.max_l in IHtr; [clarify | omega].
      etransitivity; [apply IHtr | apply NPeano.Nat.le_max_l].
    - unfold vc_inc in *; clarify.
      specialize (Hwf221 x0 t); rewrite Hown in *; clarify; omega.
    - destruct (eq_dec t1 t); clarify.
      + unfold vc_inc in *; clarify.
        specialize (Hwf221 x0 t); rewrite Hown in *; clarify; omega.
      + unfold vc_join in *.
        specialize (Hwf1 t1 t); rewrite Max.max_l in IHtr; clarify; [|omega].
        etransitivity; [apply IHtr | apply NPeano.Nat.le_max_l].
    - destruct (eq_dec u0 t); clarify.
      + unfold vc_inc in Hown; clarify.
        specialize (Hwf221 x0 t); rewrite Hown in *; clarify; omega.
      + unfold vc_join in *.
        specialize (Hwf1 u0 t); rewrite Max.max_l in IHtr; clarify; [|omega].
        etransitivity; [apply IHtr | apply NPeano.Nat.le_max_l].
  Qed.

  Lemma read_after_write : forall s tr s' i j x t u (Hsteps : step_star s tr s')
    (Hi : nth_error tr i = Some (wr t x)) (Hj : nth_error tr j = Some (rd u x))
    (Hlt : i < j) tr0 (Hroot : step_star s0 tr0 s), happens_before tr i j.
  Proof.
    induction tr using rev_ind; clarsimp.
    generalize (step_star_rev_inv _ _ Hsteps); intros [sx [Htr Hx]].
    destruct (lt_dec j (length tr)).
    { rewrite nth_error_app in *; clarify.
      destruct (lt_dec i (length tr)); [|omega].
      specialize (IHtr _ _ _ _ _ _ Htr Hi Hj Hlt _ Hroot).
      apply hb_app; auto. }
    rewrite nth_error_app in *; clarify.
    destruct (j - length tr) eqn: Hminus; clarsimp.
    assert (j = length tr) by omega; clarify.
    destruct (write_of sx x0) eqn: Hwrite.
    specialize (step_star_wf wf0 Hroot); intro Hwf.
    generalize (write_last _ Htr Hwrite Hwf); intro Hlast.
    destruct (last_write tr x0) eqn: Hfind.
    destruct Hlast as [Hn1 [sw Hsw]]; clarify.
    generalize (nth_error_lt _ _ Hn1); intro.
    eapply hbe_hb_trans.
    - instantiate (1 := length tr - n1 - 1).
      assert (i <= length tr - n1 - 1) as Hle.
      { destruct (le_dec i (length tr - n1 - 1)); auto.
        generalize (nth_error_rev _ _ Hi); intro.
        assert (length tr - i - 1 < n1) by omega.
        unfold last_write in Hfind; rewrite find_index_spec in Hfind;
          clarify.
        specialize (Hfind22 (length tr - i - 1) (wr t x0)); clarify.
        unfold beq in *; clarify. }
      rewrite le_lt_or_eq_iff in Hle; unfold hbe; clarify.
      left; eapply write_after_write; eauto; rewrite nth_error_app;
        clarify; eauto.
    - assert (clock_of sx u t1 >= clock_of sw t1 t1) as Hle.
      { generalize (read_ge Hx Hwrite); intros [? | Hread]; auto.
        generalize (ss_trans Hroot Htr); intro Hsteps'.
        generalize (read_own _ Hsteps' Hread t1); rewrite Hwrite; clarify. }
      generalize (step_star_wf Hwf Hsw1); intro Hwf'.
      rewrite <- (firstn_skipn (length tr - n1 - 1) tr) at 1.
      erewrite skipn_n; erewrite skipn_n in Hsw22; eauto.
      generalize (clocks_hb (rd u x0) Hwf' Hsw22 eq_refl eq_refl);
        intro Hhb; use Hhb.
      generalize (hb_app' (firstn (length tr - n1 - 1) tr) Hhb).
      intro Hhb'; rewrite <- (firstn_skipn (length tr - n1 - 1) tr) at 6.
      erewrite (skipn_n (length tr - n1 - 1)); eauto.
      rewrite List.firstn_length in Hhb' at 1.
      rewrite Min.min_l in Hhb'; [|omega].
      rewrite <- app_assoc, app_length; clarsimp.
    - unfold last_write in Hfind; rewrite find_index_fail in Hfind.
      rewrite Forall_rev, Forall_forall in Hfind.
      generalize (Coqlib.nth_error_in _ _ Hi); intro Hin;
        specialize (Hfind _ Hin); clarify; unfold beq in *; clarify.
  Qed.

  Hint Resolve ss_refl wf0.

  Theorem Soundness tr : forall s', step_star s0 tr s' -> race_free tr.
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
      upd (upd C t (vc_join (C t) (C u))) u (vc_inc u (C u))
  | acq t m => let C := clock_of s in let L := lock_of s in
      upd C t (vc_join (C t) (L m))
  | _ => clock_of s
  end.

  Lemma K_lower : forall a s t t', clock_of s t t' <= K a s t t'.
  Proof.
    intros; destruct a; clarify; unfold upd, vc_join, vc_inc; clarify.
    - apply Max.le_max_l.
    - destruct (eq_dec u t); clarify.
      apply Max.le_max_l.
  Qed.

  Lemma K_upper : forall a s s' (Hstep : step s a s') t t',
    K a s t t' <= clock_of s' t t'.
  Proof.
    intros.
    generalize (clock_mono (ss_step Hstep (ss_refl _)) t t'); intro.
    destruct a; clarify; inversion Hstep; clarify.
  Qed.

  Lemma acq_rel_clock : forall s t m tr s'
    (Hsteps : step_star s (acq t m :: tr ++ [rel t m]) s'),
    vc_le (clock_of s t) (lock_of s' m).
  Proof.
    intros.
    inversion Hsteps as [|? ? ? ? Ha Htr]; clarify.
    inversion Ha; clarify.
    generalize (step_star_rev_inv _ _ Htr); intros [s'' [Htr' Hx]].
    inversion Hx; clarify.
    unfold upd; clarify.
    generalize (ss_step Ha Htr'); intro Hsteps'.
    generalize (clock_mono Hsteps'); unfold vc_le; auto.
  Qed.

  Lemma feasible_app : forall tr tr', feasible (tr ++ tr') -> feasible tr.
  Proof.
    induction tr' using rev_ind; clarsimp.
    apply IHtr'; eapply feasible_snoc; rewrite <- app_assoc; eauto.
  Qed.

  Lemma lock_mono : forall s tr s' tr' s'' (Hsteps : step_star s tr s')
    (Hsteps' : step_star s' tr' s'') m t (Hfeasible : feasible (tr ++ tr')),
    lock_of s' m t <= lock_of s'' m t.
  Proof.
    induction tr' using rev_ind; clarify.
    { inversion Hsteps'; clarify. }
    generalize (step_star_rev_inv _ _ Hsteps'); intros [sx [Htr' Hx]].
    specialize (IHtr' _ Hsteps Htr' m t).
    rewrite app_assoc in Hfeasible; generalize (feasible_snoc _ _ Hfeasible);
      clarify.
    inversion Hx; unfold upd, vc_inc, vc_join in *; clarify.
    generalize (ss_trans Hsteps Htr'); intro Htr.
    generalize (feasible_le Htr m t1 t Hfeasible); clarify; omega.
  Qed.

  Lemma fork_irrefl : forall tr i t (Hfeasible : feasible tr),
    nth_error tr i <> Some (fork t t).
  Proof.
    repeat intro; inversion Hfeasible.
    specialize (Hfork _ _ _ H i (fork t t)); clarify.
    contradiction Hfork; unfold uses_thread; clarify.
  Qed.

  Lemma join_irrefl : forall tr i t (Hfeasible : feasible tr),
    nth_error tr i <> Some (join t t).
  Proof.
    repeat intro; inversion Hfeasible.
    specialize (Hjoin _ _ _ H i (join t t)); clarify.
    contradiction Hjoin; unfold uses_thread; clarify.
  Qed.

  (* Lemma 4 *)
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
            generalize (step_star_app_inv _ _ Hsteps2); intros [sr [? Hsr]].
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
            generalize (step_star_app_inv _ _ Hsteps2); intros [sc [Hsc ?]].
            generalize (step_star_app_inv _ _ Hsc); intros [sr [? Hsr]].
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
            generalize (step_star_app_inv _ _ Hsteps2); intros [sc [? Hsc]].
            exists [], sa, sa', l2, sc, (l3 ++ [rel u m]); clarsimp.
            rewrite removelast_snoc; auto. }
      transitivity (K (rel t m) sr t t1); [|transitivity (K (acq u m) sc u t1)].
      + destruct Hlocka; clarify.
        * destruct l1; clarify.
          inversion Hra21 as [|? ? ? ? Ha Hl1]; clarify.
          generalize (clock_mono Hl1 t t1); inversion Ha; clarify.
        * eapply clock_mono; eauto.
      + simpl; unfold upd, vc_join; clarify.
        generalize (step_star_inv Hra21 Hra221); intro Hsteps.
        generalize (ss_trans Hsteps1 Hsteps); intro Hsteps'.
        generalize (lock_mono Hsteps' Hra2221 m t1); intro Hlock.
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
          generalize (clock_mono Hl3 u t1); inversion Hstep; clarify.
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
          { generalize (clock_mono Hsteps2 (thread_of b) t1);
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
          generalize (clock_mono Hsteps2 t t1).
          unfold upd, vc_join, vc_inc; clarify.
          destruct (eq_dec u t); clarify.
          { generalize (fork_irrefl(t := t) (length tr1) Hfeasible);
              rewrite nth_error_split; clarify. }
          destruct (eq_dec t v); clarify.
          { generalize (join_irrefl(t := v) (length tr1 + S (length tr2))
              Hfeasible); rewrite nth_error_app, lt_dec_plus_r, minus_plus;
              simpl; rewrite nth_error_split; clarify. }
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
      rewrite <- plus_n_Sm in Hltj; rewrite <- NPeano.Nat.succ_lt_mono in Hltj.
      generalize (nth_error_succeeds tr2); intro Hk.
      specialize (Hk (k - length tr1)); use Hk; [|omega].
      destruct Hk as [c Hk].
      generalize (nth_error_split' _ _ Hk); intros [l1 [l2 ?]]; clarify.
      generalize (step_star_app_inv _ _ Hsteps2); intros [sc [Hl1 Hstepsc]].
      inversion Hstepsc as [|? sc' ? ? Hstepc Hl2]; clarify.
      transitivity (K c sc (thread_of c) t1).
      + destruct (eq_dec (thread_of a) (thread_of c)).
        { rewrite e; etransitivity; [apply K_upper; eauto|].
          etransitivity; [|apply K_lower].
          eapply clock_mono; eauto. }
        eapply IHHhb1; eauto; clarsimp; omega.
      + destruct (eq_dec (thread_of c) (thread_of b)).
        { rewrite e; etransitivity; [apply K_upper; eauto|].
          etransitivity; [|apply K_lower].
          eapply clock_mono; eauto. }
        generalize (ss_step Hstepa Hl1); intro Hstepsa.
        generalize (ss_trans Hsteps1 Hstepsa); intro.
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
    clock_of sa t t <= clock_of sb u t.
  Proof.
    intros.
    inversion Hsteps as [|? ? ? ? Hstepa Htr]; clarify.
    generalize (hb_app' tr0 Hhb); intro Hhb'; clarsimp.
    generalize (hb_clocks Hsteps0 Hstepa Htr _ eq_refl eq_refl _ Hhb');
      clarify.
    destruct Ha as [? [? | ?]], Hb as [? [? | ?]]; clarify.
  Qed.

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
  
  Lemma access_write : forall tr s a x (Hsteps : step_star s0 tr s)
    (Hrf : race_free' (tr ++ [a])) (Haccesses : accesses a x)
    (Hfeasible : feasible (tr ++ [a])),
    e_le (write_of s x) (clock_of s (thread_of a)).
  Proof.
    intros.
    destruct (write_of s x) eqn: HW; clarify.
    generalize (write_last _ Hsteps HW wf0); intro Hlast.
    destruct (last_write tr x) eqn: Hfind; clarify;
      [|unfold e_bot in *; clarify].
    generalize (nth_error_lt _ _ Hlast1); intro.
    specialize (Hrf (length tr - n0 - 1) (length tr));
      rewrite nth_error_split, nth_error_app in Hrf; clarify.
    specialize (Hrf _ _ Hlast1 eq_refl x); unfold writes, accesses in Hrf;
      use Hrf; eauto; use Hrf; eauto.
    rewrite <- (firstn_skipn (length tr - n0 - 1) tr) in Hrf at 1;
      rewrite <- app_assoc in Hrf.
    rewrite <- (firstn_skipn (length tr - n0 - 1) tr) in Hrf at 6.
    erewrite skipn_n in Hlast222, Hrf; eauto.
    generalize (step_star_wf wf0 Hlast21); intro Hwf.
    eapply hb_clocks'; unfold accesses; eauto.
    - rewrite <- (firstn_skipn (length tr - n0 - 1) tr) in Hfeasible.
      erewrite skipn_n in Hfeasible; eauto; clarsimp.
    - assert (length (firstn (length tr - n0 - 1) tr) = length tr - n0 - 1)
        as Hlen.
      { rewrite List.firstn_length; apply Min.min_l; omega. }
      generalize (hb_suffix _ _ Hrf); clarsimp.
  Qed.

  Definition eorv_le r V :=
    match r with VC v => vc_le v V | E e => e_le e V end.

  Lemma eorv_le_iff : forall r V, eorv_le r V <-> forall t, app r t <= V t.
  Proof.
    intros; split; intros; destruct r; clarify; destruct e; clarify.
    specialize (H t); clarify.
  Qed.    

  Lemma read_step : forall s a s' tr s'' x t (Hstep : step s a s')
    (Hwf : well_formed s) (Hsteps : step_star s' tr s'')
    (Hle : eorv_le (read_of s x) (clock_of s'' t))
    (Hrf : accesses a x ->
       happens_before (a :: tr ++ [wr t x]) 0 (S (length tr)))
    tr0 s0 (Hsteps0 : step_star s0 tr0 s)
    (Hfeasible : feasible (tr0 ++ a :: tr ++ [wr t x])),
    eorv_le (read_of s' x) (clock_of s'' t).
  Proof.
    intros.
    rewrite eorv_le_iff; intro u.
    destruct (eq_dec (app (read_of s' x) u) (app (read_of s x) u)).
    { rewrite eorv_le_iff in Hle; rewrite e; auto. }
    assert (accesses a x) as Haccess by (exists (thread_of a); inversion Hstep;
      clarify; unfold upd in n; clarify); clarify.
    generalize (ss_step Hstep Hsteps); intro Hsteps'.
    generalize (hb_clocks' Hwf Hsteps' Hsteps0 Hfeasible eq_refl eq_refl Hrf
      Haccess); intro Hle'.
    specialize (Hle' x); unfold accesses in Hle'; use Hle'; eauto.
    inversion Hstep; clarify; unfold upd in *; clarsimp.
  Qed.

  Lemma write_read_aux : forall tr s x t (Hsteps : step_star s0 tr s)
    (Hread : forall tr1 sa a sa' tr2, tr = tr1 ++ a :: tr2 ->
       step_star s0 tr1 sa -> step sa a sa' -> step_star sa' tr2 s ->
       eorv_le (read_of sa' x) (clock_of s t)),
    eorv_le (read_of s x) (clock_of s t).
  Proof.
    intros.
    destruct (eq_dec tr []).
    { subst; inversion Hsteps; clarify. }
    rewrite (app_removelast_last (wr t x)) in Hsteps; auto.
    generalize (step_star_rev_inv _ _ Hsteps); clarify.
    eapply Hread; eauto; try (apply ss_refl).
    apply app_removelast_last; auto.
  Qed.    

  Lemma write_read : forall tr s t x (Hsteps : step_star s0 tr s)
    (Hrf : forall i a, nth_error tr i = Some a -> accesses a x ->
       happens_before (tr ++ [wr t x]) i (length tr))
    (Hfeasible : feasible (tr ++ [wr t x])),
    eorv_le (read_of s x) (clock_of s t).
  Proof.
    intros; eapply write_read_aux; eauto.
    induction tr1 using rev_ind; intros sa a sa' tr2 ? H0 Ha Htr2; clarify.
    - inversion H0; clarify.
      eapply read_step; eauto.
      + clarify.
      + apply Hrf; auto.
    - generalize (step_star_rev_inv _ _ H0); intros [sx [Htr Hx]].
      rewrite <- app_assoc in IHtr1; simpl in IHtr1;
        specialize (IHtr1 _ _ _ _ eq_refl Htr Hx).
      generalize (ss_step Ha Htr2); clarify.
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
    assert (exists s', step s x s').
    destruct s as (((C, L), R), W).
    generalize (step_star_wf wf0 Htr); intro Hwf.
    destruct x; try (eexists; econstructor; eauto; fail).
    - generalize (access_write(x := x) Htr Hrf); unfold accesses; intro HW;
        use HW; eauto.
      destruct (R x) eqn: HR.
      + eexists; eapply read_shared; eauto; clarsimp.
      + destruct e as (n, u); destruct (eq_dec u t).
        * subst; eexists; eapply read_exclusive; eauto; clarsimp.
          specialize (Hwf221 x t); clarsimp.
        * eexists; eapply read_share; eauto; clarsimp.
    - generalize (access_write(x := x) Htr Hrf); unfold accesses; intro HW;
        use HW; eauto.
      generalize (write_read(x := x) t Htr); intro X; lapply X; [clarify|].
      destruct (R x) eqn: HR.
      + eexists; eapply write_shared; eauto.
      + eexists; eapply write_exclusive; eauto.
      + intros ? ? Hi Ha.
        generalize (nth_error_lt _ _ Hi); intro.
        eapply Hrf; auto.
        * rewrite nth_error_app; clarify; eauto.
        * apply nth_error_split.
        * right; unfold writes; eauto.
        * unfold accesses; clarify; eauto.
    - clarify; eexists; eapply step_star_inv; eauto.
  Qed.

  Theorem Correctness tr (Hfeasible : feasible tr) :
    race_free tr <-> exists s, step_star s0 tr s.
  Proof.
    split.
    - apply Completeness; auto.
    - intros [? ?]; eapply Soundness; eauto.
  Qed.

End FastTrack. (*~800loc*)