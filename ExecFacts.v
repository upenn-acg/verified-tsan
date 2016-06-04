(* Lemmas about execution and alternative execution relations *)
Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import SCFacts.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Hint Constructors exec.

Notation upd_env' G t u := (match u with Some (a, v) => upd_env G t a v
  | None => G end).

Section Exec.

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

Lemma upd_triv : forall G t a, upd_env G t a (G t a) = G.
Proof.
  intros; extensionality t'; extensionality a'; unfold upd_env, upd; clarify.
Qed.
 
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

Lemma upd_old : forall G t1 a1 v1 t2 a2 (Ha : a1 <> a2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

Lemma upd_old_t : forall G t1 a1 v1 t2 a2 (Ht : t1 <> t2),
  upd_env G t1 a1 v1 t2 a2 = G t2 a2.
Proof.
  intros; unfold upd_env, upd; clarify.
Qed.

Lemma upd_three : forall G t a1 a2 v1 v2 v1' (Hdiff : a1 <> a2),
  upd_env (upd_env (upd_env G t a1 v1) t a2 v2) t a1 v1' =
  upd_env (upd_env G t a1 v1') t a2 v2.
Proof.
  intros; rewrite upd_assoc, upd_overwrite; auto.
Qed.

Definition mods_loc i x :=
  match i with
  | Store y _ => y = x
  | Lock y => x = (y, 0)
  | Unlock y => x = (y, 0)
  | _ => False
  end.

Context {ML : @Memory_Layout var nat _}.

(*if a prog step does not modify x, then we could read the same value of x*)
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

Definition instr_result t i G v :=
  match i with
  | Assign a e => Some (None, None, None, Some (a, eval G e),
      fun (P : state) => True)
  | Load a x => Some (None, Some (rd t (fst x)), Some (Read t x v), Some (a, v),
      fun P => True)
  | Store x e => Some (None, Some (wr t (fst x)), Some (Write t x (eval G e)),
      None, fun P => True)
  | Lock m => Some (None, Some (acq t m), Some (Acq t m), None, fun P => True)
  | Unlock m => Some (None, Some (rel t m), Some (Rel t m), None, fun P => True)
  | Spawn u li => Some (Some (u, li), Some (fork t u), None, None,
      fun P => ~In u (map fst P))
  | Wait u => Some (None, Some (join t u), None, None, fun P => In (u, []) P)
  | Assert_le e1 e2 => if le_dec (eval G e1) (eval G e2) then
      Some (None, None, None, None, fun P => True) else None
  end.

Lemma exec_result : forall P G t o c P' G'
  (Hexec : exec P G t o c P' G'),
  exists P1 i li P2 v, P = P1 ++ (t, i :: li) :: P2 /\
    match instr_result t i (G t) v with
    | Some (th, o1, c1, u1, f) => G' = match u1 with Some (a, v) =>
        upd_env G t a v | None => G end /\ o1 = o /\ c1 = c /\
        P' = Some (P1 ++ (t, li) :: opt_to_list th ++ P2) /\ f P
    | None => G' = G /\ P' = None /\ o = None /\ c = None
    end.
Proof.
  intros; inversion Hexec; clarify; do 4 eexists; try (exists v);
    try (exists 0); repeat eexists; eauto; clarify.
Qed.

Lemma result_exec : forall P P1 t i li P2 G v
  (HP : P = P1 ++ (t, i :: li) :: P2),
  match instr_result t i (G t) v with
  | Some (th, o, c, u1, f) => f P -> exec P G t o c
      (Some (P1 ++ (t, li) :: opt_to_list th ++ P2))
      (match u1 with Some (a, v) => upd_env G t a v | None => G end)
  | None => exec P G t None None None G
  end.
Proof.
  destruct i; clarify.
  destruct (le_dec (eval (G t) e1) (eval (G t) e2)); eauto.
Qed.

Lemma forall_step : forall P S (Hforall : state_forall P S)
  G t o c S' G' (Hstep : exec S G t o c (Some S') G'), state_forall P S'.
Proof.
  unfold state_forall; intros.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite Forall_app in *; clarify.
  inversion Hforall2 as [|?? Ha]; inversion Ha; constructor; clarify.
  rewrite Forall_app; clarify.
  destruct o0; clarify.
  destruct i; clarify.
  constructor; clarify.
  rewrite <- instr_forall_list; eauto.
Qed.

Corollary forall_steps : forall P S (Hforall : state_forall P S)
  G o c S' G' (Hsteps : exec_star (Some S) G o c (Some S') G'),
  state_forall P S'.
Proof.
  intros; remember (Some S) as P1; remember (Some S') as P2;
    generalize dependent S; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  apply (IHHsteps s); auto.
  eapply forall_step; eauto.
Qed.

Definition instr_size := instr_rect'' _ _ (fun _ => 1) (fun _ li r => S r)
  0 (fun _ _ r1 r2 => r1 + r2).

Fixpoint instr_list_size l :=
  match l with
  | [] => 0
  | i :: rest => instr_size i + instr_list_size rest
  end.

Lemma instr_list_size_app : forall l1 l2, instr_list_size (l1 ++ l2) =
  instr_list_size l1 + instr_list_size l2.
Proof.
  induction l1; clarify.
  rewrite IHl1; omega.
Qed.

Fixpoint size (P : state) :=
  match P with
  | [] => 0
  | (_, l) :: rest =>  instr_list_size l + size rest
  end.

Lemma size_app : forall P1 P2, size (P1 ++ P2) = size P1 + size P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; destruct a; omega.
Qed.

Lemma spawn_size : forall u li, instr_size (Spawn u li) =
  S (instr_list_size li).
Proof. induction li; clarify. Qed.

Lemma size_decr : forall P G t o c P' G' (Hstep : exec P G t o c (Some P') G'),
  size P' < size P.
Proof.
  intros; inversion Hstep; subst; repeat rewrite size_app; try (clarify; omega).
  unfold size at 4; fold size.
  unfold instr_list_size at 1; fold instr_list_size.
  rewrite spawn_size; simpl; omega.
Qed.

Lemma size_steps : forall P G o c P' G'
  (Hsteps : exec_star (Some P) G o c (Some P') G'), size P' <= size P.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit size_decr; eauto.
  specialize (IHHsteps _ eq_refl _ eq_refl); omega.
Qed.

Lemma exec_next : forall P G t o c P' G' (Hexec : exec P G t o c P' G')
  (Hdistinct : distinct P) Pa Pb i li (Hin : P = Pa ++ (t, i :: li) :: Pb),
  exists v,
  match instr_result t i (G t) v with
  | Some (th, o1, c1, u1, f) => G' = match u1 with Some (a, v) =>
      upd_env G t a v | None => G end /\ o1 = o /\ c1 = c /\
      P' = Some (Pa ++ (t, li) :: opt_to_list th ++ Pb) /\ f P
  | None => G' = G /\ P' = None /\ o = None /\ c = None end.
Proof.
  intros; exploit exec_result; eauto; intros (? & i' & ? & ? & v & ?).
  clarify.
  exploit distinct_thread; eauto; clarify; eauto.
Qed.

Lemma distinct_in : forall P (Hdistinct : distinct P) t li1 li2
  (Hin1 : In (t, li1) P) (Hin2 : In (t, li2) P), li1 = li2.
Proof.
  intros.
  generalize (in_split _ _ Hin1), (in_split _ _ Hin2); clarify.
  exploit distinct_thread; eauto; clarify.
Qed.

Lemma step_thread : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G') (Hdistinct : distinct P)
  li (Ht : In (t, li) P),
  exists i li', li = i :: li' /\ In (t, li') P'.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify].
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  repeat eexists; eauto; rewrite in_app; clarify.
Qed.

Lemma in_step_rev : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G') t' li (Hin : In (t', li) P'),
  In (t', li) P \/ (t' = t /\ exists i, In (t, i :: li) P) \/
  exists li', In (t, Spawn t' li :: li') P.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i' & ? & ? & v & ? & Hresult).
  destruct (instr_result t i' (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi';
    clarify.
  rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
  setoid_rewrite in_app; destruct Hin as [? | [? | [? | ?]]]; clarify;
    try solve [left; eauto].
  - right; left; clarify; eauto.
  - right; right; destruct o0; clarify.
    destruct i'; clarify; eauto.
Qed.

Inductive exec_star_minus t : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_m P G : exec_star_minus t P G [] [] P G
| exec_step_m P G t' o c P' G' (Hin : t' <> t)
    (Hexec : exec P G t' o c P' G') lo lc P'' G''
    (Hexec' : exec_star_minus t P' G' lo lc P'' G'') :
    exec_star_minus t (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc)
                P'' G''.

Lemma exec_mono : forall P G lo lc P' G' t (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  li (Hin : In (t, li) P) li' (Hin' : In (t, li') P'),
  exists n, li' = skipn n li.
Proof.
  intros ?????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  - generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    exists 0; auto.
  - destruct P'; [|inversion Hsteps; clarify].
    exploit distinct_step; eauto; intro.
    specialize (IHHsteps s); clarify.
    specialize (IHHsteps _ eq_refl).
    destruct (eq_dec t0 t); clarify.
    + exploit step_thread; eauto; clarify.
      specialize (IHHsteps _ H02 _ Hin'); destruct IHHsteps as [n ?].
      exists (S n); clarify.
    + exploit exec_other_thread; try apply Hexec; eauto.
Qed.

Lemma exec_maintain : forall P G lo lc P' G' t li (Hdistinct : distinct P)
  (Hin : In (t, li) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exec_star_minus t (Some P) G lo lc (Some P') G'.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  - apply exec_refl_m.
  - destruct P'; [|inversion Hsteps; clarify].
    exploit distinct_step; eauto; intro.
    specialize (IHHsteps s); clarify.
    destruct (eq_dec t0 t); clarify.
    { exploit step_thread; eauto; clarify.
      exploit exec_mono; eauto; intros (n & Hmono).
      exploit skip_cons_neq; eauto; clarify. }
    exploit exec_other_thread; try apply Hexec; eauto; clarify.
    specialize (IHHsteps _ eq_refl); clarify.
    eapply exec_step_m; eauto.
Qed.      

Fixpoint t_steps P G t n lo lc P' G' :=
  match n with
  | 0 => lo = [] /\ lc = [] /\ P' = Some P /\ G' = G
  | S n' => exists o c P1 G1, exec P G t o c P1 G1 /\
      exists lo1 lc1 P2 G2 lo2 lc2, exec_star_minus t P1 G1 lo1 lc1 P2 G2 /\
      match P2 with
      | Some P2 => t_steps P2 G2 t n' lo2 lc2 P' G' /\
          lo = opt_to_list o ++ lo1 ++ lo2 /\ lc = opt_to_list c ++ lc1 ++ lc2
      | None => lo = opt_to_list o ++ lo1 /\ lc = opt_to_list c ++ lc1 /\
          P' = None /\ G' = G2 /\ n' = 0
      end
  end.

Lemma exec_minus_exec : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G'),
  exec_star P G lo lc P' G'.
Proof.
  intros; induction Hminus; clarify;
    [apply exec_refl | eapply exec_step; eauto].
Qed.

Lemma exec_other_threads : forall P t li (Hin : In (t, li) P)
  G o c P' G' (Hsteps : exec_star_minus t (Some P) G o c (Some P') G'),
  In (t, li) P'.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit exec_other_thread; eauto.
Qed.

Lemma t_steps_exec : forall t n P G lo lc P' G'
  (Ht_steps : t_steps P G t n lo lc P' G'),
  exec_star (Some P) G lo lc P' G'.
Proof.
  induction n; simpl; intros.
  - clarify; apply exec_refl.
  - destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2 &
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    + repeat rewrite app_assoc; eapply exec_star_trans; [|apply IHn; eauto].
      eapply exec_step; eauto.
      eapply exec_minus_exec; eauto.
    + eapply exec_step; eauto.
      eapply exec_minus_exec; eauto.
Qed.

Lemma t_steps_length : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G') li1 li2
  (Hin : In (t, li1 ++ li2) P) (Hin' : In (t, li2) P'), n = length li1.
Proof.
  induction n; simpl; intros.
  - clarify.
    generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    destruct li1; clarify.
    assert (length (i :: li1 ++ li2) = length li2) by (rewrite H1; auto).
    simpl in *; rewrite app_length in *; omega.
  - destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2 &
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    destruct P1; [|inversion Hminus; clarify].
    exploit distinct_step; eauto; intro Hdistinct1.
    exploit distinct_steps; eauto.
    { eapply exec_minus_exec; eauto. }
    intro Hdistinct'.
    specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1).
    exploit step_thread; eauto; clarify.
    destruct li1; clarify.
    { exploit exec_mono.
      { apply Hdistinct1. }
      { eapply exec_star_trans; [eapply exec_minus_exec | eapply t_steps_exec];
          eauto. }
      { eauto. }
      { eauto. }
      clarify; exploit skip_cons_neq; eauto; clarify. }
    erewrite IHn; eauto.
    eapply exec_other_threads; eauto.
Qed.

Lemma exec_step_inv_m : forall t P G lo lc P' G'
  (Hsteps : exec_star_minus t P G lo lc (Some P') G') o c P'' G'' t'
  (Hstep : exec P' G' t' o c P'' G'') (Hdiff : t' <> t),
  exec_star_minus t P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  intros ????????.
  remember (Some P') as S; generalize dependent P'; induction Hsteps; clarify.
  - generalize (exec_step_m Hdiff Hstep (exec_refl_m _ _ _)); clarsimp.
  - specialize (IHHsteps _ eq_refl _ _ _ _ _ Hstep Hdiff).
    repeat rewrite <- app_assoc; eapply exec_step_m; try apply Hexec; eauto.
Qed.

Lemma t_steps_add_t : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G')
  o c P'' G'' (Hexec : exec P' G' t o c P'' G''),
  t_steps P G t (S n) (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  induction n; simpl; intros.
  - clarify.
    repeat eexists; eauto.
    + apply exec_refl_m.
    + destruct P''; clarify; repeat rewrite app_nil_r; auto.
  - destruct Ht_steps as (o' & c' & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2
      & lc2 & Hminus & Hrest).
    do 5 eexists; eauto.
    do 7 eexists; eauto.
    destruct P2; clarify.
    destruct P1; [|inversion Hminus; clarify].
    generalize (distinct_step Hdistinct Htstep); intro.
    exploit distinct_steps; eauto.
    { eapply exec_minus_exec; eauto. }
    intro Hdistinct'.
    specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1 _ _ _ _ Hexec); clarify.
    split.
    + repeat eexists; eauto.
    + repeat rewrite <- app_assoc; auto.
Qed.

Lemma t_steps_add_other : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G')
  t' o c P'' G'' (Hexec : exec P' G' t' o c P'' G'') (Hdiff : t' <> t)
  (Hnz : n <> 0),
  t_steps P G t n (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  induction n; [clarify | simpl; intros].
  destruct Ht_steps as (o' & c' & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2
    & lc2 & Hminus & Hrest).
  destruct P2; clarify.
  destruct P1; [|inversion Hminus; clarify].
  generalize (distinct_step Hdistinct Htstep); intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro Hdistinct'.
  specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1 _ _ _ _ _ Hexec); clarify.
  do 5 eexists; eauto.
  destruct n.
  - clarify; do 7 eexists; [eapply exec_step_inv_m; eauto|].
    destruct P''; clarify; repeat rewrite app_nil_r;
      repeat rewrite <- app_assoc; auto.
  - do 7 eexists; eauto.
    split; [apply IHn; auto|].
    repeat rewrite <- app_assoc; auto.
Qed.

Lemma t_steps_extend : forall P' G' lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  P G t n lo0 lc0 (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo0 lc0 (Some P') G')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hlen : length li1 <> 0) (Hn : n <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (lo0 ++ lo) (lc0 ++ lc) (Some P'') G''.
Proof.
  intros ???????.
  remember (Some P') as S; remember (Some P'') as S'; generalize dependent P'';
    generalize dependent P'; induction Hsteps; clarify.
  { repeat rewrite app_nil_r; erewrite <- t_steps_length; eauto. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl).
  destruct (eq_dec t0 t); clarify.
  - exploit t_steps_add_t; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
  - exploit t_steps_add_other; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
Qed.

Corollary exec_thread : forall P G t o c P' G' (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G') lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hlen : length li1 <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (opt_to_list o ++ lo) (opt_to_list c ++ lc)
    (Some P'') G''.
Proof.
  intros; eapply t_steps_extend with (n := 1); eauto.
  simpl; repeat eexists; eauto.
  - apply exec_refl_m.
  - clarify; repeat rewrite app_nil_r; auto.
Qed.

Inductive exec_star_t t : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_t P G : exec_star_t t P G [] [] P G
| exec_step_t P G o c P' G' (Hexec : exec P G t o c P' G') lo lc P'' G''
    (Hexec' : exec_star_t t P' G' lo lc P'' G'') :
    exec_star_t t (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc)
                  P'' G''.

Lemma exec_minus_trans : forall t P G P' S G' G'' e1 m1 e2 m2,
  exec_star_minus t (Some P) G e1 m1 (Some P') G' ->
  exec_star_minus t (Some P') G' e2 m2 S G''->
  exec_star_minus t (Some P) G (e1++e2) (m1++m2) S G''.
Proof.
  intros ??????????? Hexec; induction Hexec; clarify.
  repeat rewrite <- app_assoc; eapply exec_step_m; eauto.
Qed.

Lemma exec_minus_env : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G'), G' t = G t.
Proof.
  intros; induction Hminus; auto.
  rewrite IHHminus.
  exploit exec_result; eauto; intros (? & i & li & ? & v & ?); clarify.
  destruct (instr_result t' i (G t') v) as [((((?, ?), ?), u1), ?)|];
    [destruct u1 as [(?, ?)|]|]; clarify.
  unfold upd_env, upd; clarify.
Qed.

Lemma upd_comm : forall (G : env) t t' Gt Gt' (Hdiff : t' <> t),
  upd (upd G t Gt) t' Gt' = upd (upd G t' Gt') t Gt.
Proof.
  intros; extensionality a; unfold upd; clarify.
Qed.

Lemma result_env : forall t t' (Hdiff : t' <> t) u1 G,
  upd_env' G t u1 t' = G t'.
Proof.
  destruct u1 as [(?, ?)|]; unfold upd_env, upd; clarify.
Qed.

Lemma result_comm : forall G u1 u1' t t' (Hdiff : t' <> t),
  upd_env' (upd_env' G t u1) t' u1' = upd_env' (upd_env' G t' u1') t u1.
Proof.
  destruct u1 as [(?, ?)|], u1' as [(?, ?)|]; clarify.
  unfold upd_env; do 2 (rewrite VectorClocks.upd_old; auto).
  apply upd_comm; auto.
Qed.

Lemma exec_swap : forall t P G o c P' G' t' o' c' P'' G''
  (Hdiff : t' <> t) (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G')
  (Hstep' : exec P' G' t' o' c' (Some P'') G'')
  (Hspawn : forall li rest, ~In (t, Spawn t' li :: rest) P)
  (Hwait : forall i rest, In (t, [i]) P -> ~In (t', Wait t :: rest) P)
  (Hjoin : forall u rest rest', In (t, Spawn u [] :: rest) P ->
     ~In (t', Wait u :: rest') P),
  exists P1 G1, exec P G t' o' c' (Some P1) G1 /\
                exec P1 G1 t o c (Some P'') G''.
Proof.
  intros.
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_step; eauto; intro Hdistinct''.
  exploit exec_result; eauto; intros (P'a & i' & li' & P'b & v' & HP' & ?);
    clarify.
  destruct (instr_result t' i' (G' t') v') as [((((?, ?), ?), u1'), ?)|]
    eqn: Hresult'; clarify.
  exploit exec_result; [apply Hstep|]; intros (Pa & i & li & Pb & v & HP & ?);
    clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), u1), ?)|]
    eqn: Hresult; clarify.
  rewrite result_env in Hresult'; auto.
  assert (~In (t', i' :: li') (opt_to_list o1)) as Hout.
  { specialize (Hspawn (i' :: li') li); rewrite in_app in Hspawn; clarify.
    destruct o1; clarify.
    intro; destruct i; clarify. }
  assert (In (t', i' :: li') (Pa ++ (t, i :: li) :: Pb)).
  { assert (In (t', i' :: li') (P'a ++ (t', i' :: li') :: P'b)) as Hin
      by (rewrite in_app; clarify).
    rewrite H2 in Hin; rewrite in_app in *; clarify.
    rewrite in_app in *; destruct Hin; clarify. }
  exploit in_split; eauto; intros (P1a & P1b & HP').
  exploit (result_exec(P := Pa ++ (t, i :: li) :: Pb));
    [apply HP' | setoid_rewrite Hresult'; intro Hstep'1].
  use Hstep'1.
  do 3 eexists; eauto.
  assert (t <> t') as Hdiff' by auto.
  rewrite <- (result_env Hdiff' u1') in Hresult; auto.
  exploit exec_other_thread; try apply Hstep'1.
  { rewrite in_app; clarify. }
  { auto. }
  intro; exploit in_split; eauto; intros (P1'a & P1'b & HP1').
  exploit result_exec; [apply HP1' | setoid_rewrite Hresult; intro Hstep1].
  assert (~In (t, i :: li) (opt_to_list o0)) as Hout'.
  { destruct o0; clarify.
    intro; destruct i'; clarify.
    contradiction H2222.
    assert (In (t, li) (P'a ++ (t', Spawn t (i :: li) :: li') :: P'b)) as Hin
      by (rewrite H2, in_app; clarify).
    rewrite in_map_iff; setoid_rewrite in_app; rewrite in_app in Hin;
      destruct Hin; clarify.
    - do 2 eexists; [|left; eauto]; auto.
    - do 2 eexists; [|right; right; eauto]; auto. }
  assert (P'a ++ (t', li') :: opt_to_list o0 ++ P'b =
    P1'a ++ (t, li) :: opt_to_list o1 ++ P1'b) as Heq.
  { clear - H2 HP' HP1' Hdiff Hdistinct Hdistinct'' Hout Hout'.
    destruct (le_dec (length P1a) (length P1'a)).
    - exploit app_eq_inv_ge; eauto; intros (l1' & ?); clarify; clear HP1' l.
      destruct l1'; clarify.
      assert (length (opt_to_list o0) <= length l1').
      { destruct o0; clarify.
        destruct l1'; clarify; [|omega].
        contradiction Hout'; auto. }
      exploit app_eq_inv_ge; eauto; clarify.
      exploit NoDup_inj.
      { eauto. }
      { rewrite map_app; apply nth_error_split. }
      { rewrite HP', map_app, nth_error_plus; instantiate (1 := S _); simpl.
        rewrite map_app; apply nth_error_split. }
      rewrite (split_app P1a), app_assoc in HP'; intro.
      exploit app_eq_inv; try apply HP'; clarsimp.
      destruct (le_dec (length P'a) (length P1a)).
      + exploit app_eq_inv_ge; eauto; intros (l' & ?); clarify;
          clear H2 l.
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega.
      + symmetry in H2; exploit app_eq_inv_ge; eauto; [omega |
          intros (l' & ?); clarify; clear H2 n].
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega.
    - symmetry in HP1'; exploit app_eq_inv_ge; eauto; [omega |
        intros (l1' & ?); clarify; clear HP1' n].
      destruct l1'; clarify.
      rewrite <- app_assoc in HP'.
      exploit NoDup_inj.
      { eauto. }
      { rewrite map_app; apply nth_error_split. }
      { rewrite HP', map_app; apply nth_error_split. }
      repeat rewrite map_length; intro; exploit app_eq_inv; eauto; clarify.
      rewrite (split_app P1'a), app_assoc, app_assoc in H2.
      destruct (le_dec (length P'a)
        (length (((P1'a ++ [(t, li)]) ++ opt_to_list o1) ++ l1'))).
      + exploit app_eq_inv_ge; eauto; intros (l' & ?); clarify.
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite app_assoc, map_app; apply nth_error_split. }
        omega.
      + symmetry in H2; exploit app_eq_inv_ge; eauto; [omega |
          intros (l' & ?); clarify; clear H2 n].
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app, nth_error_plus; instantiate (2 := S _); simpl.
          rewrite app_assoc, map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite app_assoc, map_app, nth_error_plus;
            instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega. }
  rewrite Heq, result_comm; auto; apply Hstep1.
  - destruct i; simpl in *; inversion Hresult; subst; auto.
    + intro Hin; contradiction H0.
      rewrite HP'; rewrite map_app, in_app.
      do 2 (rewrite map_app, in_app in Hin; clarify).
      destruct o0; clarify; destruct i'; clarify.
      contradiction H2222; rewrite H2, map_app, in_app; clarify.
    + rewrite HP', in_app in *; clarify.
      rewrite in_app; auto.
    + clarify.
  - destruct i'; simpl in *; inversion Hresult'; subst; auto.
    + intro Hin; contradiction H2222.
      rewrite H2; rewrite map_app, in_app in *; clarify.
      rewrite map_app, in_app; auto.
    + rewrite H2, in_app in H2222; rewrite in_app; clarify.
      rewrite in_app in H2222; destruct H2222; clarify.
      * specialize (Hwait i li'); rewrite in_app in Hwait; clarify.
      * destruct o1; clarify; destruct i; clarify.
        specialize (Hjoin t0 li li'); rewrite in_app in Hjoin; clarify.
    + clarify.
Qed.

Lemma exec_later_t : forall t P' G' lo lc P'' G''
  (Hrest : exec_star_minus t P' G' lo lc (Some P'') G'')
  P G o c (Htstep : exec P G t o c P' G') (Hdistinct : distinct P)
  (Hspawn : forall u li rest, ~In (t, Spawn u li :: rest) P)
  (Hlast : forall i, ~In (t, [i]) P),
  exists P1 G1, exec_star_minus t (Some P) G lo lc (Some P1) G1 /\
    exec P1 G1 t o c (Some P'') G''.
Proof.
  intros ????????.
  remember (Some P'') as S; generalize dependent P'';
    induction Hrest; clarify.
  { do 3 eexists; eauto; apply exec_refl_m. }
  specialize (IHHrest _ eq_refl).
  destruct P'; clarify; [|inversion Hrest; clarify].
  exploit exec_swap; eauto.
  { intros; exploit Hlast; eauto. }
  { intros; exploit Hspawn; eauto. }
  intros (P1 & G1 & Ht' & Ht).
  exploit distinct_step; eauto; intro Hdistinct1.
  specialize (IHHrest _ _ _ _ Ht Hdistinct1).
  assert (exists li, In (t, li) P0) as (li & ?).
  { generalize (exec_result Htstep); clarify.
    eexists; rewrite in_app; clarify. }
  exploit exec_other_thread; eauto; intro.
  use IHHrest.
  use IHHrest.
  clarify; repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - intro Hin1; generalize (NoDup_id_inj _ _ (t, li) Hdistinct1 Hin1); clarify.
    exploit Hlast; eauto.
  - intro Hin1; generalize (NoDup_id_inj _ _ (t, li) Hdistinct1 Hin1); clarify.
    exploit Hspawn; eauto.
Qed.

Lemma exec_sooner_t : forall t P G lo lc P' G'
  (Hrest : exec_star_minus t (Some P) G lo lc (Some P') G')
  P'' G'' o c (Htstep : exec P' G' t o c (Some P'') G'')
  (Hdistinct : distinct P)
  (Hwait : forall u rest, ~In (t, Wait u :: rest) P)
  li (Ht_start : In (t, li) P),
  exists P1 G1, exec P G t o c P1 G1 /\
    exec_star_minus t P1 G1 lo lc (Some P'') G''.
Proof.
  intros ????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hrest; clarify.
  { do 3 eexists; eauto; apply exec_refl_m. }
  destruct P'; clarify; [|inversion Hrest; clarify].
  specialize (IHHrest _ eq_refl _ eq_refl).
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit exec_other_thread; eauto; intro Ht_start'.
  specialize (IHHrest _ _ _ _ Htstep Hdistinct').
  use IHHrest.
  specialize (IHHrest _ Ht_start').
  destruct IHHrest as (P1 & G1 & Htstep' & Hrest').
  destruct P1; clarify; [|inversion Hrest'; clarify].
  assert (t <> t') by auto.
  exploit exec_swap; try (apply Hdistinct); eauto.
  { intros ?? Hspawn.
    generalize (exec_result Hexec); intros (P1 & i' & li' & Hresult); clarify.
    generalize (NoDup_id_inj _ _ (t', i' :: li') Hdistinct Hspawn);
      rewrite in_app; clarify.
    contradiction Hresult22222; rewrite in_map_iff; exists (t, li); auto. }
  clarify; repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - intro Hin'; generalize (NoDup_id_inj _ _ (t, li) Hdistinct' Hin'); clarify.
    exploit Hwait; eauto.
Qed.

Lemma exec_t_exec : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc P' G'),
  exec_star P G lo lc P' G'.
Proof.
  intros; induction Hsteps; clarify;
    [apply exec_refl | eapply exec_step; eauto].
Qed.

Lemma exec_step_inv_t : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc (Some P') G') o c P'' G''
  (Hstep : exec P' G' t o c P'' G''),
  exec_star_t t P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  intros ????????.
  remember (Some P') as S; generalize dependent P'; induction Hsteps; clarify.
  - generalize (exec_step_t Hstep (exec_refl_t _ _ _)); clarsimp.
  - specialize (IHHsteps _ eq_refl _ _ _ _ Hstep).
    repeat rewrite <- app_assoc; eapply exec_step_t; eauto.
Qed.

Lemma exec_minus_ops : forall t P G lo lc P' G'
  (Hsteps : exec_star_minus t P G lo lc P' G'),
  Forall (fun c => beq (thread_of c) t = false) lc.
Proof.
  intros; induction Hsteps; clarify.
  rewrite Forall_app; clarify.
  inversion Hexec; constructor; auto; unfold beq; clarify.
Qed.

Lemma t_steps_plus : forall t n1 n2 P G lo lc P' G'
  (Ht_steps : t_steps P G t (n1 + n2) lo lc (Some P') G'),
  exists lo1 lc1 P1 G1 lo2 lc2, t_steps P G t n1 lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t n2 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  induction n1; simpl; intros.
  - repeat eexists; auto.
  - destruct Ht_steps as (o & c & P1 & G1 & Hstep & lo1 & lc1 & P2 & G2 & lo2 & 
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    specialize (IHn1 _ _ _ _ _ _ _ Hrest1);
      destruct IHn1 as (lo1' & lc1' & P1' & G1' & lo2' & lc2' & Hsteps1 &
      Hsteps2 & ?); clarify.
    exists (opt_to_list o ++ lo1 ++ lo1'), (opt_to_list c ++ lc1 ++ lc1'),
      P1', G1', lo2', lc2'; clarsimp.
    repeat eexists; eauto; clarify.
Qed.

Lemma exec_ops : forall P G t o c P' G' (Hexec : exec P G t o c P' G'),
  Forall (fun x => beq (thread_of x) t = true) (opt_to_list c).
Proof.
  intros; inversion Hexec; constructor; auto; unfold beq; clarify.
Qed.

Lemma exec_keep : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P), exists n, In (t, skipn n li) P'.
Proof.
  intros ????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  { exists 0; auto. }
  destruct P'; [|inversion Hsteps; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHsteps _ Hdistinct' eq_refl _ eq_refl).
  destruct (eq_dec t0 t); subst.
  - exploit step_thread; eauto; intros (? & ? & ? & Hin').
    specialize (IHHsteps _ _ Hin'); destruct IHHsteps as (n & ?); clarify.
    exists (S n); auto.
  - exploit exec_other_thread; eauto.
Qed.

Lemma step_instr : forall t i li P (Hin : In (t, i :: li) P)
  (Hdistinct : distinct P) G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  n (Hin' : In (t, skipn n li) P'),
  exists P1 G1 lo1 lc1 o c P1' G1' lo2 lc2,
    exec_star_minus t (Some P) G lo1 lc1 (Some P1) G1 /\
    exec P1 G1 t o c (Some P1') G1' /\
    exec_star (Some P1') G1' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros; remember (Some P) as P0; remember (Some P') as Pf;
    generalize dependent P'; generalize dependent P; induction Hsteps;
    clarify.
  - generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    exploit skip_cons_neq; eauto; clarify.
  - destruct P'; [|inversion Hsteps; clarify].
    destruct (eq_dec t0 t).
    + subst.
      repeat eexists; eauto.
      * apply exec_refl_m.
      * auto.
      * auto.
    + exploit exec_other_thread; try apply Hin; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit IHHsteps; eauto; clarify.
      repeat eexists; eauto.
      * eapply exec_step_m; eauto.
      * clarsimp.
      * clarsimp.
Qed.

Lemma prog_step : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  Forall prog_op (opt_to_list c).
Proof.
  intros; inversion Hstep; clarify; constructor; simpl; auto.
Qed.

Lemma prog_steps : forall P G lo lc P' G' (Hsteps : exec_star P G lo lc P' G'),
  Forall prog_op lc.
Proof.
  intros; induction Hsteps; clarify.
  rewrite Forall_app; clarify; eapply prog_step; eauto.
Qed.

Definition accesses i := match i with
| Load _ p => Some p
| Store p _ => Some p
| Lock m => Some (m, 0)
| Unlock m => Some (m, 0)
| _ => None
end.

Lemma exec_accesses : forall P G t (Hdistinct : distinct P) o c P' G'
  (Hexec : exec P G t o c P' G') i rest (Hi : In (t, i :: rest) P) l,
  (match c with Some c => loc_of c = l | None => False end) <->
  accesses i = Some l.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  inversion Hexec; exploit distinct_thread; eauto; clarify; split; clarify.
Qed.

Inductive exec_star_rev : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_rev P G : exec_star_rev P G [] [] P G
| exec_step_rev P G lo lc P' G' (Hexec : exec_star_rev P G lo lc (Some P') G')
    t o c P'' G'' (Hexec' : exec P' G' t o c P'' G'') :
    exec_star_rev P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.

Lemma exec_rev_trans : forall P G P' S G' G'' e1 m1 e2 m2,
  exec_star_rev P G e1 m1 P' G' ->
  exec_star_rev P' G' e2 m2 S G'' ->
  exec_star_rev P G (e1++e2) (m1++m2) S G''.
Proof.
  intros ?????????? Hexec Hexec'; revert Hexec; induction Hexec'; clarify.
  - clarsimp.
  - repeat rewrite app_assoc; eapply exec_step_rev; eauto.
Qed.

Lemma exec_rev_some : forall P G lo lc P' G'
  (Hrev : exec_star_rev P G lo lc (Some P') G'), exists P0, P = Some P0.
Proof.
  intros; remember (Some P') as P1; generalize dependent P';
    induction Hrev; clarify; eauto.
Qed.

Lemma exec_rev : forall P G lo lc P' G',
  exec_star P G lo lc P' G' <-> exec_star_rev P G lo lc P' G'.
Proof.
  split; intros; induction H.
  - apply exec_refl_rev.
  - eapply exec_rev_trans; eauto.
    apply (exec_step_rev (exec_refl_rev _ _) Hexec).
  - apply exec_refl.
  - exploit exec_rev_some; eauto; clarify.
    eapply exec_step_inv; eauto.
Qed.

Lemma step_thread' : forall P G t o c P' G'
   (Hstep : exec P G t o c (Some P') G'),
  exists i li', In (t, i :: li') P /\ In (t, li') P'.
Proof.
  intros; inversion Hstep; clarify; repeat eexists; eauto; rewrite in_app;
    clarify.
Qed.

Lemma exec_t_steps : forall P G lo lc P' G'
  (Hexec : exec_star P G lo lc (Some P') G') t,
  exists n lo1 lc1 P1 G1 lo2 lc2, exec_star_minus t P G lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t n lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros; remember (Some P') as P2; generalize dependent P'; induction Hexec;
    clarify.
  - exists 0; repeat eexists; try apply exec_refl_m; auto.
  - specialize (IHHexec _ eq_refl); destruct IHHexec as (n & ?); clarify.
    destruct (eq_dec t0 t).
    + subst; exists (S n); do 7 eexists; [apply exec_refl_m | clarify].
      repeat eexists; eauto; simpl; eauto.
    + do 8 eexists; [eapply exec_step_m; eauto|].
      split; eauto; clarsimp.
Qed.

Lemma t_steps_extend' : forall P' G' lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  P G t n lo0 lc0 (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo0 lc0 (Some P') G')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hn : n <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (lo0 ++ lo) (lc0 ++ lc) (Some P'') G''.
Proof.
  intros ???????.
  remember (Some P') as S; remember (Some P'') as S'; generalize dependent P'';
    generalize dependent P'; induction Hsteps; clarify.
  { clarsimp.
    erewrite <- t_steps_length; eauto. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl).
  destruct (eq_dec t0 t); clarify.
  - exploit t_steps_add_t; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
  - exploit t_steps_add_other; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
Qed.

Lemma exec_thread' : forall P G t o c P' G' (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G') lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (opt_to_list o ++ lo) (opt_to_list c ++ lc)
    (Some P'') G''.
Proof.
  intros; eapply t_steps_extend' with (n := 1); eauto.
  simpl; repeat eexists; eauto.
  - apply exec_refl_m.
  - clarsimp.
Qed.

Lemma step_thread0 : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  exists i li, In (t, i :: li) P.
Proof.
  intros; inversion Hstep; clarify; repeat eexists; rewrite in_app; clarify.
Qed.

Lemma step_invariant : forall P G lo lc P' G' (I : state -> Prop)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (HI : I P')
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hdistinct : distinct P)
  (HnotI : forall P (Hdistinct : distinct P) n (Hn : n < length li1)
                  (Ht : In (t, skipn n li1 ++ li2) P), ~I P),
  exists P'' G'' lo1 lc1 lo2 lc2, exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    In (t, li2) P'' /\ exec_star (Some P'') G'' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros; destruct li1.
  { exists P, G, [], [], lo, lc; repeat split; clarify; apply exec_refl. }
  remember (Some P) as S; remember (Some P') as S';
    generalize dependent li2; generalize dependent li1; revert i;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  { specialize (HnotI _ Hdistinct 0); clarify. }
  destruct P'; [|inversion Hsteps; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHsteps _ eq_refl Hdistinct' _ eq_refl); clarify.
  destruct (eq_dec t t0); subst.
  - exploit step_thread; eauto; intros (? & ? & ? & Ht'); clarify.
    destruct li1; clarify.
    + exists s, G', (opt_to_list o), (opt_to_list c), lo, lc; clarify.
      eapply exec_step'; [eauto | apply exec_refl | clarsimp | clarsimp].
    + specialize (IHHsteps _ _ _ Ht'); use IHHsteps.
      destruct IHHsteps as (Pa & Ga & lo1 & lc1 & lo2 & lc2 & ?).
      exists Pa, Ga, (opt_to_list o ++ lo1), (opt_to_list c ++ lc1), lo2, lc2;
        clarsimp.
      eapply exec_step; eauto.
      { apply (HnotI _ Hdistinct0 (S n)); auto. }
  - exploit exec_other_thread; eauto; intro Hin.
    specialize (IHHsteps _ _ _ Hin HnotI);
      destruct IHHsteps as (Pa & Ga & lo1 & lc1 & lo2 & lc2 & ?).
    exists Pa, Ga, (opt_to_list o ++ lo1), (opt_to_list c ++ lc1), lo2, lc2;
      clarsimp.
    eapply exec_step; eauto.
Qed.

Lemma exec_keep' : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P) li' (Hin' : In (t, li') P'),
  exists n, li' = skipn n li.
Proof.
  intros; exploit exec_keep; eauto; clarify.
  exploit distinct_steps; eauto; intro.
  exploit distinct_in; [eauto | apply Hin' | eauto | clarify; eauto].
Qed.

Lemma exec_length : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G'),
  length P <= length P'.
Proof.
  intros; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; induction Hsteps; clarify.
  destruct P'0; [|inversion Hsteps].
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  specialize (IHHsteps _ eq_refl); rewrite app_length in *; simpl in *.
  rewrite app_length in *; omega.
Qed.

Lemma in_steps_rev : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P'),
  (exists li1, In (t, li1 ++ li) P) \/ (forall li, ~In (t, li) P) /\
  exists P1 G1 lo1 lc1 t' li1 rest lo2 lc2 P1',
    exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t', Spawn t (li1 ++ li) :: rest) P1 /\
    exec P1 G1 t' (Some (fork t' t)) None (Some P1') G1 /\
    exec_star (Some P1') G1 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ fork t' t :: lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb; generalize dependent P;
    induction Hsteps; clarify.
  - left; exists []; auto.
  - destruct P'0; [|inversion Hsteps].
    exploit distinct_step; eauto; intro.
    exploit IHHsteps; eauto; intros [IH | IH].
    + destruct IH as (li1 & ?).
      exploit in_step_rev; eauto; intros [? | [(? & i & ?) | (rest & ?)]];
        eauto.
      * left; exists (i :: li1); clarify.
      * right.
        exploit in_split; eauto; clarify.
        exploit exec_next; eauto; clarify.
        split; [|repeat eexists; eauto; try apply exec_refl; auto].
        repeat intro; contradiction H22222.
        rewrite in_map_iff; do 2 eexists; eauto; clarify.
    + right; clarify.
      split.
      * repeat intro.
        destruct (eq_dec t0 t); [subst; exploit step_thread |
          exploit exec_other_thread]; eauto; clarify; eapply IH1; eauto.
      * do 11 eexists; [|split; eauto].
        { eapply exec_step; eauto. }
        repeat (split; eauto); rewrite <- app_assoc; auto.
Qed.

Lemma in_steps_rev2 : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P'),
  (exists li1, In (t, li1 ++ li) P) \/ (forall li, ~In (t, li) P) /\
  exists P1 G1 lo1 lc1 t0 t' li' rest li1 lo2 lc2 P1',
    exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t0, Spawn t' li' :: rest) P1 /\
    In (t0, li1 ++ Spawn t' li' :: rest) P /\
    exec P1 G1 t0 (Some (fork t0 t')) None (Some P1') G1 /\
    exec_star (Some P1') G1 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ fork t0 t' :: lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros.
  remember (Some P) as Pa; remember (Some P') as Pb; generalize dependent P;
    induction Hsteps; clarify.
  - left; exists []; auto.
  - destruct P'0; [|inversion Hsteps].
    exploit distinct_step; eauto; intro.
    exploit IHHsteps; eauto; intros [IH | IH].
    + destruct IH as (li1 & ?).
      exploit in_step_rev; eauto; intros [? | [(? & i & ?) | (rest & ?)]];
        eauto.
      * left; exists (i :: li1); clarify.
      * right.
        exploit in_split; eauto; clarify.
        exploit exec_next; eauto; clarify.
        split.
        { repeat intro; contradiction H22222.
          rewrite in_map_iff; do 2 eexists; eauto; clarify. }
        { repeat eexists; try apply exec_refl; eauto.
          instantiate (1 := []); rewrite in_app; clarify. }
    + right; destruct IH as (IH1 & ? & ? & ? & ? & t' & ? & ? & ? & rest & ?);
        clarify.
      split.
      * repeat intro.
        destruct (eq_dec t0 t); [subst; exploit step_thread |
          exploit exec_other_thread]; eauto; clarify; eapply IH1; eauto.
      * exploit in_step_rev; try apply Hexec; eauto;
          intros [? | [(? & i & ?) | ?]].
        { do 13 eexists; [|split; eauto].
          { eapply exec_step; eauto. }
          repeat (split; eauto); rewrite <- app_assoc; auto. }
        { clarify; do 13 eexists; [|split; eauto].
          { eapply exec_step; eauto. }
          repeat (split; eauto); try solve [rewrite <- app_assoc; auto].
          instantiate (1 := i :: rest); auto. }
        { clarify; do 13 eexists; [apply exec_refl|].
          split; eauto.
          split; [instantiate (1 := []); auto|].
          assert (G' = G /\ o = Some (fork t0 t') /\ c = None).
          { exploit in_split; eauto; clarify.
            inversion Hexec; subst; exploit distinct_thread;
              try apply Hdistinct; eauto; clarify. }
          clarify; eauto. }
Qed.

Lemma exec_t_maintain : forall P G lo lc P' G' t li (Hdistinct : distinct P)
  (Hin : In (t, li) P) (Hsteps : exec_star_t t (Some P) G lo lc (Some P') G')
  (Hin' : In (t, li) P'), P' = P /\ G' = G /\ lo = [] /\ lc = [].
Proof.
  intros; inversion Hsteps; clarify.
  destruct P'0; [|inversion Hexec'; clarify].
  exploit step_thread; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit exec_mono; eauto.
  { eapply exec_t_exec; eauto. }
  clarify.
  exploit skip_cons_neq; eauto; clarify.
Qed.

Lemma exec_t_segment : forall t P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star_t t (Some P) G lo lc (Some P') G')
  li1 li2 li3 (Hin : In (t, li1 ++ li2 ++ li3) P) (Hin' : In (t, li3) P'),
  exists P1 G1 lo1 lc1 lo2 lc2, exec_star_t t (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t, li2 ++ li3) P1 /\ exec_star_t t (Some P1) G1 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros ?????????; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; induction Hsteps; clarify.
  - exploit distinct_in; [eauto | apply Hin | apply Hin' | clarify].
    rewrite app_assoc in H; exploit app_nil_inv; eauto; clear H; intro.
    exploit app_eq_nil; eauto; clarify.
    repeat eexists; try apply exec_refl_t; auto.
  - destruct P'0; [|inversion Hsteps].
    exploit distinct_step; eauto; intro.
    destruct li1.
    { do 7 eexists; [apply exec_refl_t | clarify].
      eapply exec_step_t; eauto. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (v & ?).
    destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
    exploit IHHsteps; eauto.
    { rewrite in_app; clarify. }
    intros (? & ? & ? & ? & ? & ? & Hsteps' & ?).
    clarify; do 7 eexists; [eapply exec_step_t; try apply Hsteps'; eauto |
      clarify].
    split; eauto.
    repeat rewrite <- app_assoc; auto.
Qed.

Lemma exec_t_rev_inv : forall t P G lo lc P' G'
  (Ht : exec_star_t t P G lo lc P' G'),
  P' = P /\ G' = G /\ lo = [] /\ lc = [] \/
    exists P1 G1 lo1 lc1 o c, exec_star_t t P G lo1 lc1 (Some P1) G1 /\
      exec P1 G1 t o c P' G' /\ lo = lo1 ++ opt_to_list o /\
      lc = lc1 ++ opt_to_list c.
Proof.
  intros; induction Ht; clarify.
  right; destruct IHHt; clarify.
  - repeat eexists; eauto; try apply exec_refl_t; clarsimp.
  - repeat eexists; eauto; try eapply exec_step_t; eauto; clarsimp.
Qed.

Fixpoint to_mem' G t li vs :=
  match li with
  | [] => Some ([], G, vs, [])
  | i :: li =>
      match i with
      | Assign a e => to_mem' (upd G a (eval G e)) t li vs
      | Load a x => match vs with [] => None | v :: vs =>
          match to_mem' (upd G a v) t li vs with None => None
          | Some (lc, G, vs, cond) => Some (Read t x v :: lc, G, vs, cond) end
          end
      | Store x e => match to_mem' G t li vs with None => None
          | Some (lc, G', vs, cond) =>
            Some (Write t x (eval G e) :: lc, G', vs, cond)
          end
      | Lock m => match to_mem' G t li vs with None => None
          | Some (lc, G, vs, cond) => Some (Acq t m :: lc, G, vs, cond) end
      | Unlock m => match to_mem' G t li vs with None => None
          | Some (lc, G, vs, cond) => Some (Rel t m :: lc, G, vs, cond) end
      | Assert_le e1 e2 => match to_mem' G t li vs with None => None
          | Some (lc, G', vs, cond) =>
            Some (lc, G', vs, (eval G e1 <= eval G e2) :: cond)
          end
      | _ => to_mem' G t li vs
      end
  end.

Lemma to_mem'_app : forall t li1 li2 G vs lc G' vs' cond,
  to_mem' G t (li1 ++ li2) vs = Some (lc, G', vs', cond) <->
  match to_mem' G t li1 vs with None => False
  | Some (lc1, G1, vs1, cond1) => match to_mem' G1 t li2 vs1 with None => False
  | Some (lc2, G2, vs2, cond2) => lc = lc1 ++ lc2 /\ G' = G2 /\ vs' = vs2 /\
                                  cond = cond1 ++ cond2 end end.
Proof.
  induction li1; clarify.
  - destruct (to_mem' G t li2 vs) as [(((?, ?), ?), ?)|]; split; clarify.
  - assert (forall c G1 vs1, match to_mem' G1 t (li1 ++ li2) vs1 with
      | Some (lc0, G0, vs0, cond0) => Some (c :: lc0, G0, vs0, cond0)
      | None => None end = Some (lc, G', vs', cond) <->
      match match to_mem' G1 t li1 vs1 with
            | Some (lc0, G0, vs0, cond0) => Some (c :: lc0, G0, vs0, cond0)
            | None => None end with
      | Some (lc1, G1, vs1, cond1) =>
          match to_mem' G1 t li2 vs1 with
          | Some (lc2, G2, vs2, cond2) => lc = lc1 ++ lc2 /\ G' = G2 /\
                                          vs' = vs2 /\ cond = cond1 ++ cond2
          | None => False end
      | None => False end).
    { intros.
      specialize (IHli1 li2 G1 vs1).
      destruct (to_mem' G1 t li1 vs1) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' n t li2 l0) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' G1 t (li1 ++ li2) vs1) as [(((?, ?), ?), ?)|];
        clarify.
      * specialize (IHli1 l0 n l5 l6); destruct IHli1; split; clarify.
      * specialize (IHli1 (l ++ l2) n0 l3 (l1 ++ l4)); destruct IHli1; clarify.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto. }
    destruct a; clarify.
    + destruct vs; [split|]; clarify.
    + specialize (IHli1 li2 G vs).
      destruct (to_mem' G t li1 vs) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' n t li2 l0) as [(((?, ?), ?), ?)|]; clarify.
      destruct (to_mem' G t (li1 ++ li2) vs) as [(((?, ?), ?), ?)|];
        clarify.
      * specialize (IHli1 l0 n l5 l6); destruct IHli1; split; clarify.
      * specialize (IHli1 (l ++ l2) n0 l3 (l1 ++ l4)); destruct IHli1; clarify.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto.
      * split; clarify.
        destruct x as (((?, ?), ?), ?); clarify.
        rewrite IHli1 in *; auto.
Qed.

Definition until_last cond li n G' := Forall id cond \/
  exists e1 e2, nth_error li (n - 1) = Some (Assert_le e1 e2) /\
  ~eval G' e1 <= eval G' e2 /\ Forall id (removelast cond) /\ ~last cond True.

Lemma until_last_nil : forall li n G, until_last [] li n G.
Proof.
  unfold until_last; clarify.
Qed.
Hint Resolve until_last_nil.

Lemma t_steps_mem' : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : t_steps P G t n lo lc P' G') li (Hin : In (t, li) P),
  exists vs vs' cond, to_mem' (G t) t (firstn n li) vs =
    Some (filter (fun c => beq (thread_of c) t) lc, G' t, vs', cond) /\
    until_last cond li n (G' t).
Proof.
  induction n; intros.
  { exists [], [], []; clarify. }
  simpl in Hsteps.
  destruct Hsteps as (? & c & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus & ?);
    clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & ?); clarify.
  assert (li = i :: rest).
  { exploit distinct_in; [eauto | eauto | apply split_in | clarify]. }
  assert (match li with [] => [] | a :: l => a :: firstn n l end =
    [i] ++ firstn n rest) as Heq by clarify; subst; rewrite Heq.
  setoid_rewrite to_mem'_app.
  assert (exists lcr, lc = opt_to_list c ++ lcr) as (lcr & ?).
  { destruct P2; clarify; eauto. }
  subst.
  assert (exists vs vs' cond, to_mem' match instr_result t i (G t) v with
    Some (_, _, _, u, _) => upd_env' G t u t | None => G t end t (firstn n rest)
    vs = Some (filter (fun c => beq (thread_of c) t) lcr, G' t, vs', cond) /\
    until_last cond rest n (G' t)) as (vs & vs' & cond & Hm2 & ?).
  { exploit exec_minus_ops; eauto; intro Hops'.
    destruct P1; [|inversion Hminus]; clarify.
    - exploit distinct_step; eauto; intro.
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
      destruct P2; clarify.
      + exploit exec_other_threads; try apply Hminus; try apply split_in; intro.
        exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
        exploit IHn; eauto.
        intros (vs & vs' & cond & Heq); exists vs, vs', cond.
        erewrite exec_minus_env in Heq; eauto.
        exploit app_inv_head; eauto; clarify.
        rewrite filter_app, (filter_none _ Hops'); auto.
      + exploit app_inv_head; eauto; clarify.        
        rewrite (filter_none _ Hops').
        rewrite (exec_minus_env Hminus); exists [], [], []; clarify.
    - exploit app_inv_head; eauto; clarify.
      exists [], [], [].
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  }
  assert (forall i, until_last cond (i :: rest) (S n) (G' t)).
  { unfold until_last in *; clarify.
    destruct n; clarify.
    rewrite <- minus_n_O in *; right; repeat eexists; eauto. }
  exists (match i with Load _ _ => v :: vs | _ => vs end), vs',
    (match i with Assert_le e1 e2 => (eval (G t) e1 <= eval (G t) e2) :: cond
     | _ => cond end); destruct i; clarify.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - destruct (le_dec (eval (G t) e1) (eval (G t) e2)); clarify.
    + unfold until_last in *; clarify; destruct n; clarify.
      rewrite <- minus_n_O in *; right; do 3 eexists; eauto.
    + inversion Hminus; clarify.
      inversion H; clarify.
      right; simpl; repeat eexists; eauto.
Qed.

Lemma t_steps_mem_Some : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : t_steps P G t n lo lc (Some P') G') li (Hin : In (t, li) P),
  exists vs vs' cond, to_mem' (G t) t (firstn n li) vs =
    Some (filter (fun c => beq (thread_of c) t) lc, G' t, vs', cond) /\
    Forall id cond.
Proof.
  induction n; intros.
  { exists [], [], []; clarify. }
  simpl in Hsteps.
  destruct Hsteps as (? & c & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus & ?);
    clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & ?); clarify.
  assert (li = i :: rest).
  { exploit distinct_in; [eauto | eauto | apply split_in | clarify]. }
  assert (match li with [] => [] | a :: l => a :: firstn n l end =
    [i] ++ firstn n rest) as Heq by clarify; subst; rewrite Heq.
  setoid_rewrite to_mem'_app.
  assert (exists lcr, lc = opt_to_list c ++ lcr) as (lcr & ?).
  { destruct P2; clarify; eauto. }
  subst.
  assert (exists vs vs' cond, to_mem' match instr_result t i (G t) v with
    Some (_, _, _, u, _) => upd_env' G t u t | None => G t end t (firstn n rest)
    vs = Some (filter (fun c => beq (thread_of c) t) lcr, G' t, vs', cond) /\
    Forall id cond) as (vs & vs' & cond & Hm2 & ?).
  { exploit exec_minus_ops; eauto; intro Hops'.
    destruct P1; [|inversion Hminus]; clarify.
    exploit distinct_step; eauto; intro.
    destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
    destruct P2; clarify.
    exploit exec_other_threads; try apply Hminus; try apply split_in; intro.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit IHn; eauto.
    intros (vs & vs' & cond & Heq); exists vs, vs', cond.
    erewrite exec_minus_env in Heq; eauto.
    exploit app_inv_head; eauto; clarify.
    rewrite filter_app, (filter_none _ Hops'); auto. }
  exists (match i with Load _ _ => v :: vs | _ => vs end), vs',
    (match i with Assert_le e1 e2 => (eval (G t) e1 <= eval (G t) e2) :: cond
     | _ => cond end); destruct i; clarify.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - inversion Hminus; clarify.
Qed.

Lemma to_mem_conds : forall t li G vs lc G' vs'
  (Hmem : to_mem' G t li vs = Some (lc, G', vs', [])),
  Forall (fun i => match i with Assert_le _ _ => False | _ => True end) li.
Proof.
  induction li; clarify.
  destruct a; constructor; clarify; eauto.
  - destruct vs; clarify.
    destruct x0 as (((?, ?), ?), ?); clarify; eauto.
  - destruct x0 as (((?, ?), ?), ?); clarify; eauto.
  - destruct x as (((?, ?), ?), ?); clarify; eauto.
  - destruct x as (((?, ?), ?), ?); clarify; eauto.
  - destruct x as (((?, ?), ?), ?); clarify.
  - destruct x as (((?, ?), ?), ?); clarify; eauto.
Qed.

Lemma until_last_cons : forall cond i li n G
  (Huntil : until_last cond (i :: li) (S n) G)
  (Hi : match i with Assert_le _ _ => False | _ => True end),
  until_last cond li n G.
Proof.
  unfold until_last; clarify.
  destruct n; clarify.
  rewrite <- minus_n_O; right; repeat eexists; eauto.
Qed.

Lemma until_last_app : forall cond1 cond2 li n G'
  (Huntil : until_last (cond1 ++ cond2) li n G'),
  Forall id cond1 \/ cond2 = [] /\ Forall id (removelast cond1).
Proof.
  unfold until_last; intros.
  rewrite Forall_app in Huntil; clarify.
  rewrite removelast_app in *; destruct cond2; clarify;
    [|rewrite firstn_length', Forall_app in *; [clarify | omega]].
  rewrite app_nil_r, plus_0_r, <- removelast_firstn_eq in *; auto.
Qed.

Lemma t_minus : forall t P G lo lc P' G' t'
  (Hsteps : exec_star_t t P G lo lc P' G') (Hdiff : t' <> t),
  exec_star_minus t' P G lo lc P' G'.
Proof.
  intros; induction Hsteps; clarify; econstructor; eauto.
Qed.

Lemma exec_rd_ops : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  Forall (fun x => VectorClocks.thread_of x = t) (opt_to_list o).
Proof.
  intros; inversion Hstep; clarify.
Qed.

Lemma final_steps : forall P (Hfinal : final_state P)
  G lo lc P' G' (Hsteps : exec_star P G lo lc P' G'),
  P' = P /\ G' = G /\ lo = [] /\ lc = [].
Proof.
  intros; inversion Hsteps; clarify.
  inversion Hexec; subst; rewrite Forall_app in *; clarify;
    inversion Hfinal2; clarify.
Qed.

Lemma exec_star_t_steps : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t (Some P) G lo lc P' G'),
  exists n, t_steps P G t n lo lc P' G'.
Proof.
  intros; remember (Some P) as Pa; generalize dependent P; induction Hsteps;
    clarify.
  - exists 0; simpl; auto.
  - destruct P'.
    + specialize (IHHsteps _ eq_refl); destruct IHHsteps as (n & ?);
        exists (S n); simpl.
      repeat eexists; eauto.
      { apply exec_refl_m. }
      clarify.
    + inversion Hsteps; clarify.
      exists 1; simpl.
      do 5 eexists; eauto.
      do 4 eexists; exists [], []; split; [apply exec_refl_m | clarify].
Qed.

Lemma exec_other_thread' : forall P G t o c P' G' t' li (Hin : In (t', li) P)
  li' (Hin' : In (t', li') P') (Hstep : exec P G t o c (Some P') G')
  (Ht' : t' <> t) (Hdistinct : distinct P), li = li'.
Proof.
  intros; exploit exec_other_thread; try apply Hstep; eauto; intro.
  exploit distinct_step; eauto; intro.
  eapply distinct_in; eauto.
Qed.

Lemma component_decr : forall P G o c P' G'
  (Hsteps : exec_star (Some P) G o c (Some P') G') (Hdistinct : distinct P)
  t li (Hin : In (t, li) P) li' (Hin' : In (t, li') P')
  (Hlt : length li' < length li), size P' < size P.
Proof.
  intros.
  inversion Hsteps; clarify.
  - exploit (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify; omega.
  - destruct P'0; [|inversion Hexec'; clarify].
    exploit size_decr; eauto; intro.
    generalize (size_steps Hexec'); omega.
Qed.

Lemma step_segment : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hfinal : final_state (Some P')) (Hdistinct : distinct P)
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hli1 : li1 <> []),
  exists P'' G'' lo1 lc1 Pt Gt o c lo2 lc2,
    exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    exec P'' G'' t o c (Some Pt) Gt /\ In (t, li2) Pt /\
    exec_star (Some Pt) Gt lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros ???????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  { rewrite Forall_forall in Hfinal; specialize (Hfinal _ Ht); clarify.
    destruct li1; clarify. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl); clarify.
  exploit distinct_step; eauto; clarify.
  destruct (eq_dec t0 t); subst.
  - exploit step_thread; eauto; clarify.
    destruct li1; clarify.
    destruct (nil_dec li1); clarify.
    + repeat eexists; eauto.
      { apply exec_refl. }
      { auto. }
      { auto. }
    + specialize (IHHsteps t li1 li2); clarify.
      repeat eexists; eauto.
      { eapply exec_step; eauto. }
      { rewrite <- app_assoc; auto. }
      { rewrite <- app_assoc; auto. }
  - exploit exec_other_thread; eauto; intro.
    specialize (IHHsteps t0 li1 li2); clarify.
    repeat eexists; eauto.
    { eapply exec_step; eauto. }
    { rewrite <- app_assoc; auto. }
    { rewrite <- app_assoc; auto. }
Qed.

Lemma exec_t_env : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc P' G') t' (Hdiff : t' <> t), G' t' = G t'.
Proof.
  intros; induction Hsteps; clarify.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  destruct o3 as [(?, ?)|]; clarify.
  rewrite IHHsteps; unfold upd_env, upd; clarify.
Qed.

Lemma exec_star_ops : forall t P G lo lc P' G'
  (Hexec : exec_star_t t P G lo lc P' G'),
  Forall (fun c => beq (thread_of c) t = true) lc.
Proof.
  intros; induction Hexec; auto.
  rewrite Forall_app; clarify.
  eapply exec_ops; eauto.
Qed.

Lemma out_env : forall t P' (Hout : ~In t (map fst P')) P G lo lc G'
  (Hdistinct : distinct P),
  exec_star (Some P) G lo lc (Some P') G' -> G' t = G t.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P; induction H; clarify.
  destruct P'0; [|inversion H].
  exploit distinct_step; eauto; intro.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t0 i (G t0) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  exploit IHexec_star; try apply eq_refl; auto; intro IH; rewrite IH.
  apply result_env.
  intro; subst.
  exploit exec_keep; try apply H; auto.
  { apply split_in. }
  clarify; contradiction Hout; rewrite in_map_iff.
  do 2 eexists; eauto; auto.
Qed.  

Lemma exec_det : forall P G t o1 c1 P1 G1 o2 c2 P2 G2 m (Hdistinct : distinct P)
  (Hexec1 : exec P G t o1 c1 P1 G1) (Hexec2 : exec P G t o2 c2 P2 G2)
  (Hcon1 : consistent (m ++ opt_to_list c1))
  (Hcon2 : consistent (m ++ opt_to_list c2))
  (Hinit : match c1 with Some c => initialized m (loc_of c) | _ => True end),
  o1 = o2 /\ c1 = c2 /\ P1 = P2 /\ G1 = G2.
Proof.
  intros.
  inversion Hexec1; subst; inversion Hexec2; subst; exploit distinct_thread;
    eauto; clarify.
  exploit can_read_unique; [eauto | eapply can_read_thread', Hcon1 |
    eapply can_read_thread', Hcon2 | clarify].
Qed.

Lemma exec_star_t_trans : forall t P1 G1 lo1 lc1 P2 G2 lo2 lc2 P3 G3
  (Hsteps1 : exec_star_t t P1 G1 lo1 lc1 P2 G2)
  (Hsteps2 : exec_star_t t P2 G2 lo2 lc2 P3 G3),
  exec_star_t t P1 G1 (lo1 ++ lo2) (lc1 ++ lc2) P3 G3.
Proof.
  intros; induction Hsteps1; clarify.
  repeat rewrite <- app_assoc; eapply exec_step_t; eauto.
Qed.

Lemma exec_step_t' : forall P G t o c P' G' rd mops
  (Hstep : exec P G t o c P' G') lo lc P'' G''
  (Hsteps : exec_star_t t P' G' lo lc P'' G''),
  rd = opt_to_list o ++ lo -> mops = opt_to_list c ++ lc ->
  exec_star_t t (Some P) G rd mops P'' G''.
Proof.
  clarify; eapply exec_step_t; eauto.
Qed.

Lemma exec_t_reorder : forall t P G o c P1 G1 (Hstep : exec P G t o c P1 G1)
  t' (Hdiff : t' <> t) (Ht' : In t' (map fst P))
  (Ht : match P1 with Some P1 => ~In (t, []) P1 | _ => True end)
  (* this can be weakened *)
  (Hspawn : forall u li' li, In (t, Spawn u li' :: li) P -> li' <> [])
  lo lc P2 G2 (Hsteps : exec_star_t t' P1 G1 lo lc P2 G2)
  (Hdistinct : distinct P),
  exists P1' G1', exec_star_t t' (Some P) G lo lc P1' G1' /\
    match P1' with Some P1' => exec P1' G1' t o c P2 G2 | None => P2 = None end.
Proof.
  intros; generalize dependent G; generalize dependent P; induction Hsteps;
    intros.
  - do 3 eexists; [apply exec_refl_t | auto].
  - exploit exec_result; eauto; intros (Pa & i & li & Pb & v & ?).
    destruct (instr_result t i (G0 t) v) as [((((?, ?), ?), u), ?)|] eqn: Hi;
      clarify.
    exploit exec_result; try apply Hexec; intros (? & i' & li' & ? & v' & Heq & 
      ?).
    rewrite result_env in *; auto.
    assert (In (t', i' :: li') (Pa ++ (t, i :: li) :: Pb)).
    { assert (In (t', i' :: li') (Pa ++ (t, li) :: opt_to_list o1 ++ Pb))
        as Hin by (rewrite Heq; apply split_in).
      rewrite in_app in *; clarify.
      rewrite in_app in Hin; destruct Hin as [? | [? | ?]]; clarify.
      destruct o1; clarify.
      destruct i; simpl in Hi; inversion Hi; clarify. }
    exploit in_split; eauto; intros (Pa' & Pb' & Heq0).
    exploit result_exec; eauto.
    destruct (instr_result t' i' (G0 t') v') as [((((?, ?), ?), ?), ?)|]
      eqn: Hi'; setoid_rewrite Hi'; intro Hstep'; clarify.
    + use Hstep'.
      assert (In (t, i :: li) (Pa' ++ (t', li') :: opt_to_list o2 ++ Pb')).
      { assert (In (t, i :: li) (Pa' ++ (t', i' :: li') :: Pb'))
          as Hin by (rewrite <- Heq0; apply split_in).
        rewrite in_app in *; clarify.
        rewrite in_app; destruct Hin; clarify. }
      exploit in_split; eauto; intros (? & ? & Heq1).
      exploit result_exec; eauto.
      assert (t <> t') by auto.
      erewrite <- result_env in Hi; eauto.
      setoid_rewrite Hi; intro Hstep''.
      assert (x1 ++ (t, li) :: opt_to_list o1 ++ x2 =
        x ++ (t', li') :: opt_to_list o2 ++ x0) as Heq'.
      { destruct (le_dec (length Pa) (length Pa')).
        * exploit app_eq_inv_ge; try apply l; eauto; intros ([| ] & ?); clarify.
          rewrite <- app_assoc in *; simpl in *.
          exploit distinct_thread; try apply Heq1.
          { eapply distinct_step; eauto. }
          clarify.
          rewrite split_app, app_assoc, app_assoc in Heq.
          exploit distinct_thread; try apply Heq.
          { repeat rewrite <- app_assoc; eapply distinct_step; eauto. }
          clarify.
          repeat rewrite <- app_assoc; auto.
        * symmetry in Heq0; exploit app_eq_inv_ge; try apply Heq0.
          { omega. }
          intros ([| ] & ?); clarify.
          repeat rewrite <- app_assoc in *; simpl in *.
          exploit distinct_thread; try apply Heq.
          { eapply distinct_step; eauto. }
          clarify.
          rewrite split_app, app_assoc, app_assoc in Heq1.
          exploit distinct_thread; try apply Heq1.
          { repeat rewrite <- app_assoc; eapply distinct_step; eauto. }
          clarify.
          repeat rewrite <- app_assoc; auto. }
      rewrite Heq', result_comm in Hstep''.
      exploit IHHsteps; try apply Hstep''.
      { intro Hnil; contradiction Ht.
        rewrite <- Heq' in Hnil.
        exploit distinct_in; [| apply Hnil | apply split_in|].
        { rewrite Heq'; eapply distinct_step; [|eauto].
          eapply distinct_step; eauto. }
        intro; subst.
        rewrite in_app; simpl; auto. }
      { rewrite map_app, in_app; simpl; auto. }
      { intros ??? Hin; eapply Hspawn.
        rewrite Heq0; rewrite in_app in Hin; rewrite in_app; simpl in Hin.
        rewrite in_app in Hin; destruct Hin as [? | [? | [? | ?]]]; eauto;
          clarify.
        destruct o2; clarify.
        destruct i'; simpl in Hi'; inversion Hi'; clarify.
        contradiction H2222; rewrite map_app, in_app; simpl; auto. }
      { eapply distinct_step; eauto. }
      { destruct i; simpl in Hi; inversion Hi; auto; clarify.
        * intro; contradiction H22222.
          rewrite Heq0; rewrite map_app, in_app in *; clarify.
          rewrite map_app, in_app in *; clarify.
          destruct o2; clarify.
          destruct i'; simpl in Hi'; inversion Hi'; auto; clarify.
          contradiction H2222; rewrite map_app, in_app; simpl; auto.
        * rewrite Heq0 in H22222.
          rewrite in_app in *; clarify.
          rewrite in_app; auto. }
      clarify; do 3 eexists; eauto.
      eapply exec_step_t; eauto.
      { auto. }
      { destruct i'; simpl in Hi'; inversion Hi'; auto; clarify.
        * intro; contradiction H2222.
          rewrite map_app, in_app in *; clarify.
          rewrite map_app, in_app; auto.
        * rewrite in_app in *; clarify.
          rewrite in_app in H2222; destruct H2222; clarify.
          { contradiction Ht; auto. }
          destruct o1; clarify.
          destruct i; simpl in Hi; inversion Hi; auto; clarify.
          exploit Hspawn; [apply split_in | auto | contradiction]. }
    + inversion Hsteps; clarify.
      do 3 eexists.
      * eapply exec_step_t'; eauto.
        apply exec_refl_t.
        { auto. }
        { auto. }
      * simpl; auto.
Qed.    

Lemma exec_minus_reorders : forall t P G lo lc P1 G1 (Hdistinct : distinct P)
  (Hminus : exec_star_minus t (Some P) G lo lc (Some P1) G1)
  lo2 lc2 P2 G2 (Ht : exec_star_t t (Some P1) G1 lo2 lc2 (Some P2) G2)
  (Ht : In t (map fst P)) (Hlive : forall t', In (t', []) P1 -> In (t', []) P),
  exists P1' G1', exec_star_t t (Some P) G lo2 lc2 (Some P1') G1' /\
    exec_star_minus t (Some P1') G1' lo lc (Some P2) G2.
Proof.
  intros; remember (Some P) as Pa; remember (Some P1) as Pb;
    generalize dependent P; induction Hminus; clarify.
  - do 3 eexists; eauto; apply exec_refl_m.
  - destruct P'; [|inversion Hminus].
    exploit distinct_step; eauto; intro Hdistinct'.
    specialize (IHHminus _ Hdistinct' eq_refl); use IHHminus.
    use IHHminus; clarify.
    exploit exec_t_reorder; try apply IHHminus1; eauto.
    { simpl.
      intro; exploit exec_keep; try eapply exec_minus_exec; eauto.
      intros (? & ?); rewrite skipn_nil in *.
      exploit Hlive; eauto; intro.
      exploit step_thread; eauto; clarify. }
    { repeat intro.
      exploit exec_result; eauto; intro Hresult; clarify.
      exploit distinct_in; [eauto | eauto | apply split_in | clarify].
      contradiction Hresult22222.
      exploit exec_keep; try eapply exec_minus_exec; try apply Hminus; auto.
      { rewrite in_app; simpl; right; right; eauto. }
      clarify; rewrite skipn_nil in *.
      exploit Hlive; eauto; intro.
      rewrite in_map_iff; do 2 eexists; eauto; auto. }
    intros ([|] & ?); clarify.
    do 3 eexists; eauto.
    eapply exec_step_m; eauto.
    + exploit Hlive; eauto; intro.
      exploit exec_keep; try eapply exec_step'; try apply Hexec; eauto.
      { apply exec_refl. }
      clarify; rewrite skipn_nil in *; auto.
    + rewrite in_map_iff in *; destruct Ht0 as ((?, ?) & ?); clarify.
      exploit exec_other_thread; eauto; intro.
      do 2 eexists; eauto; auto.
Qed.

Lemma exec_diamond : forall t1 t2 (Hdiff : t1 <> t2) P G
  (Hdistinct : distinct P) 
  o1 c1 P1 G1 (Hstep1 : exec P G t1 o1 c1 (Some P1) G1)
  o2 c2 P2 G2 (Hstep2 : exec P G t2 o2 c2 (Some P2) G2)
  (Hspawns : forall u li1 rest1, In (t1, Spawn u li1 :: rest1) P ->
     forall li2 rest2, ~In (t2, Spawn u li2 :: rest2) P),
  exists P' G', exec P2 G2 t1 o1 c1 (Some P') G' /\
                exec P1 G1 t2 o2 c2 (Some P') G' /\
    exists u, G1 = upd_env' G t1 u /\ G' = upd_env' G2 t1 u.
Proof.
  intros.
  generalize (exec_result Hstep1);
    intros (Pa1 & i1 & li1 & Pb1 & v1 & ? & Hresult1).
  generalize (exec_result Hstep2);
    intros (Pa2 & i2 & li2 & Pb2 & v2 & Heq & Hresult2); subst.
  destruct (instr_result t1 i1 (G t1) v1) as [((((th1, ?), ?), ?), ?)|]
    eqn: Hi1; clarify.
  destruct (instr_result t2 i2 (G t2) v2) as [((((th2, ?), ?), ?), ?)|]
    eqn: Hi2; clarify.
  assert (In (t2, i2 :: li2) (Pa1 ++ (t1, li1) :: opt_to_list th1 ++ Pb1)).
  { exploit split_in; setoid_rewrite <- Heq.
    repeat rewrite in_app; simpl; rewrite in_app; clarify. }
  exploit in_split; eauto; intros (Pa2' & Pb2' & Heq2').
  exploit result_exec; eauto.
  rewrite result_env.
  setoid_rewrite Hi2; intro Hstep2'; use Hstep2'.
  do 3 eexists; [|split; eauto].
  assert (In (t1, i1 :: li1) (Pa2 ++ (t2, li2) :: opt_to_list th2 ++ Pb2)).
  { exploit split_in; setoid_rewrite Heq.
    repeat rewrite in_app; simpl; rewrite in_app; clarify. }
  exploit in_split; eauto; intros (Pa1' & Pb1' & Heq1').
  exploit result_exec; eauto.
  rewrite result_env.
  setoid_rewrite Hi1; intro Hstep1'; use Hstep1'.
  rewrite result_comm in Hstep1'.
  replace (Pa1' ++ (t1, li1) :: opt_to_list th1 ++ Pb1') with
    (Pa2' ++ (t2, li2) :: opt_to_list th2 ++ Pb2') in Hstep1'; eauto.
  + destruct (le_dec (length Pa1) (length Pa2)).
    * exploit app_eq_inv_ge; try apply l; eauto; intros ([|] & ?); clarify.
      rewrite <- app_assoc in *; simpl in *.
      exploit distinct_thread; try apply Heq1'.
      { eapply distinct_step; eauto. }
      clarify.
      rewrite split_app, app_assoc, app_assoc in Heq2'.
      exploit distinct_thread; try apply Heq2'.
      { repeat rewrite <- app_assoc in *; eapply distinct_step; eauto. }
      repeat rewrite <- app_assoc; clarify.
      repeat rewrite <- app_assoc; simpl.
      rewrite <- app_assoc; auto.
    * symmetry in Heq; exploit app_eq_inv_ge; try apply Heq; [omega|];
        intros ([|] & ?); clarify.
      repeat rewrite <- app_assoc in *; simpl in *.
      exploit distinct_thread; try apply Heq2'.
      { eapply distinct_step; eauto. }
      clarify.
      rewrite split_app, app_assoc, app_assoc in Heq1'.
      exploit distinct_thread; try apply Heq1'.
      { repeat rewrite <- app_assoc in *; eapply distinct_step; eauto. }
      repeat rewrite <- app_assoc; clarify.
      repeat rewrite <- app_assoc; simpl.
      rewrite <- app_assoc; auto.
  + auto.
  + destruct i1; simpl in Hi1; inversion Hi1; auto; clarify.
    * intro; contradiction Hresult12222.
      rewrite Heq; rewrite map_app, in_app in *; clarify.
      rewrite map_app, in_app in *; clarify.
      destruct th2; clarify.
      destruct i2; simpl in Hi2; inversion Hi2; clarify.
      exploit Hspawns.
      { apply split_in. }
      { rewrite Heq; apply split_in. }
      contradiction.
    * rewrite Heq, in_app in Hresult12222; rewrite in_app; clarify.
      rewrite in_app; auto.
  + auto.
  + do 2 eexists; eauto.
    rewrite result_comm; auto.
  + destruct i2; simpl in Hi2; inversion Hi2; auto; clarify.
    * intro; contradiction Hresult22222.
      rewrite map_app, in_app in *; clarify.
      rewrite map_app, in_app in *; clarify.
      destruct th1; clarify.
      destruct i1; simpl in Hi1; inversion Hi1; clarify.
      exploit Hspawns.
      { apply split_in. }
      { rewrite Heq; apply split_in. }
      contradiction.
    * rewrite in_app in Hresult22222; rewrite in_app; clarify.
      rewrite in_app; auto.
  + auto.
Qed.  

Definition disjoint_upd (G : env) t g G' := (forall a, match g a with
  Some v' => G t a <> v' /\ G' t a = v' |
  None => G' t a = G t a end) /\ forall t', t' <> t -> G' t' = G t'. 

Lemma disjoint_upd_refl : forall G t, disjoint_upd G t (fun _ => None) G.
Proof.
  split; auto.
Qed.

Definition add_upd t u (G : env) g :=
  match u with
  | Some (a, v) => match g a with
                   | Some v' => if eq_dec v' (G t a) then upd g a None else g
                   | None => if eq_dec v (G t a) then upd g a None
                             else upd g a (Some v)
                   end
  | None => g
  end.

Lemma disjoint_upd_env' : forall G t u g G',
  disjoint_upd (upd_env' G t u) t g G' ->
  disjoint_upd G t (add_upd t u G g) G'.
Proof.
  intros.
  destruct H as (H & Ht').
  split; [|intros t' ?; specialize (Ht' t'); rewrite result_env in Ht'; auto].
  destruct u as [(?, ?)|]; eauto; simpl.
  intro a; specialize (H a); destruct (eq_dec l a).
  - subst; destruct (g a) eqn: Ha; rewrite upd_same in *; clarify.
    + rewrite upd_new; auto.
    + destruct (eq_dec (G' t a) (G t a)); rewrite upd_new; auto.
  - rewrite upd_old in *; auto.
    destruct (g l); clarify.
    + rewrite VectorClocks.upd_old; auto.
    + destruct (eq_dec n (G t l)); rewrite VectorClocks.upd_old; auto.
Qed.  

Lemma add_other : forall G t u g t' u' (Hdiff : t' <> t),
  add_upd t u (upd_env' G t' u') g = add_upd t u G g.
Proof.
  destruct u as [(?, ?)|]; clarify.
  rewrite result_env; auto.
Qed.
  
Definition spawns t := instr_rect'' _ _ (fun _ => 0)
  (fun u _ r => if eq_dec u t then S r else r) 0 (fun _ _ r1 r2 => r1 + r2).

Fixpoint spawns_list t li :=
  match li with
  | [] => 0
  | i :: rest => spawns t i + spawns_list t rest
  end.

Lemma spawns_list_def : forall t li, instr_list_rect _ _ (fun _ => 0)
  (fun u _ r => if eq_dec u t then S r else r) 0 (fun _ _ r1 r2 => r1 + r2) li =
   spawns_list t li.
Proof. induction li; clarify. Qed.

Fixpoint spawn_count t (P : state) :=
  match P with
  | [] => 0
  | (_, li) :: rest => spawns_list t li + spawn_count t rest
  end.

Definition safe_spawns P := forall t, spawn_count t P <= 1 /\
  (forall li, In (t, li) P -> spawn_count t P = 0).

Lemma spawn_count_app : forall t P1 P2, spawn_count t (P1 ++ P2) =
  spawn_count t P1 + spawn_count t P2.
Proof.
  induction P1; clarify.
  destruct a; clarify.
  rewrite IHP1; omega.
Qed.

Lemma safe_spawns_step : forall P (Hspawns : safe_spawns P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), safe_spawns P'.
Proof.
  intros; exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  intro t'; specialize (Hspawns t'); rewrite spawn_count_app in *; clarify.
  destruct o0 as [(u, li)|]; clarify.
  destruct i; clarify.
  generalize (Hspawns2 li).
  unfold spawns in *; simpl in *; rewrite (spawns_list_def t') in *.
  destruct (eq_dec u t'); [split; intros; omega|].
  split; [omega | intros ? Hin].
  destruct (eq_dec t' t).
  - subst; exploit Hspawns2.
    { rewrite in_app; clarify. }
    omega.
  - rewrite <- (Hspawns2 li0); [omega|].
    rewrite in_app in *; simpl in *.
    destruct Hin as [? | [? | [? | ?]]]; clarify.
  - assert (spawns t' i = 0) as Hz by (destruct i; clarify); rewrite Hz in *;
      clarify.
    generalize (Hspawns2 li); rewrite in_app in *; clarify.
    eapply Hspawns2; rewrite in_app; clarify.
Qed.

Lemma spawns_list_app : forall t P1 P2, spawns_list t (P1 ++ P2) =
  spawns_list t P1 + spawns_list t P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; omega.
Qed.

Lemma safe_spawns_steps : forall P (Hspawns : safe_spawns P)
  G o c P' G' (Hsteps : exec_star (Some P) G o c (Some P') G'), safe_spawns P'.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P;
    induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  apply (IHHsteps s); auto.
  eapply safe_spawns_step; eauto.
Qed.

Lemma exec_t_diamond : forall t t' (Hdiff : t' <> t) P (Hdistinct : distinct P) 
  G lot lct Pt Gt (Hstepst : exec_star_t t (Some P) G lot lct (Some Pt) Gt)
  o c P' G' (Hstep : exec P G t' o c (Some P') G') (Hspawns : safe_spawns P),
  exists Pt' Gt', exec_star_t t (Some P') G' lot lct (Some Pt') Gt' /\
    exec Pt Gt t' o c (Some Pt') Gt' /\
    exists g, disjoint_upd G t g Gt /\ disjoint_upd G' t g Gt'.
Proof.
  intros until Gt; intro; remember (Some P) as Pa; remember (Some Pt) as Pb;
    generalize dependent P; induction Hstepst; clarify.
  { do 3 eexists; [apply exec_refl_t|].
    split; auto; eexists; split; apply disjoint_upd_refl. }
  destruct P'; [|inversion Hstepst].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHstepst _ Hdistinct' eq_refl).
  exploit exec_diamond; try apply Hdistinct; eauto.
  { intros ??? Hin1 ?? Hin2.
    specialize (Hspawns u); clarify.
    generalize (in_split _ _ Hin1); clarify.
    rewrite spawn_count_app in Hspawns1; clarify.
    rewrite in_app in Hin2; destruct Hin2; clarify.
    - exploit in_split; eauto; clarify.
      rewrite spawn_count_app in Hspawns1; simpl in Hspawns1.
      unfold spawns in Hspawns1; clarify; omega.
    - exploit in_split; eauto; clarify.
      rewrite spawn_count_app in Hspawns1; simpl in Hspawns1.
      unfold spawns in Hspawns1; clarify; omega. }
  clarify; exploit IHHstepst; eauto.
  { eapply safe_spawns_step; eauto. }
  intros (? & ? & ? & ? & ? & ? & Hdisj).
  do 3 eexists; [eapply exec_step_t; eauto|].
  split; auto.
  assert (exists u, G' = upd_env' G t u) as (u & ?).
  { exploit exec_result; try apply Hexec; intros (? & i & ? & ? & v & ?).
    destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify;
      eauto. }
  subst; eexists; split; [apply disjoint_upd_env'; eauto|].
  erewrite <- add_other.
  apply disjoint_upd_env'; auto.
  rewrite result_comm; auto.
  { auto. }
Qed.

Lemma disjoint_upd_inj : forall G t g g' G'
  (Hg : disjoint_upd G t g G') (Hg' : disjoint_upd G t g' G'), g = g'.
Proof.
  intros; extensionality a.
  destruct Hg as (Hg & _); destruct Hg' as (Hg' & _).
  specialize (Hg a); specialize (Hg' a).
  destruct (g a), (g' a); clarify.
  - contradiction Hg1; auto.
  - contradiction Hg'1; auto.
Qed.

Lemma exec_star_t_upd : forall t P G lo lc P' G',
  exec_star_t t P G lo lc P' G' ->
  exists g, disjoint_upd G t g G'.
Proof.
  induction 1.
  - eexists; apply disjoint_upd_refl.
  - clarify.
    exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
    destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
    + eexists; apply disjoint_upd_env'; eauto.
    + inversion H; subst.
      eexists; apply disjoint_upd_refl.
Qed.

Lemma exec_step_inv_t' : forall P G t lo lc P' G' rd mops
  (Hsteps : exec_star_t t (Some P) G lo lc (Some P') G')
  o c P'' G'' (Hstep : exec P' G' t o c P'' G'')
  (Hrd : rd = lo ++ opt_to_list o)
  (Hmops : mops = lc ++ opt_to_list c),
  exec_star_t t (Some P) G rd mops P'' G''.
Proof.
  clarify; eapply exec_step_inv_t; eauto.
Qed.

Lemma lock_acq : forall P (Hdistinct : distinct P)
  t li1 li2 (Hin : In (t, li1 ++ li2) P) x (Hlock : In (Lock x) li1)
  G lo lc P' G' (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hin' : In (t, li2) P'), In (Acq t x) lc.
Proof.
  intros; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; generalize dependent li1; induction Hsteps; clarify.
  - exploit distinct_in; [eauto | apply Hin | eauto | intro].
    exploit app_nil_inv; eauto; clear H; clarify.
  - destruct P'0; [|inversion Hsteps].
    destruct li1; [clarify|].
    exploit distinct_step; eauto; intro.
    rewrite in_app.
    destruct (eq_dec t0 t); [|exploit exec_other_thread; eauto].
    clarify.
    destruct Hlock; clarify.
    + exploit in_split; eauto; clarify.
      exploit exec_next; eauto; clarify.
    + exploit in_split; eauto; clarify.
      exploit exec_next; eauto; intros (v & ?).
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
      right; eapply IHHsteps; eauto.
      apply split_in.
Qed.
    
Lemma rel_inv : forall t x P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc P' G') li (Hin : In (t, li) P)
  (Hrel : In (Rel t x) lc), exists li1 li2, li = li1 ++ Unlock x :: li2 /\
  match P' with Some s' => exists n, In (t, skipn n li2) s' | None => True end.
Proof.
  intros; rewrite exec_rev in Hsteps; remember (Some P) as P0;
    generalize dependent P; induction Hsteps; clarify.
  rewrite <- exec_rev in Hsteps.
  rewrite in_app in Hrel; destruct Hrel.
  - clarify.
    specialize (IHHsteps P0); clarify.
    repeat eexists; eauto.
    destruct P''; clarify.
    exploit distinct_steps; eauto; intro.
    exploit exec_keep.
    + eauto.
    + eapply exec_step, exec_refl; eauto.
    + eauto.
    + clarify; rewrite skipn_skipn in *; eauto.
  - inversion Hexec'; clarify.
    inversion H; clarify.
    exploit exec_mono; eauto.
    { rewrite in_app; clarify. }
    intros (n & Hn).
    exists (firstn n li), rest.
    rewrite Hn, firstn_skipn; clarify.
    exists 0; rewrite in_app; clarify.
Qed.  

Lemma rel_inv' : forall t x P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') li li'
  (Hin : In (t, li ++ li') P) (Hin' : In (t, li') P') (Hrel : In (Rel t x) lc),
  In (Unlock x) li.
Proof.
  intros.
  exploit rel_inv; eauto; intros (li1 & li2 & Heq & ? & Hin2).
  exploit distinct_steps; eauto; intro.
  exploit distinct_in.
  { eauto. }
  { apply Hin'. }
  { eauto. }
  clarify.
  symmetry in Heq.
  rewrite split_app in Heq; exploit app_eq_inv_ge.
  { eauto. }
  { assert (length ((li1 ++ [Unlock x]) ++ li2) = length (li ++ skipn x0 li2))
      by (rewrite Heq; auto).
    repeat rewrite app_length in *; rewrite skipn_length in *; omega. }
  intros (? & _ & ?); subst.
  repeat rewrite in_app; simpl; auto.
Qed.

Lemma exec_star_rd_ops : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc P' G'),
  Forall (fun o => VectorClocks.thread_of o = t) lo.
Proof.
  induction 1; clarify.
  rewrite Forall_app; clarify.
  eapply exec_rd_ops; eauto.
Qed.

Lemma step_segment' : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hdistinct : distinct P)
  n (Hin' : In (t, skipn n li2) P'),
  exists P'' G'' lo1 lc1 lo2 lc2, exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    In (t, li2) P'' /\ exec_star (Some P'') G'' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros; eapply step_invariant; eauto.
  repeat intro.
  exploit distinct_in; [eauto | apply Ht0 | eauto | intro Heq].
  assert (length (skipn n0 li1 ++ li2) = length (skipn n li2))
    by (rewrite Heq; auto).
  rewrite app_length, skipn_length, skipn_length in *; omega.
Qed.    

Lemma step_instr' : forall t i li1 li2 P (Hin : In (t, li1 ++ i :: li2) P)
  (Hdistinct : distinct P)
  G lo lc P' G' (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  n (Hin' : In (t, skipn n li2) P'),
  exists P1 G1 lo1 lc1 o c P1' G1' lo2 lc2,
    exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t, i :: li2) P1 /\ exec P1 G1 t o c (Some P1') G1' /\
    exec_star (Some P1') G1' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros.
  exploit step_segment'; eauto.
  { instantiate (1 := S n); auto. }
  intros (? & ? & ? & ? & ? & ? & Hsteps0 & ?); clarify.
  exploit step_instr; eauto.
  { eapply distinct_steps; eauto. }
  clarify.
  do 11 eexists; [eapply exec_star_trans; [apply Hsteps0 |
    eapply exec_minus_exec]; eauto|].
  exploit exec_other_threads; eauto; split; auto.
  do 2 rewrite <- app_assoc; eauto.
Qed.

End Exec.