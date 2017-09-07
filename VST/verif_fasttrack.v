Require Import VectorClocks.
Require Import VST.progs.conclib.
Require Import fasttrack.
Require Import VST.floyd.sublist.
Require Import VST.floyd.library.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

Definition max_spec :=
 DECLARE _max
  WITH a : Z, b : Z
  PRE [ _a OF tint, _b OF tint]
   PROP (repable_signed a; repable_signed b)
   LOCAL (temp _a (vint a); temp _b (vint b))
   SEP ()
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (vint (Z.max a b)))
   SEP ().

Definition MAX_THREADS := 10.

Definition tepoch := Tstruct _epoch noattr.
Definition teorvc := Tstruct _eorvc noattr.

Definition VC_of (l : list Z) (t : nat) := Z.to_nat (nth t l 0).

Lemma VC_of_bounded : forall l, bounded (VC_of l) (length l).
Proof.
  repeat intro; unfold VC_of.
  rewrite nth_overflow; auto; omega.
Qed.

Definition epoch_of e := let '(c, t) := e in (Z.to_nat c, Z.to_nat t).

Fixpoint get_Zs l :=
  match l with
  | [] => Some []
  | Vint i :: rest => match get_Zs rest with Some l' => Some (Int.signed i :: l') | _ => None end
  | _ => None
  end.

Definition eorvc_of (v : reptype teorvc) := let '(tag, v) := v in
  match tag with
  | Vint i => if eq_dec (Int.signed i) 0 then
                match v with inl (Vint c, Vint t) => Some (E (epoch_of (Int.signed c, Int.signed t)))
                | _ => None end
              else match v with inr l => match get_Zs l with Some l' => Some (VC (VC_of l')) | _ => None end
                   | _ => None end
  | _ => None
  end.

Definition check_le_spec :=
 DECLARE _check_le
  WITH sh1 : share, sh2 : share, v1 : val, v2 : val, vs1 : list Z, vs2 : list Z
  PRE [ _v1 OF tptr tint, _v2 OF tptr tint ]
   PROP (Forall (fun x => 0 <= x < Int.max_signed) vs1; Forall (fun x => 0 <= x < Int.max_signed) vs2;
         readable_share sh1; readable_share sh2)
   LOCAL (temp _v1 v1; temp _v2 v2)
   SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x => vint x) vs1) v1;
        data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs2) v2)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (vint (if vc_leb (VC_of vs1) (VC_of vs2) (Z.to_nat MAX_THREADS) then 1 else 0)))
   SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x => vint x) vs1) v1;
        data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs2) v2).

Definition check_le_e_spec :=
 DECLARE _check_le_e
  WITH sh1 : share, sh2 : share, e1 : val, time : Z, t : Z, v2 : val, vs : list Z
  PRE [ _e1 OF tptr tepoch, _v2 OF tptr tint ]
   PROP (repable_signed time; repable_signed t; Forall (fun x => 0 <= x < Int.max_signed) vs; 0 <= t < MAX_THREADS;
         readable_share sh1; readable_share sh2)
   LOCAL (temp _e1 e1; temp _v2 v2)
   SEP (data_at sh1 tepoch (vint time, vint t) e1;
        data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs) v2)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (vint (if e_leb (Z.to_nat time, Z.to_nat t) (VC_of vs) then 1 else 0)))
   SEP (data_at sh1 tepoch (vint time, vint t) e1;
        data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs) v2).

Definition MAX_VARS := 10.

(* A read or write step only depends on certain information. *)
Definition step_loc (W : nat * nat) (R : epoch_or_vc) (t : nat) (C : @vector_clock nat) (write : bool)
  (W' : nat * nat) (R' : epoch_or_vc) :=
  if write then W = (C t, t) /\ W' = W /\ R' = R \/
                match R with
                | E e => e_le e C /\ e_le W C /\ R' = R /\ W' = (C t, t)
                | VC V => vc_le V C /\ e_le W C /\ W' = (C t, t) /\ R' = E (O, O)
                end
  else W' = W /\ match R with
                 | E e => e = (C t, t) /\ R' = R \/
                          e_le e C /\ e_le W C /\ R' = E (C t, t) \/
                          let '(c, u) := e in u <> t /\ e_le W C /\ R' = VC (upd (upd vc_bot t (C t)) u c)
                 | VC V => e_le W C /\ R' = VC (upd V t (C t))
                 end.

Lemma upd_same' : forall {A B} {A_eq : EqDec A} (f : A -> B) x y,
  y = f x -> upd f x y = f.
Proof.
  intros; extensionality.
  subst; apply upd_triv.
Qed.

Corollary upd_same : forall {A B} {A_eq : EqDec A} (f : A -> B) x, upd f x (f x) = f.
Proof.
  intros; apply upd_same'; auto.
Qed.

Lemma step_loc_correct : forall W R t C w W' R' (Hstep : step_loc W R t C w W' R')
  s x (HC : FT_clock_of s t = C) (HW : FT_write_of s x = W) (HR : FT_read_of s x = R),
  let '(sC, sL, sR, sW) := s in
    FT_step O s (if w then wr t x else rd t x) (sC, sL, upd sR x R', upd sW x W').
Proof.
  unfold step_loc; intros.
  destruct s as (((sC, sL), sR), sW).
  destruct w.
  - destruct Hstep as [(? & ? & ?) | Hstep].
    + simpl in *; subst.
      rewrite !upd_same'; auto; apply FT_write_same_epoch; auto.
    + destruct R.
      * destruct Hstep as (? & ? & ? & ?); simpl in *; subst.
        eapply FT_write_shared; eauto.
      * destruct Hstep as (? & ? & ? & ?); simpl in *; subst.
        rewrite upd_same'; auto; eapply FT_write_exclusive; eauto.
  - destruct Hstep as (? & Hstep); simpl in *; subst.
    rewrite upd_same.
    destruct (sR x) eqn: HR.
    + destruct Hstep; subst.
      eapply FT_read_shared; eauto.
    + destruct Hstep as [(? & ?) | Hstep].
      * subst; rewrite upd_same'; auto; apply FT_read_same_epoch; auto.
      * destruct e; destruct Hstep as [(? & ? & ?) | (? & ? & ?)]; subst;
          [eapply FT_read_exclusive | eapply FT_read_share]; eauto.
Qed.

(* Actually, a history is exactly the right thing here! In this case, the checkers don't
   need to have any share; the lock will maintain the correctness invariant. *)
(* But in that case, there's no need for the ghost state machinery; this is just a
   normal invariant. *)

Inductive consistent : list (nat * @vector_clock nat) -> nat * nat * epoch_or_vc -> Prop :=
| consistent_nil : consistent [] (O, O, (E (O, O)))
| consistent_step : forall h wc wt R t C wc' wt' R' (Hcon : consistent h (wc, wt, R))
    b (Hstep : step_loc (wc, wt) R t C b (wc', wt') R'),
    consistent ((t, C) :: h) (wc', wt', R').

Definition x_inv sh Rs Ws x R W (*gsh*) := EX tag : Z, EX v : val * val + list val, EX c : Z, EX t : Z,
  !!(readable_share sh /\ repable_signed tag /\ repable_signed c /\ 0 <= t < MAX_THREADS /\
     (if eq_dec tag 0
      then exists c u, v = inl (vint c, vint u) /\ 0 <= c < Int.max_signed /\ 0 <= u < MAX_THREADS
      else exists vs, v = inr (map (fun x => vint x) vs) /\ Forall (fun x => 0 <= x < Int.max_signed) vs) /\
     exists h R, eorvc_of (vint tag, v) = Some R /\ consistent h (Z.to_nat c, Z.to_nat t, R)) &&
  (data_at sh (tarray (tptr teorvc) MAX_VARS) Rs R * data_at Tsh teorvc (vint tag, v) (Znth x Rs Vundef) *
   data_at sh (tarray (tptr tepoch) MAX_VARS) Ws W * data_at Tsh tepoch (vint c, vint t) (Znth x Ws Vundef)).

Lemma x_inv_precise : forall sh Rs Ws x R W, precise (x_inv sh Rs Ws x R W).
Proof.
  intros ????????? (tag1 & v1 & c1 & t1 & (? & ? & ? & ? & ? & Hr1 & Hr'1) & ? & ? & ? & (? & ? & ? & (? & ? & ? & HRs1 & HR1) & HWs1) & HW1)
    (tag2 & v2 & c2 & t2 & (? & ? & ? & ? & ? & Hr2 & Hr'2) & ? & ? & ? & HR2 & HW2) ??.
Admitted.

Lemma x_inv_positive : forall sh Rs Ws x R W, positive_mpred (x_inv sh Rs Ws x R W).
Proof.
  intros; repeat (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon2, positive_andp2.
  unfold at_offset; rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  apply positive_sepcon1; rewrite data_at_rec_eq; simpl; auto.
Qed.
Hint Resolve x_inv_precise x_inv_positive.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0,
             P at level 100, Q at level 100).

Definition instr_read_spec :=
 DECLARE _instr_read
  WITH C : val, R : val, W : val, X : val, xsh : share, lsh : share, t : Z, x : Z, locks : list val,
    V : list Z, e : Z * Z, v : reptype teorvc, sh : share, Rs : list val, Ws : list val
  PRE [ _t OF tint, _x OF tint ]
   PROP (readable_share xsh; readable_share lsh;
         0 <= x < MAX_VARS; 0 <= t < MAX_THREADS; Forall (fun x => 0 <= x < Int.max_signed) V)
   LOCAL (temp _t (vint t); temp _x (vint x);
          gvar _C C; gvar _R R; gvar _W W; gvar _X X)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V) C;
        data_at xsh (tarray (tptr tlock) MAX_VARS) locks X;
        lock_inv lsh (Znth x locks Vundef) (x_inv sh Rs Ws x R W))
  POST [ tvoid ]
   EX e' : nat * nat, EX v' : epoch_or_vc,
   PROP (exists W' R', step_loc e' v' (Z.to_nat t) (VC_of V) false W' R')
   LOCAL ()
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V) C;
        data_at xsh (tarray (tptr tlock) MAX_VARS) locks X;
        lock_inv lsh (Znth x locks Vundef) (x_inv sh Rs Ws x R W)).
(* Maybe we want a ghost history after all, to relate the X data observed to the lock invariant. *)

Definition instr_write_spec :=
 DECLARE _instr_write
  WITH C : val, R : val, W : val, X : val, xsh : share, lsh : share, t : Z, x : Z, locks : list val, V : list Z,
    sh : share, Rs : list val, Ws : list val
  PRE [ _t OF tint, _x OF tint ]
   PROP (readable_share xsh; readable_share lsh;
         0 <= x < MAX_VARS; 0 <= t < MAX_THREADS; Forall (fun x => 0 <= x < Int.max_signed) V)
   LOCAL (temp _t (vint t); temp _x (vint x);
          gvar _C C; gvar _R R; gvar _W W; gvar _X X)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V) C;
        data_at xsh (tarray (tptr tlock) MAX_VARS) locks X;
        lock_inv lsh (Znth x locks Vundef) (x_inv sh Rs Ws x R W))
  POST [ tvoid ]
   EX e' : nat * nat, EX v' : epoch_or_vc,
   PROP (exists W' R', step_loc e' v' (Z.to_nat t) (VC_of V) true W' R')
   LOCAL ()
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V) C;
        data_at xsh (tarray (tptr tlock) MAX_VARS) locks X;
        lock_inv lsh (Znth x locks Vundef) (x_inv sh Rs Ws x R W)).

Definition vc_join_spec :=
 DECLARE _vc_join
  WITH sh1 : share, sh2 : share, v1 : val, v2 : val, vs1 : list Z, vs2 : list Z
  PRE [ _tgt OF tptr tint, _src OF tptr tint ]
   PROP (Forall repable_signed vs1; Forall repable_signed vs2; writable_share sh1; readable_share sh2)
   LOCAL (temp _tgt v1; temp _src v2)
   SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x => vint x) vs1) v1;
        data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs2) v2)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine vs1 vs2)) v1;
        data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs2) v2).

Definition MAX_LOCKS := 10.

Definition instr_acquire_spec :=
 DECLARE _instr_acquire
  WITH C : val, L : val, lsh : share, t : Z, m : Z, V1 : list Z, V2 : list Z
  PRE [ _t OF tint, _m OF tint ]
   PROP (Forall repable_signed V1; Forall repable_signed V2; readable_share lsh)
   LOCAL (temp _t (vint t); temp _m (vint m); gvar _C C; gvar _L L)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V1) C;
        field_at lsh (tarray (tarray tint MAX_THREADS) MAX_LOCKS) [ArraySubsc m] (map (fun x => vint x) V2) L)
 POST [ tvoid ]
   PROP (forall s, exists s', FT_clock_of s (Z.to_nat t) = VC_of V1 -> FT_lock_of s (Z.to_nat m) = VC_of V2 ->
     FT_step O s (acq (Z.to_nat t) (Z.to_nat m)) s')
   LOCAL ()
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t]
          (map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine V1 V2)) C;
        field_at lsh (tarray (tarray tint MAX_THREADS) MAX_LOCKS) [ArraySubsc m] (map (fun x => vint x) V2) L).

Definition instr_release_spec :=
 DECLARE _instr_release
  WITH C : val, L : val, t : Z, m : Z, V1 : list Z, V2 : list Z
  PRE [ _t OF tint, _m OF tint ]
   PROP (Forall repable_signed V1; Forall repable_signed V2)
   LOCAL (temp _t (vint t); temp _m (vint m); gvar _C C; gvar _L L)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V1) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_LOCKS) [ArraySubsc m] (map (fun x => vint x) V2) L)
 POST [ tvoid ]
   PROP (forall s, exists s', FT_clock_of s (Z.to_nat t) = VC_of V1 -> FT_lock_of s (Z.to_nat m) = VC_of V2 ->
     FT_step O s (rel (Z.to_nat t) (Z.to_nat m)) s')
   LOCAL ()
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t]
          (map (fun x => vint x) (upd_Znth t V1 (Znth t V1 0 + 1))) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_LOCKS) [ArraySubsc m] (map (fun x => vint x) V1) L).

Definition instr_fork_spec :=
 DECLARE _instr_fork
  WITH C : val, t : Z, u : Z, V1 : list Z, V2 : list Z
  PRE [ _t OF tint, _u OF tint ]
   PROP (Forall repable_signed V1; Forall repable_signed V2)
   LOCAL (temp _t (vint t); temp _u (vint u); gvar _C C)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V1) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc u] (map (fun x => vint x) V2) C)
 POST [ tvoid ]
   PROP (forall s, exists s', FT_clock_of s (Z.to_nat t) = VC_of V1 -> FT_clock_of s (Z.to_nat u) = VC_of V2 ->
     FT_step O s (fork (Z.to_nat t) (Z.to_nat u)) s')
   LOCAL ()
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t]
          (map (fun x => vint x) (upd_Znth t V1 (Znth t V1 0 + 1))) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc u]
          (map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine V1 V2)) C).

Definition instr_join_spec :=
 DECLARE _instr_join
  WITH C : val, t : Z, u : Z, V1 : list Z, V2 : list Z
  PRE [ _t OF tint, _u OF tint ]
   PROP (Forall repable_signed V1; Forall repable_signed V2)
   LOCAL (temp _t (vint t); temp _u (vint u); gvar _C C)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t] (map (fun x => vint x) V1) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc u] (map (fun x => vint x) V2) C)
 POST [ tvoid ]
   PROP (forall s, exists s', FT_clock_of s (Z.to_nat t) = VC_of V1 -> FT_clock_of s (Z.to_nat u) = VC_of V2 ->
     FT_step O s (join (Z.to_nat t) (Z.to_nat u)) s')
   LOCAL ()
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc t]
          (map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine V1 V2)) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS) [ArraySubsc u]
          (map (fun x => vint x) (upd_Znth u V2 (Znth u V2 0 + 1))) C).

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec;
  max_spec; check_le_spec; check_le_e_spec; instr_read_spec; instr_write_spec; vc_join_spec;
  instr_acquire_spec; instr_release_spec; instr_fork_spec; instr_join_spec]).

Lemma body_max : semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (vint (Z.max a b))) SEP ()); forward.
  - rewrite Z.max_l; [entailer! | omega].
  - rewrite Z.max_r; [entailer! | omega].
Qed.

Lemma repable_max : forall i, 0 <= i <= MAX_THREADS -> repable_signed i.
Proof.
  split; [transitivity 0 | transitivity MAX_THREADS]; unfold MAX_THREADS in *; try computable; omega.
Qed.

Opaque vc_leb.

Corollary VC_of_bounded' : forall l i, Zlength l = Z.of_nat i -> bounded (VC_of l) i.
Proof.
  intros.
  rewrite Zlength_correct in H; apply Nat2Z.inj in H; subst; apply VC_of_bounded.
Qed.

Lemma VC_of_spec : forall v i, VC_of v i = Z.to_nat (Znth (Z.of_nat i) v 0).
Proof.
  intros; unfold VC_of, Znth.
  if_tac; [omega|].
  rewrite Nat2Z.id; auto.
Qed.

Lemma Forall2_nth_error : forall {A} (P : A -> A -> Prop) l1 l2 n, Forall2 P l1 l2 ->
  match nth_error l1 n with Some a1 => exists a2, nth_error l2 n = Some a2 /\ P a1 a2
  | None => nth_error l2 n = None end.
Proof.
  intros; revert n; induction H; intro.
  - rewrite nth_error_nil; auto.
  - destruct n; simpl; eauto.
    apply IHForall2.
Qed.

Lemma VC_of_le : forall v1 v2, Forall2 Z.le v1 v2 -> vc_le (VC_of v1) (VC_of v2).
Proof.
  intros; unfold VC_of; intro.
  rewrite !nth_Znth.
  destruct (zlt (Z.of_nat t) 0); [omega|].
  pose proof (mem_lemmas.Forall2_Zlength H).
  destruct (zle (Zlength v1) (Z.of_nat t)); [rewrite !Znth_overflow; try omega|].
  apply Forall2_Znth with (i := Z.of_nat t)(d1 := 0)(d2 := 0) in H; [|omega].
  destruct (zlt (Znth (Z.of_nat t) v1 0) 0).
  { rewrite Z2Nat_neg by auto; omega. }
  apply Z2Nat.inj_le; omega.
Qed.

Lemma body_check_le : semax_body Vprog Gprog f_check_le check_le_spec.
Proof.
  start_function.
  unfold Sfor.
  forward.
  assert_PROP (Zlength vs1 = MAX_THREADS /\ Zlength vs2 = MAX_THREADS).
  { go_lowerx; apply derives_trans with (Q := !!(Zlength (map (fun x => vint x) vs1) = MAX_THREADS /\
      Zlength (map (fun x => vint x) vs2) = MAX_THREADS)); [entailer!|].
    apply prop_left; intros (? & ?); apply prop_right.
    rewrite Zlength_map in *; auto. }
  eapply semax_seq with (Q := PROP (Forall2 Z.le vs1 vs2) LOCAL (temp _v1 v1; temp _v2 v2)
    SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x => vint x) vs1) v1;
         data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs2) v2)); [|fwd_result; abbreviate_semax].
  eapply semax_pre with (P' := EX i : Z, PROP (0 <= i <= MAX_THREADS;
                                               Forall2 Z.le (sublist 0 i vs1) (sublist 0 i vs2))
    LOCAL (temp _i (vint i); temp _v1 v1; temp _v2 v2)
    SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs1) v1;
         data_at sh2 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs2) v2)).
  { Exists 0; rewrite !sublist_nil; entailer!.
    pose proof (Zlength_nonneg vs1); omega. }
  eapply semax_loop with (Q' := EX i : Z, PROP (0 <= i < MAX_THREADS;
                                      Forall2 Z.le (sublist 0 (i + 1) vs1) (sublist 0 (i + 1) vs2))
    LOCAL (temp _i (vint i); temp _v1 v1; temp _v2 v2)
    SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs1) v1;
         data_at sh2 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs2) v2)).
  Intros i.
  exploit repable_max; eauto; intro.
  forward_if (PROP (i < 10) LOCAL (temp _i (vint i); temp _v1 v1; temp _v2 v2)
    SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs1) v1;
         data_at sh2 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs2) v2)).
  { forward.
    entailer!. }
  { forward.
    match goal with H : Forall2 _ _ _ |- _ => rewrite !sublist_same in H; auto;
      try (unfold MAX_THREADS in *; omega) end.
    entailer!. }
  Intros.
  assert (0 <= i < MAX_THREADS) by (unfold MAX_THREADS in *; omega).
  forward.
  forward.
  forward_if (PROP (Znth i vs1 0 <= Znth i vs2 0) LOCAL (temp _i (vint i); temp _v1 v1; temp _v2 v2)
    SEP (data_at sh1 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs1) v1;
         data_at sh2 (tarray tint MAX_THREADS) (map (fun x : Z => vint x) vs2) v2)).
  - forward.
    apply prop_right.
    destruct (vc_leb (VC_of vs1) (VC_of vs2) 10) eqn: Hleb; auto.
    rewrite vc_leb_spec in Hleb; [|apply VC_of_bounded'; tauto].
    match goal with H : Forall _ vs1 |- _ => rewrite Forall_forall in H; exploit (Znth_In i vs1 0);
      [omega | intro Hin]; specialize (H _ Hin); clear Hin end.
    match goal with H : Forall _ vs2 |- _ => rewrite Forall_forall in H; exploit (Znth_In i vs2 0);
      [omega | intro Hin]; specialize (H _ Hin); clear Hin end.
    rewrite !Int.signed_repr in *; try (split; [transitivity 0|]; try computable; omega).
    specialize (Hleb (Z.to_nat i)); rewrite !VC_of_spec, Z2Nat.id, <- Z2Nat.inj_le in Hleb; omega.
  - forward.
    entailer!.
    match goal with H : Forall _ vs1 |- _ => rewrite Forall_forall in H; exploit (Znth_In i vs1 0);
      [omega | intro Hin]; specialize (H _ Hin); clear Hin end.
    match goal with H : Forall _ vs2 |- _ => rewrite Forall_forall in H; exploit (Znth_In i vs2 0);
      [omega | intro Hin]; specialize (H _ Hin); clear Hin end.
    rewrite !Int.signed_repr in *; try omega;
      try (split; [transitivity 0|]; try computable; omega).
  - intros.
    unfold exit_tycon, overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
    Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert; entailer!.
    Exists i; entailer!.
    rewrite !sublist_split with (lo := 0)(mid := i)(hi := i + 1), !sublist_len_1 with (d := 0); try omega.
    apply Forall2_app; auto.
  - Intros i; forward.
    unfold loop2_ret_assert; entailer!.
    Exists (i + 1); entailer!.
  - forward.
    apply prop_right.
    destruct (vc_leb (VC_of vs1) (VC_of vs2) 10) eqn: Hleb; auto.
    match goal with H : Forall2 _ _ _ |- _ => apply VC_of_le in H end.
    rewrite <- vc_leb_spec, Hleb in *; [discriminate | apply VC_of_bounded'; tauto].
Qed.

Lemma data_at_epoch : forall sh a b p, data_at sh (tarray tint 2) [a; b] p =
  data_at sh tepoch (a, b) p.
Proof.
  intros.
  apply mpred_ext.
  - unfold data_at, field_at, at_offset; Intros; apply andp_right.
    { apply prop_right; auto. }
    rewrite !data_at_rec_eq; unfold withspacer; simpl.
    unfold array_pred, aggregate_pred.array_pred; simpl.
    apply derives_extract_prop; intro.
    unfold unfold_reptype in *; simpl in *; cancel.
  - unfold data_at, field_at, at_offset; Intros; apply andp_right.
    { apply prop_right; auto. }
    rewrite !data_at_rec_eq; unfold withspacer; simpl.
    unfold array_pred, aggregate_pred.array_pred; simpl.
    unfold unfold_reptype; simpl.
    rewrite !Zlength_cons, Zlength_nil; entailer!.
Qed.

Lemma body_check_le_e : semax_body Vprog Gprog f_check_le_e check_le_e_spec.
Proof.
  start_function.
  forward.
  forward.
  rewrite data_at_isptr; Intros.
  assert_PROP (Zlength vs = MAX_THREADS).
  { entailer!.
    rewrite Zlength_map in *; auto. }
  forward.
  forward.
  entailer!.
  unfold both_int; simpl.
  rewrite Zlength_map in *.
  match goal with H : Forall _ vs |- _ => rewrite Forall_forall in H; exploit (Znth_In t vs 0); [omega|];
    intro Hin; specialize (H _ Hin) end.
  assert (repable_signed (Znth t vs 0)) by (split; [transitivity 0|]; auto; try computable; omega).
  rewrite VC_of_spec, Z2Nat.id; try omega.
  destruct (zlt time 0).
  { rewrite Z2Nat_neg; auto.
    destruct (Z.to_nat time <=? Z.to_nat (Znth t vs 0%Z))%nat eqn: Hle; simpl.
    destruct (Int.lt (Int.repr (Znth t vs 0)) (Int.repr time)) eqn: Hlt; simpl; auto.
    apply lt_repr in Hlt; auto; omega.
    { apply leb_complete_conv in Hle; rewrite (Z2Nat_neg time) in Hle; auto; omega. } }
  destruct (Int.lt (Int.repr (Znth t vs 0)) (Int.repr time)) eqn: Hlt;
    [apply lt_repr in Hlt | apply lt_repr_false in Hlt]; auto; simpl;
    destruct (Z.to_nat time <=? Z.to_nat (Znth t vs 0%Z))%nat eqn: Hle;
    try (apply leb_complete in Hle; rewrite <- Z2Nat.inj_le in Hle; auto; omega);
    try (apply leb_complete_conv in Hle; rewrite <- Z2Nat.inj_lt in Hle; auto; omega).
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Opaque upto.

(* to forward? *)
Lemma gvar_eval_var:
 forall i t v rho, locald_denote (gvar i v) rho -> eval_var i t rho = v.
Proof.
intros.
unfold eval_var. hnf in H. 
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); auto; contradiction.
Qed.

(* up *)
Lemma field_at_data_at' : forall sh t gfs v p, field_at sh t gfs v p =
  !!field_compatible t gfs p &&
  data_at sh (nested_field_type t gfs) v (offset_val (nested_field_offset t gfs) p).
Proof.
  intros.
  rewrite field_at_data_at.
  unfold field_address.
  if_tac.
  - rewrite prop_true_andp; auto.
  - rewrite prop_false_andp by auto.
    rewrite data_at_isptr, prop_false_andp; auto.
Qed.

(* up *)
Lemma sublist_last_1 : forall {A} lo hi (al : list A) d, 0 <= lo <= hi -> hi + 1 <= Zlength al ->
  sublist lo (hi + 1) al = sublist lo hi al ++ [Znth hi al d].
Proof.
  intros.
  erewrite sublist_split with (mid := hi)(hi0 := hi + 1), sublist_len_1 with (d0 := d); auto; omega.
Qed.

Lemma get_Zs_spec : forall l, Forall repable_signed l -> get_Zs (map (fun x => vint x) l) = Some l.
Proof.
  induction 1; auto; simpl.
  rewrite IHForall, Int.signed_repr; auto.
Qed.

Lemma VC_of_upd : forall V t c, 0 <= t < Zlength V ->
  VC_of (upd_Znth t V c) = upd (VC_of V) (Z.to_nat t) (Z.to_nat c).
Proof.
  intros; unfold VC_of.
  extensionality u; unfold upd.
  rewrite !nth_Znth.
  if_tac.
  - subst; rewrite Z2Nat.id, upd_Znth_same by omega; auto.
  - rewrite upd_Znth_diff'; auto.
    intro; subst.
    rewrite Nat2Z.id in *; contradiction.
Qed.

Lemma VC_of_bot : forall n, VC_of (repeat 0 n) = vc_bot.
Proof.
  unfold VC_of; intro; extensionality u.
  rewrite nth_Znth, Znth_repeat; auto.
Qed.

Opaque repeat.

Lemma body_instr_read : semax_body Vprog Gprog f_instr_read instr_read_spec.
Proof.
  start_function.
  rewrite <- lock_struct_array.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
  unfold x_inv at 2.
  Intros tag Rx cx tx.
  forward.
  forward.
  forward.
  assert_PROP (Zlength V = MAX_THREADS) as HV.
  { entailer!.
    match goal with H : value_fits _ (map _ V) |- _ => rewrite value_fits_eq in H; simpl in H;
      destruct H as (Hlen & _) end.
    unfold unfold_reptype in Hlen; simpl in Hlen.
    rewrite Zlength_map in Hlen; rewrite Hlen; auto. }
  forward.
  forward_if (fun _ : environ => FF); [| |apply semax_ff];
    destruct (eq_dec tag 0); try solve [absurd (tag = 0); auto].
  - match goal with H : exists c u, _ |- _ => destruct H as (c & u & ? & ? & ? & ?); subst end.
    assert_PROP (field_compatible teorvc [] (Znth x Rs Vundef)) as HR by entailer!.
    destruct (Znth x Rs Vundef) eqn: HRx; try (destruct HR; contradiction).
    forward.
    simpl.
    unfold_data_at 2%nat.
    rewrite field_at_data_at' with (gfs := [StructField _data]); Intros; simpl.
    unfold data_at at 2; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
    unfold withspacer; simpl.
    rewrite field_at_data_at' with (gfs := [UnionField _e]); Intros; simpl.
    rewrite Int.add_zero.
    forward.
    forward.
    assert (repable_signed t) by (apply repable_max; omega).
    assert (repable_signed tx) by (apply repable_max; omega).
    assert (repable_signed u) by (apply repable_max; omega).
    assert (repable_signed (Znth t V 0)).
    { apply Forall_Znth; [omega|].
      pose proof Int.min_signed_neg.
      eapply Forall_impl; [|eauto]; split; omega. }
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP ()
        (LOCALx (temp _t'1 (vint (if eq_dec c (Znth t V 0) then if eq_dec u t then 1 else 0 else 0)) :: Q)
        (SEPx R))) end.
    { forward.
      entailer!.
      rewrite eq_dec_refl.
      unfold eval_binop; simpl.
      pose proof (Int.eq_spec (Int.repr u) (Int.repr t)).
      destruct (Int.eq (Int.repr u) (Int.repr t)); simpl; destruct (eq_dec u t); auto.
      + match goal with H : Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in H; auto end.
        contradiction n; auto.
      + subst; absurd (Int.repr t = Int.repr t); auto. }
    { forward.
      entailer!.
      destruct (eq_dec c (Znth t V 0)); [absurd (c = Znth t V 0); auto | auto]. }
    match goal with |-semax _ ?P _ _ => forward_if P end.
    { forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
      { lock_props.
        unfold x_inv.
        Exists 0 ((inl (vint c, vint u)) : val * val + list val) cx tx; entailer!.
        { rewrite eq_dec_refl; eauto 6. }
        unfold_data_at 3%nat; rewrite HRx; cancel.
        rewrite field_at_data_at' with (gfs := [StructField _data]); simpl.
        unfold data_at at 3; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
        unfold withspacer; simpl.
        rewrite field_at_data_at' with (gfs := [UnionField _e]); simpl; entailer!; cancel. }
      forward.
      Exists (Z.to_nat cx, Z.to_nat tx) (E (Z.to_nat c, Z.to_nat u)).
      apply andp_right; [|rewrite lock_struct_array; cancel].
      apply prop_right.
      repeat eexists; eauto.
      destruct (eq_dec c (Znth t V 0)); [|absurd (Int.repr 0 = Int.zero); auto].
      destruct (eq_dec u t); [subst | absurd (Int.repr 0 = Int.zero); auto].
      rewrite VC_of_spec, Z2Nat.id; auto; omega. }
    { forward.
      entailer!. }
    forward_call (Tsh, Ews, Znth x Ws Vundef, cx, tx,
      force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), V).
    { rewrite gvar_eval_var with (v := C); auto.
      repeat split; auto; destruct C; auto; contradiction. }
    { rewrite field_at_data_at' with (p := C); entailer!. }
    { repeat (split; auto). }
    match goal with |-semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROP (e_le (Z.to_nat cx, Z.to_nat tx) (VC_of V)) (LOCALx Q (SEPx R))) end.
    { forward_call tt.
      contradiction. }
    { forward.
      entailer!.
      destruct (Z.to_nat cx <=? VC_of V (Z.to_nat tx))%nat eqn: Hle; [|absurd (0 = 0); auto].
      rewrite <- Nat.leb_le; auto. }
    assert (repable_signed c) by (pose proof Int.min_signed_neg; split; omega).
    forward_call (Tsh, Ews, Vptr b (Int.add i (Int.repr 4)), c, u,
      force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), V).
    { rewrite gvar_eval_var with (v := C); auto. }
    { repeat (split; auto). }
    Intros v'; subst.
    match goal with |-semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROP (u <> t) (LOCALx Q (SEPx R))) end.
    { destruct ((Z.to_nat c <=? VC_of V (Z.to_nat u))%nat) eqn: Hle; [|absurd (0 = 0); auto].
      rewrite Nat.leb_le in Hle.
      forward.
      forward.
      forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
      { lock_props.
        unfold x_inv.
        Exists 0 ((inl (vint (Znth t V 0), vint t)) : val * val + list val) cx tx; entailer!.
        { rewrite eq_dec_refl; split; [do 3 eexists; eauto; split; auto|].
          { apply Forall_Znth; auto; omega. }
          match goal with H : exists h R, _ |- _ => destruct H as (h & R1 & HR1 & ?) end.
          exists ((Z.to_nat t, VC_of V) :: h); do 2 eexists; simpl; eauto.
          econstructor; eauto.
          instantiate (1 := false); split; auto; simpl in *.
          inv HR1.
          right; left.
          repeat split; auto; rewrite ?VC_of_spec, !Int.signed_repr, ?Z2Nat.id; auto; omega. }
        unfold_data_at 3%nat; rewrite HRx; cancel.
        rewrite field_at_data_at' with (p := Vptr b i); simpl.
        unfold data_at at 3; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
        unfold withspacer; simpl.
        rewrite field_at_data_at' with (gfs := [UnionField _e]); simpl; entailer!; cancel. }
      forward.
      Exists (Z.to_nat cx, Z.to_nat tx) (E (Z.to_nat c, Z.to_nat u)).
      rewrite field_at_data_at'; rewrite lock_struct_array; entailer!.
      eauto 8. }
    { forward.
      entailer!.
      admit. (* If u = t, then the core VC invariant guarantees that c <= C[t][t]. *) }
    forward.
    assert (Int.unsigned (Int.add i (Int.repr 4)) = Int.unsigned i + 4) as Hadd.
    { destruct HR; unfold Int.add.
      rewrite (Int.unsigned_repr 4) by computable; rewrite Int.unsigned_repr; auto.
      split; [pose proof (Int.unsigned_range i) | simpl in *; unfold Int.max_unsigned]; omega. }
    assert (field_compatible (tarray tint MAX_THREADS) [] (Vptr b (Int.add i (Int.repr 4)))) as HRV.
    { destruct HR.
      repeat split; auto; simpl in *.
      + rewrite Hadd; omega.
      + rewrite Hadd; apply Z.divide_add_r; [tauto | reflexivity]. }
    gather_SEP 0 6.
    assert (Zlength (upd_Znth t (repeat 0 (Z.to_nat MAX_THREADS)) (Znth t V 0)) = MAX_THREADS).
    { rewrite upd_Znth_Zlength; rewrite Zlength_repeat, Z2Nat.id; omega. }
    assert (Zlength (map (fun x => vint x) (upd_Znth u (upd_Znth t
      (repeat 0 (Z.to_nat MAX_THREADS)) (Znth t V 0)) c)) = MAX_THREADS).
    { rewrite Zlength_map, upd_Znth_Zlength; omega. }
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?P)))) _ _ =>
      forward_for_simple_bound MAX_THREADS (EX i1 : Z, PROP () (LOCALx Q
        (SEPx (data_at Tsh (tarray tint MAX_THREADS)
          (sublist 0 i1 (map (fun x => vint x) (upd_Znth u (upd_Znth t (repeat 0 (Z.to_nat MAX_THREADS)) (Znth t V 0)) c))
           ++ repeat Vundef (Z.to_nat (MAX_THREADS - i1))) (Vptr b (Int.add i (Int.repr 4))) :: P)))) end.
    { unfold MAX_THREADS; computable. }
    { rewrite sublist_nil; entailer!.
      unfold spacer, at_offset.
      if_tac; [omega|].
      change (40 - 8) with (sizeof (tarray tint 8)).
      rewrite memory_block_data_at_.
      eapply derives_trans, split2_data_at_Tarray_fold
        with (n1 := 2)(v' := repeat Vundef (Z.to_nat MAX_THREADS)); eauto.
      rewrite field_address0_offset, <- data_at_epoch.
      entailer!.
      { apply field_compatible_field_compatible0; rewrite field_compatible_cons; simpl; split; auto.
        unfold MAX_THREADS; computable. }
      { destruct HRV; simpl.
        assert (Int.unsigned (Int.add (Int.add i (Int.repr 4)) (Int.repr 8)) = Int.unsigned i + 4 + 8)
          as Hadd'.
        { rewrite Int.add_unsigned, Hadd.
          unfold Int.add; rewrite Int.unsigned_repr; rewrite Int.unsigned_repr; try computable; try omega.
          pose proof (Int.unsigned_range_2 i).
          simpl in *; unfold Int.max_unsigned; omega. }
        repeat split; auto; simpl in *; rewrite Hadd'; try omega.
        rewrite Hadd in *; apply Z.divide_add_r; [tauto | exists 2; auto]. } }
    { assert_PROP (Vptr b (Int.add (Int.add i (Int.repr 4)) (Int.mul (Int.repr 4) (Int.repr i0))) =
        field_address (tarray tint MAX_THREADS) [ArraySubsc i0] (Vptr b (Int.add i (Int.repr 4)))).
      { rewrite field_address_offset; [entailer!|].
        rewrite field_compatible_cons; simpl; auto. }
      match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
        set (q := PROP () (LOCALx Q (SEPx (data_at Tsh (tarray tint MAX_THREADS)
          (sublist 0 (i0 + 1) (map (fun x => vint x) (upd_Znth u (upd_Znth t
            (repeat 0 (Z.to_nat MAX_THREADS)) (Znth t V 0)) c)) ++
           repeat Vundef (Z.to_nat (MAX_THREADS - (i0 + 1)))) (Vptr b (Int.add i (Int.repr 4))) :: R)))) end.
      forward_if q; [|forward_if q|]; subst q.
      + assert (i0 = t).
        { apply repr_inj_signed; auto; apply repable_max; omega. }
        forward.
        entailer!.
        unfold MAX_THREADS in *; simpl in *.
        rewrite upd_init by (rewrite ?Zlength_sublist; omega).
        erewrite sublist_last_1 by omega.
        rewrite Znth_map' with (b0 := 0), upd_Znth_diff', upd_Znth_same;
          rewrite ?Zlength_repeat; simpl in *; try omega.
        rewrite <- app_assoc; auto.
      + assert (i0 = u).
        { apply repr_inj_signed; auto; apply repable_max; omega. }
        forward.
        entailer!.
        unfold MAX_THREADS in *; simpl in *.
        rewrite upd_init by (rewrite ?Zlength_sublist; omega).
        erewrite sublist_last_1 by omega.
        rewrite Znth_map' with (b0 := 0), upd_Znth_same;
          rewrite ?Zlength_repeat; simpl in *; try omega.
        rewrite <- app_assoc; auto.
      + forward.
        entailer!.
        unfold MAX_THREADS in *; simpl in *.
        rewrite upd_init by (rewrite ?Zlength_sublist; omega).
        erewrite sublist_last_1 by omega.
        rewrite Znth_map', upd_Znth_diff', upd_Znth_diff';
          rewrite ?Zlength_repeat; simpl in *; try omega; try (intro; subst; contradiction).
        rewrite Znth_repeat, <- app_assoc; auto.
      + intros; unfold overridePost, exit_tycon.
        if_tac; [|apply drop_tc_environ].
        Intros; subst; unfold POSTCONDITION, abbreviate; entailer!.
      + intros; unfold overridePost, exit_tycon.
        if_tac; [|apply drop_tc_environ].
        Intros; subst; unfold POSTCONDITION, abbreviate, normal_ret_assert; entailer!. }
    forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
    { lock_props.
      unfold x_inv.
      rewrite Zminus_diag, app_nil_r, sublist_same; auto.
      Exists 1 ((inr (map (fun x => vint x) (upd_Znth u (upd_Znth t (repeat 0 (Z.to_nat MAX_THREADS)) (Znth t V 0))
        c))) : val * val + list val) cx tx; entailer!.
      + simpl.
        assert (Forall (fun x0 : Z => 0 <= x0 < Int.max_signed)
          (upd_Znth u (upd_Znth t (repeat 0 10) (Znth t V 0)) c)).
        { do 2 (apply Forall_upd_Znth; auto).
          + apply Forall_repeat; computable.
          + apply Forall_Znth; auto; omega. }
        split; [eauto|].
        rewrite get_Zs_spec.
        match goal with H : exists h R, _ |- _ => destruct H as (h & R1 & HR1 & ?) end.
        exists ((Z.to_nat t, VC_of V) :: h); do 2 eexists; simpl; eauto.
        econstructor; eauto.
        instantiate (1 := false); split; auto; simpl in *.
        inv HR1.
        right; right.
        repeat split; auto.
        * rewrite Int.signed_repr; auto.
          intro Y; apply Z2Nat.inj in Y; auto; omega.
        * rewrite !VC_of_upd, VC_of_bot
            by (rewrite ?Zlength_repeat, ?Z2Nat.id; unfold MAX_THREADS in *; simpl; omega).
          rewrite !Int.signed_repr by auto.
          rewrite VC_of_spec, Z2Nat.id by omega; auto.
        * eapply Forall_impl; [|eauto].
          intro; simpl; pose proof Int.min_signed_neg; split; omega.
      + unfold_data_at 4%nat; rewrite HRx; cancel.
        rewrite field_at_data_at'; simpl.
        unfold data_at at 4; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
        unfold withspacer; simpl.
        rewrite field_at_data_at' with (gfs := [UnionField _vc]); entailer!; [|cancel].
        rewrite field_compatible_cons; unfold in_members; simpl; split; auto. }
    forward.
    Exists (Z.to_nat cx, Z.to_nat tx) (E (Z.to_nat c, Z.to_nat u)).
    rewrite lock_struct_array, field_at_data_at'; entailer!.
    repeat eexists; eauto.
    right; right; split; eauto.
    intro Y; apply Z2Nat.inj in Y; auto; omega.
  - exploit (repable_max tx); [omega | intro].
    forward_call (Tsh, Ews, Znth x Ws Vundef, cx, tx,
      force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), V).
    { rewrite gvar_eval_var with (v := C); auto.
      repeat split; auto; destruct C; auto; contradiction. }
    { rewrite field_at_data_at'; entailer!. }
    { repeat (split; auto). }
    match goal with H : exists vs, _ /\ _ |- _ => destruct H as (vs & ? & ?); subst end.
    match goal with |-semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROP (~e_le (Z.to_nat cx, Z.to_nat tx) (VC_of V)) (LOCALx Q (SEPx R))) end.
    { assert_PROP (Zlength vs = MAX_THREADS) as Hlen.
      { entailer!.
        match goal with H : value_fits teorvc _ |- _ =>
          rewrite value_fits_eq in H; simpl in H; destruct H as (_ & Hfits) end.
        rewrite value_fits_eq in Hfits; simpl in Hfits.
        rewrite value_fits_eq in Hfits; simpl in Hfits.
        unfold unfold_reptype in Hfits; simpl in Hfits; rewrite Zlength_map in Hfits; tauto. }
      forward.
      simpl.
      destruct (Z.to_nat cx <=? VC_of V (Z.to_nat tx))%nat eqn: Ht; [|contradiction].
      apply leb_complete in Ht.
      forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
      { lock_props.
        unfold x_inv.
        Exists tag ((inr (map (fun x => vint x) (upd_Znth t vs (Znth t V 0)))) : val * val + list val)
          cx tx; entailer!.
        + if_tac; [contradiction|].
          assert (Forall (fun x0 : Z => 0 <= x0 < Int.max_signed) (upd_Znth t vs (Znth t V 0))).
          { apply Forall_upd_Znth; auto.
            apply Forall_Znth; auto; omega. }
          split; [eauto|].
          match goal with H : exists h R, _ |- _ => destruct H as (h & R1 & HR1 & ?) end.
          simpl in *.
          rewrite Int.signed_repr in * by auto.
          if_tac; [contradiction|].
          assert (Forall repable_signed vs).
          { eapply Forall_impl; [|eauto].
            intro; simpl; pose proof Int.min_signed_neg; split; omega. }
          rewrite get_Zs_spec in *; auto.
          exists ((Z.to_nat t, VC_of V) :: h); do 2 eexists; eauto.
          econstructor; eauto.
          instantiate (1 := false); simpl.
          inv HR1.
          repeat split; auto.
          rewrite VC_of_upd, VC_of_spec, Z2Nat.id; auto; omega.
          { eapply Forall_impl; [|eauto].
            intro; simpl; pose proof Int.min_signed_neg; split; omega. }
        + rewrite <- upd_Znth_map; cancel. }
      forward.
      Exists (Z.to_nat cx, Z.to_nat tx) (VC (VC_of V)).
      rewrite lock_struct_array, field_at_data_at'; entailer!.
      eauto 8. }
    { forward.
      entailer!.
      match goal with H : (_ <= _)%nat |- _ => apply leb_correct in H; rewrite H in *; discriminate end. }
    { forward_call tt.
      contradiction. }
Admitted.

Lemma body_instr_write : semax_body Vprog Gprog f_instr_write instr_write_spec.
Proof.
  start_function.
  rewrite <- lock_struct_array.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
  unfold x_inv at 2.
  Intros tag Rx cx tx.
  forward.
  forward.
  forward.
  assert_PROP (Zlength V = MAX_THREADS) as HV.
  { entailer!.
    match goal with H : value_fits _ (map _ V) |- _ => rewrite value_fits_eq in H; simpl in H;
      destruct H as (Hlen & _) end.
    unfold unfold_reptype in Hlen; simpl in Hlen.
    rewrite Zlength_map in Hlen; rewrite Hlen; auto. }
  forward.
  forward.
  assert (repable_signed t) by (apply repable_max; omega).
  assert (repable_signed tx) by (apply repable_max; omega).
  assert (repable_signed (Znth t V 0)).
  { apply Forall_Znth; [omega|].
    pose proof Int.min_signed_neg.
    eapply Forall_impl; [|eauto]; split; omega. }
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP ()
      (LOCALx (temp _t'1 (vint (if eq_dec cx (Znth t V 0) then if eq_dec tx t then 1 else 0 else 0))
      :: Q) (SEPx R))) end.
  { forward.
    entailer!.
    rewrite eq_dec_refl.
    unfold eval_binop; simpl.
    pose proof (Int.eq_spec (Int.repr tx) (Int.repr t)).
    destruct (Int.eq (Int.repr tx) (Int.repr t)); simpl; destruct (eq_dec tx t); auto.
    - match goal with H : Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in H; auto end.
      contradiction n; auto.
    - subst; contradiction. }
  { forward.
    entailer!.
    if_tac; [contradiction | auto]. }
  match goal with |-semax _ ?P _ _ => forward_if P end.
  { forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
    { lock_props.
      unfold x_inv.
      Exists tag Rx cx tx; entailer!. }
    forward.
    match goal with H : exists h R, _ |- _ => destruct H as (h & R1 & ? & ?) end.
    Exists (Z.to_nat cx, Z.to_nat tx) R1.
    rewrite lock_struct_array.
    destruct (eq_dec cx (Znth t V 0)); [|contradiction].
    destruct (eq_dec tx t); [|contradiction].
    subst; entailer!.
    do 2 eexists; left.
    rewrite VC_of_spec, Z2Nat.id; auto; omega. }
  { forward.
    entailer!. }
  forward_call (Tsh, Ews, Znth x Ws Vundef, cx, tx,
    force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), V).
  { rewrite gvar_eval_var with (v := C); auto.
    repeat split; auto; destruct C; auto; contradiction. }
  { rewrite field_at_data_at'; entailer!. }
  { repeat (split; auto). }
  match goal with |-semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROP (e_le (Z.to_nat cx, Z.to_nat tx) (VC_of V)) (LOCALx Q (SEPx R))) end.
  { forward_call tt.
    contradiction. }
  { forward.
    entailer!.
    destruct (Z.to_nat cx <=? VC_of V (Z.to_nat tx))%nat eqn: Hle; [|absurd (0 = 0); auto].
    rewrite <- Nat.leb_le; auto. }
  forward.
  assert_PROP (field_compatible teorvc [] (Znth x Rs Vundef)) by entailer!.
  unfold_data_at 4%nat.
  rewrite field_at_data_at' with (gfs := [StructField _data]); simpl.
  unfold data_at at 4; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
  unfold withspacer; simpl.
  forward_if (fun _ : environ => FF); [| |apply semax_ff];
    destruct (eq_dec tag 0); try solve [absurd (tag = 0); auto].
  - match goal with H : exists c u, _ |- _ => destruct H as (c & u & ? & ? & ? & ?); subst end.
    assert (repable_signed c) by (pose proof Int.min_signed_neg; split; omega).
    assert (repable_signed u) by (apply repable_max; omega).
    rewrite field_at_data_at' with (gfs := [UnionField _e]); simpl; Intros.
    forward_call (Tsh, Ews, offset_val 4 (Znth x Rs Vundef), c, u,
      force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), V).
    { rewrite gvar_eval_var with (v := C); auto. }
    { entailer!. }
    { repeat (split; auto). }
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (~e_le (Z.to_nat c, Z.to_nat u) (VC_of V)) (LOCALx Q (SEPx R))) end.
    + forward.
      forward.
      destruct ((Z.to_nat c <=? VC_of V (Z.to_nat u))%nat) eqn: Hle; [|contradiction].
      rewrite Nat.leb_le in Hle.
      forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
      { lock_props.
        unfold x_inv.
        Exists 0 ((inl (vint c, vint u)) : val * val + list val) (Znth t V 0) t; entailer!.
        { rewrite eq_dec_refl; split; [do 3 eexists; eauto; split; auto|].
          match goal with H : exists h R, _ |- _ => destruct H as (h & R1 & HR1 & ?) end.
          exists ((Z.to_nat t, VC_of V) :: h); do 2 eexists; simpl; eauto.
          econstructor; eauto.
          instantiate (1 := true); simpl.
          inv HR1.
          right; repeat split; auto; rewrite ?VC_of_spec, ?Int.signed_repr, ?Z2Nat.id; auto; omega. }
        unfold_data_at 4%nat; cancel.
        rewrite field_at_data_at'; simpl.
        unfold data_at at 4; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
        unfold withspacer; simpl.
        rewrite field_at_data_at' with (gfs := [UnionField _e]); simpl; entailer!; cancel. }
      forward.
      Exists (Z.to_nat cx, Z.to_nat tx) (E (Z.to_nat c, Z.to_nat u)).
      entailer!.
      { eauto 7. }
      rewrite lock_struct_array, field_at_data_at'; entailer!.
    + forward.
      entailer!.
      match goal with H : (_ <= _)%nat |- _ => apply leb_correct in H; rewrite H in *; discriminate end.
    + forward_call tt.
      entailer!.
  - match goal with H : exists vs, _ /\ _ |- _ => destruct H as (vs & ? & ?); subst end.
    rewrite field_at_data_at' with (gfs := [UnionField _]); simpl; Intros.
    forward_call (Tsh, Ews, offset_val 4 (Znth x Rs Vundef),
      force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), vs, V).
    { rewrite gvar_eval_var with (v := C); auto. }
    { entailer!. }
    forward_if (fun _ : environ => FF).
    + assert_PROP (Zlength vs = MAX_THREADS).
      { entailer!.
        rewrite Zlength_map in *; auto. }
      forward.
      forward.
      forward.
      replace_SEP 0 (data_at Tsh tepoch (Vundef, Vundef) (offset_val 4 (Znth x Rs Vundef)) *
        spacer Tsh 8 40 (offset_val 4 (Znth x Rs Vundef))).
      { entailer!.
        eapply derives_trans; [eapply split2_data_at_Tarray_unfold with (n1 := 2); eauto|].
        { unfold MAX_THREADS; computable. }
        rewrite <- data_at_epoch; cancel.
        unfold spacer; simpl.
        unfold at_offset.
        eapply derives_trans; [apply data_at_memory_block|].
        rewrite field_address0_offset; auto.
        apply field_compatible_field_compatible0.
        rewrite field_compatible_cons; simpl.
        split; [unfold MAX_THREADS; computable | auto]. }
      assert_PROP (offset_val 0 (offset_val 4 (Znth x Rs Vundef)) =
        field_address tepoch [StructField _time] (offset_val 4 (Znth x Rs Vundef))).
      { entailer!.
        rewrite field_address_offset; normalize.
        rewrite field_compatible_cons; unfold in_members; simpl; auto. }
      Intros; forward.
      assert_PROP (offset_val 4 (offset_val 4 (Znth x Rs Vundef)) =
        field_address tepoch [StructField _thread] (offset_val 4 (Znth x Rs Vundef))).
      { entailer!.
        rewrite field_address_offset; normalize.
        rewrite field_compatible_cons; unfold in_members; simpl; auto. }
      forward.
      destruct (vc_leb (VC_of vs) (VC_of V) _) eqn: Hle; [|contradiction].
      rewrite vc_leb_spec in Hle
        by (apply VC_of_bounded'; rewrite Z2Nat.id; auto; unfold MAX_THREADS in *; omega).
      forward_call (Znth x locks Vundef, lsh, x_inv sh Rs Ws x R W).
      { lock_props.
        unfold x_inv.
        Exists 0 ((inl (vint 0, vint 0)) : val * val + list val) (Znth t V 0) t; entailer!.
        + simpl.
          split; [do 3 eexists; eauto; unfold MAX_THREADS; computable|].
          match goal with H : exists h R, _ |- _ => destruct H as (h & R1 & HR1 & ?) end.
          exists ((Z.to_nat t, VC_of V) :: h); do 2 eexists; eauto.
          econstructor; eauto.
          instantiate (1 := true); simpl in *.
          right.
          rewrite Int.signed_repr in HR1 by auto.
          destruct (eq_dec tag 0); [contradiction|].
          rewrite get_Zs_spec in HR1.
          inv HR1.
          repeat split; auto.
          rewrite VC_of_spec, Z2Nat.id; auto; omega.
          { eapply Forall_impl; [|eauto].
            intro; simpl; pose proof Int.min_signed_neg; split; omega. }
        + unfold_data_at 3%nat; cancel.
          rewrite field_at_data_at' with (t := teorvc); simpl.
          unfold data_at at 3; erewrite field_at_Tunion with (t0 := Tunion _ _) by (simpl; eauto); simpl.
          unfold withspacer; simpl.
          rewrite field_at_data_at' with (gfs := [UnionField _]); entailer!; [|cancel].
          match goal with H : field_compatible (Tunion _ _) _ _ |- _ =>
            rewrite field_compatible_cons in H |- *; unfold in_members; simpl in *; tauto end. }
      forward.
      Exists (Z.to_nat cx, Z.to_nat tx) (VC (VC_of vs)); entailer!.
      { eauto 7. }
      rewrite lock_struct_array, field_at_data_at'; entailer!.
    + forward_call tt.
      entailer!.
    + intros; unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; go_lowerx.
      contradiction.
Qed.

Lemma body_vc_join : semax_body Vprog Gprog f_vc_join vc_join_spec.
Proof.
  start_function.
  assert_PROP (Zlength vs1 = MAX_THREADS /\ Zlength vs2 = MAX_THREADS).
  { entailer!.
    rewrite Zlength_map, Z.max_r in * by (unfold MAX_THREADS; computable); auto. }
  assert (Zlength (map (fun '(a, b) => vint (Z.max a b)) (combine vs1 vs2)) = MAX_THREADS).
  { rewrite Zlength_map, Zlength_combine, Z.min_l; omega. }
  forward_for_simple_bound MAX_THREADS (EX i : Z, PROP () LOCAL (temp _tgt v1; temp _src v2)
    SEP (data_at sh1 (tarray tint MAX_THREADS)
      (sublist 0 i (map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine vs1 vs2)) ++
       sublist i MAX_THREADS (map (fun x : Z => vint x) vs1)) v1;
     data_at sh2 (tarray tint MAX_THREADS) (map (fun x => vint x) vs2) v2)).
  { unfold MAX_THREADS; computable. }
  { unfold MAX_THREADS; computable. }
  - rewrite sublist_nil; entailer!.
    rewrite sublist_same; auto.
  - assert (Zlength (sublist 0 i (map (fun '(a, b) => vint (Z.max a b)) (combine vs1 vs2))) = i) as Hi.
    { rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; omega. }
    forward.
    { entailer!.
      rewrite app_Znth2, Hi, Zminus_diag, Znth_sublist by omega.
      rewrite Znth_map with (d' := 0) by omega; simpl; auto. }
    forward.
    rewrite app_Znth2, Hi, Zminus_diag, Znth_sublist by omega.
    rewrite Znth_map with (d' := 0) by omega.
    rewrite Z.add_0_l.
    forward_call (Znth i vs1 0, Znth i vs2 0).
    { split; apply Forall_Znth; auto; omega. }
    forward.
    entailer!.
    rewrite upd_Znth_app2, Hi, Zminus_diag, upd_Znth0, sublist_sublist;
      rewrite ?Hi, ?Zlength_sublist; rewrite ?Zlength_map; try omega.
    erewrite Z.sub_simpl_r, sublist_last_1; try omega.
    rewrite Znth_map', Znth_combine by omega.
    rewrite <- app_assoc, Z.add_comm; apply derives_refl.
  - forward.
    rewrite sublist_nil, sublist_same, app_nil_r by auto; entailer!.
Qed.

Lemma body_instr_acquire : semax_body Vprog Gprog f_instr_acquire instr_acquire_spec.
Proof.
  start_function.
  rewrite !field_at_data_at'; simpl; Intros.
  forward_call (Ews, lsh, force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)),
    force_val (sem_add_pi (tarray tint MAX_THREADS) L (vint m)), V1, V2).
  { rewrite gvar_eval_var with (v := C), gvar_eval_var with (v := L); auto.
    repeat split; auto; destruct C, L; auto; contradiction. }
  { entailer!. }
  forward.
  rewrite !field_at_data_at'; entailer!.
  intros (((sC, sL), sR), sW).
  eexists; intros; constructor; eauto.
Qed.

Lemma body_instr_release : semax_body Vprog Gprog f_instr_release instr_release_spec.
Proof.
  start_function.
  assert_PROP (Zlength V1 = MAX_THREADS /\ Zlength V2 = MAX_THREADS).
  { entailer!.
    repeat match goal with H : value_fits _ _ |- _ => rewrite value_fits_eq in H end; simpl in *.
    unfold unfold_reptype in *; simpl in *; rewrite Zlength_map in *; tauto. }
  rewrite <- seq_assoc.
  forward_for_simple_bound MAX_THREADS (EX i : Z, PROP ( )
   LOCAL (temp _t (vint t); temp _m (vint m); gvar _C C; gvar _L L)
   SEP (field_at Ews (tarray (tarray tint MAX_THREADS) MAX_THREADS)
          [ArraySubsc t] (map (fun x : Z => vint x) V1) C;
        field_at Ews (tarray (tarray tint MAX_THREADS) MAX_LOCKS) [ArraySubsc m]
          (sublist 0 i (map (fun x => vint x) V1) ++
           sublist i MAX_THREADS (map (fun x => vint x) V2)) L)).
  { unfold MAX_THREADS; computable. }
  { unfold MAX_THREADS; computable. }
  { entailer!.
    rewrite sublist_same; auto.
    rewrite Zlength_map; symmetry; tauto. }
  - forward.
    forward.
    { entailer!.
      match goal with H : field_compatible _ _ L |- _ => rewrite field_compatible_cons in H;
        simpl in H; tauto end. }
    entailer!.
    assert (Zlength (sublist 0 i (map (fun x : Z => vint x) V1)) = i) as HV1.
    { rewrite Zlength_sublist by (rewrite ?Zlength_map; omega); omega. }
    assert (Zlength (sublist i MAX_THREADS (map (fun x : Z => vint x) V2)) = MAX_THREADS - i) as HV2.
    { rewrite Zlength_sublist by (rewrite ?Zlength_map; omega); auto. }
    rewrite upd_Znth_app2; rewrite HV1, ?HV2; try omega.
    rewrite Zminus_diag, upd_Znth0, sublist_sublist; rewrite ?HV2; try omega.
    erewrite Z.sub_simpl_r, sublist_last_1 by (rewrite ?Zlength_map; omega).
    rewrite Znth_map', <- app_assoc, Z.add_comm; apply derives_refl.
  - assert_PROP (0 <= t < MAX_THREADS).
    { entailer!.
      match goal with H : field_compatible _ _ C |- _ => rewrite field_compatible_cons in H;
        simpl in H; tauto end. }
    forward.
    forward.
    forward.
    rewrite sublist_nil, sublist_same, app_nil_r by (rewrite ?Zlength_map; auto; omega).
    rewrite <- upd_Znth_map.
    entailer!.
    intros (((sC, sL), sR), sW).
    eexists; intros; constructor; auto.
Qed.

Lemma vc_max_comm : forall V1 V2,
  map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine V1 V2) =
  map (fun x => let '(a, b) := x in vint (Z.max a b)) (combine V2 V1).
Proof.
  induction V1; destruct V2; auto; simpl.
  rewrite Z.max_comm, IHV1; auto.
Qed.

Lemma body_instr_fork : semax_body Vprog Gprog f_instr_fork instr_fork_spec.
Proof.
  start_function.
  rewrite !field_at_data_at'; simpl; Intros.
  assert_PROP (Zlength V1 = MAX_THREADS /\ Zlength V2 = MAX_THREADS).
  { entailer!.
    repeat match goal with H : value_fits _ _ |- _ => rewrite value_fits_eq in H end; simpl in *.
    unfold unfold_reptype in *; simpl in *; rewrite Zlength_map in *; tauto. }
  forward_call (Ews, Ews, force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint u)),
    force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)), V2, V1).
  { rewrite gvar_eval_var with (v := C); auto.
    repeat split; auto; destruct C; auto; contradiction. }
  { entailer!. }
  assert (0 <= t < MAX_THREADS).
  { match goal with H : field_compatible _ [ArraySubsc t] _ |- _ =>
      rewrite field_compatible_cons in H; simpl in H; tauto end. }
  assert_PROP (force_val (sem_add_pi tint (force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)))
    (vint t)) = field_address (tarray tint MAX_THREADS) [ArraySubsc t]
    (force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)))).
  { entailer!.
    match goal with H : field_compatible _ _ (force_val (sem_add_pi _ _ (vint t))) |- _ =>
      rewrite sem_add_pi_ptr in H by auto; simpl in H end.
    rewrite field_address_offset; normalize.
    rewrite field_compatible_cons; simpl; tauto. }
  forward.
  { entailer!.
    rewrite gvar_eval_var with (v := C); auto.
    rewrite !sem_add_pi_ptr by auto; simpl; auto. }
  forward.
  { entailer!.
    rewrite gvar_eval_var with (v := C); auto.
    rewrite !sem_add_pi_ptr by auto; simpl; auto. }
  forward.
  rewrite !field_at_data_at', <- upd_Znth_map, vc_max_comm; entailer!; [|cancel].
  intros (((sC, sL), sR), sW).
  eexists; intros; constructor; auto.
Qed.

Lemma body_instr_join : semax_body Vprog Gprog f_instr_join instr_join_spec.
Proof.
  start_function.
  rewrite !field_at_data_at'; simpl; Intros.
  assert_PROP (Zlength V1 = MAX_THREADS /\ Zlength V2 = MAX_THREADS).
  { entailer!.
    repeat match goal with H : value_fits _ _ |- _ => rewrite value_fits_eq in H end; simpl in *.
    unfold unfold_reptype in *; simpl in *; rewrite Zlength_map in *; tauto. }
  forward_call (Ews, Ews, force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint t)),
    force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint u)), V1, V2).
  { rewrite gvar_eval_var with (v := C); auto.
    repeat split; auto; destruct C; auto; contradiction. }
  { entailer!. }
  assert (0 <= u < MAX_THREADS).
  { match goal with H : field_compatible _ [ArraySubsc u] _ |- _ =>
      rewrite field_compatible_cons in H; simpl in H; tauto end. }
  assert_PROP (force_val (sem_add_pi tint (force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint u)))
    (vint u)) = field_address (tarray tint MAX_THREADS) [ArraySubsc u]
    (force_val (sem_add_pi (tarray tint MAX_THREADS) C (vint u)))).
  { entailer!.
    match goal with H : field_compatible _ _ (force_val (sem_add_pi _ _ (vint u))) |- _ =>
      rewrite sem_add_pi_ptr in H by auto; simpl in H end.
    rewrite field_address_offset; normalize.
    rewrite field_compatible_cons; simpl; tauto. }
  forward.
  { entailer!.
    rewrite gvar_eval_var with (v := C); auto.
    rewrite !sem_add_pi_ptr by auto; simpl; auto. }
  forward.
  { entailer!.
    rewrite gvar_eval_var with (v := C); auto.
    rewrite !sem_add_pi_ptr by auto; simpl; auto. }
  forward.
  rewrite !field_at_data_at', <- upd_Znth_map; entailer!; [|cancel].
  intros (((sC, sL), sR), sW).
  eexists; intros; constructor; auto.
Qed.
