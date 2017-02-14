Require Import progs.conclib.
Require Import List.
Require Import msl.eq_dec.
Require Import Arith.
Require Import Wf_nat.
Require Import VectorClocks.
Import ListNotations.

Close Scope Z.
Set Implicit Arguments.

(* Step 1: treat acquire loads and release stores as acquires and releases.
   In fact, since atomics can't race, atomic locations are treated as locks rather than variables.
   Relaxed operations are just noops... at first. *)

(* Race detection occurs in two phases. First, we take an SC trace and use vector clocks on it.
   Second, we use lifting to generate a set of relaxed traces represented by the SC trace.
   Section 6 describes the correctness property for the latter part. It may not be useful to prove any
   properties of just part 1. *)


Section C11Clocks.
  Context `{Types : VC_base}.

  (* Basic definitions (Section 2) *)
  Inductive operation :=
  | rd (t : tid) (x : var)
  | wr (t : tid) (x : var)
  | ldacq (t : tid) (m : lock)
  | strel (t : tid) (m : lock)
  | ldrlx (t : tid) (m : lock)
  | strlx (t : tid) (m : lock)
  | rmwrlx (t : tid) (m : lock)
  | rmwacq (t : tid) (m : lock)
  | rmwrel (t : tid) (m : lock)
  | facq (t : tid)
  | frel (t : tid).

  Global Instance op_eq : EqDec operation.
  Proof. hnf. decide equality. Qed.

  Definition trace := list operation.

(*  Definition thread_of a := match a with
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
  | hb_trans k (Hhb1 : happens_before tr i k) (Hhb2 : happens_before tr k j).*)


End VectorClocks.