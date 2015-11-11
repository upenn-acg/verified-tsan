Require Import Lang.
Require Import Util.
Require Import HBRaceDetector.
Set Implicit Arguments.
Definition x :=1.
Definition y :=2.
Definition z :=3.
Definition a :=1.
Definition b :=2.
Definition c :=3.
Definition t0 :=0.
Definition t1 :=1.
Definition t2 :=2.
Definition l1 :=1.
Definition l2 :=2.
Definition p1_t1 (l : lock) :=
[
    Lock l;
    Assign a (I 0);
    Assign a (Plus (V a) (I 1)); 
    Store (x, 0) (V a);
    
    Unlock l
].

Definition p1_t2 (l : lock):=
[
    Lock l;
    Load b (x, 0);
    Assign b (Plus (V b) (I 2));
    Store (x, 0) (V b);
    Unlock l
].

Definition p1 t1 t2:=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l1);
    Wait t1;
    Wait t2
].

(* a racy program*)

Definition p2 t1 t2:=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l2);  (* x is protected by different locks*)
    Wait t1;
    Wait t2
].





Definition C_base := 16.
Definition L_base := 32.
Definition R_base := 48.
Definition W_base := 64.
Definition local_base := 0.
(*
Definition instrumented_p1 :=instrument C_base L_base R_base W_base 3 local_base (local_base+1) (p1 1 2) t0.
Definition instrumented_p1_t1 := instrument C_base L_base R_base W_base 3 local_base (local_base+1) (p1_t1 l1) t1.
Definition instrumented_p1_t2 := instrument C_base L_base R_base W_base 3 local_base (local_base+1) (p1_t2 l1) t2.

Theorem dummy: instrumented_p1_t1 = instrumented_p1_t1.
Proof.
  unfold instrumented_p1_t1,t1.
  simpl.
  
  reflexivity.
Qed.*)
