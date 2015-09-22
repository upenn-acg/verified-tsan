Require Import Lang.
Require Import Util.
Set Implicit Arguments.
Definition x :=1.
Definition y :=2.
Definition z :=3.
Definition a :=1.
Definition b :=2.
Definition c :=3.
Definition t1 :=1.
Definition t2 :=2.
Definition l1 :=1.
Definition l2 :=2.
Definition p1_t1 (l : lock) :=
[
    Lock l;
    Assign a (I 0);
    Assign a (Plus (V a) (I 1)); 
    Store x (V a);
    
    Unlock l
].

Definition p1_t2 (l : lock):=
[
    Lock l;
    Load b x;
    Assign b (Plus (V b) (I 2));
    Store x (V b);
    Unlock l
].

Definition p1 :=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l1);
    Wait(t1);
    Wait(t2)
].

(* a racy program*)

Definition p2 :=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l2);  (* x is protected by different locks*)
    Wait(t1);
    Wait(t2)
].

Definition handler (cop : conc_op):=
match cop with
| Read t x v =>  [
                     Load 0 x (* race detection code here?*)
]
| _ => []
end.

Definition instrument_instr(ins : instr) (t: tid): prog :=
match ins with
| Load a x   => Load a x::(handler (Read t x a))
| _          => []
end.

Fixpoint instrument(p: prog)(t: tid) : prog:=
match p with
| [] => []
| ins::inss => (instrument_instr ins t)++(instrument inss t)
end.