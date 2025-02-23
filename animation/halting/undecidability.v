Require Import Classical_Prop.
Require Import Ciaffaglione.halting.witness.
Require Import Ciaffaglione.halting.halting_defs.
Require Import Ciaffaglione.halting.halt_not_halt.
Require Import Ciaffaglione.halting.not_halt_halt.

Lemma HM_cannot_exist: 
 HM_decides_stop -> HM_decides_loop -> False.
intro HM_decides_stop_proof.
intro HM_decides_loop_proof.
elim (classic (halt witness (gamma witness))).
apply (witness_stops_absurd HM_decides_stop_proof). apply (witness_loops_absurd HM_decides_loop_proof).
Qed.