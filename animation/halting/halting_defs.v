Require Import Ciaffaglione.datatypes.
Require Import Ciaffaglione.bigstep.
Require Import Ciaffaglione.coinduction.
Require Import Ciaffaglione.adequacy.streams_vs_lists.
Require Import Ciaffaglione.join.shift_maxsource.
(*********** Definition of the HALTING PROBLEM ***********)

(* halt T n says that machine T stops on input n *)
Definition halt (T:Spec) (n:nat) := exists t:Tape,
           bf T (pair Bs (app_ls (ones (S n)) Bs)) 0
                t                                  (max_source T 0 + 1).

(* Assumptions: coding function, halting machine *)
Parameter gamma: Spec -> nat.

(* the below definitions is the correctness specification of
   the machine HM:
   - if the Turing machine T stops on input n, HM returns 0
   - if it does not stop, HM returns 1
   note that 0 is coded by a single 1 on the output tape,
    surrounded by blanks,
   1 is coded by two consecutive 1s and then blanks, etc.
*)
Parameter HM: Spec.
Definition HM_decides_stop := forall T:Spec, forall n:nat,
           halt T n ->
           bf HM (pair Bs (app_ls (ones (S (gamma T)))
                                  (Cons B (app_ls (ones (S n)) Bs))))
                 0
                 (pair Bs (Cons one Bs))
                 (max_source HM 0 + 1).

Definition HM_decides_loop := forall T:Spec, forall n:nat,
           ~halt T n ->
           bf HM (pair Bs (app_ls (ones (S (gamma T)))
                                  (Cons B (app_ls (ones (S n)) Bs))))
                 0
                 (pair Bs (Cons one (Cons one Bs)))
                 (max_source HM 0 + 1).