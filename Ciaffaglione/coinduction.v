Require Import Ciaffaglione.datatypes.

(* recursive functions consume values of an inductive type *)
(* corecursive functions produce values in a coinductive type *)
CoFixpoint Bs := Cons B Bs.

(* corecursive definition of a stream (a, a, a, ...) *)
CoFixpoint same (a:Sym) := Cons a (same a).
CoFixpoint blink (a b:Sym) := Cons a (Cons b (blink a b)).
CoFixpoint merge (h k:HTape) := 
           match h with | Cons a h' => 
           match k with | Cons b k' => Cons a (Cons b (merge h' k'))
           end end.

(* a coinductive definition of type EqH
   - it represents an infinite stream of equalities between
     individual cells of the two half-tapes considered
   - EqH is a binary relation between two HTape values,
     results in a proposition (Prop), which may or may not hold
   - for every symbol `a` and two tapes `h, k`,
     if `h = k`, then `a:h = a:k`
   - eqh is a constructor of EqH and every element of EqH
     represents a proof of equality of 2 tapes
*)
CoInductive EqH: HTape -> HTape -> Prop :=
            eqh: forall a:Sym, forall h k:HTape,
                 EqH h k -> EqH (Cons a h) (Cons a k).


Lemma unfold_HTape: forall h:HTape, 
                    h = match h with | Cons a k => Cons a k end.
destruct h. auto.
Qed.

Lemma unfold_same: forall a:Sym, same a = (Cons a (same a)).
intro. apply (unfold_HTape (same a)).
Qed.

Lemma unfold_blink: forall a b:Sym, blink a b = (Cons a (Cons b (blink a b))).
intros. apply (unfold_HTape (blink a b)).
Qed.

Lemma unfold_merge: forall a b:Sym, forall h k:HTape,
      merge (Cons a h) (Cons b k) = (Cons a (Cons b (merge h k))).
intros. apply (unfold_HTape (merge (Cons a h) (Cons b k))).
Qed.

Lemma example: forall a b:Sym,
               EqH (merge (same a) (same b))
                   (blink a b).
(* we can now *assume* the goal as coinductive hypothesis *)
(* to actually use it, it has to be "guarded"
   by the `eqh` constructor *)
cofix co_hp.
intros.
rewrite unfold_same.
rewrite (unfold_same b).
rewrite unfold_merge.
rewrite (unfold_blink a b).
do 2 apply eqh.
(* this has the effect of repeating the above proof *ad infinitum* *)
apply co_hp.
Qed.