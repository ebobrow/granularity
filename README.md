# The Question

Given a proof step, probably provided by a student, is there a way to give it to
some automated theorem prover and with some weighted counting of its steps,
judge whether the student's step is at an appropriate level of granularity?

## Sub-questions

Is granularity context-dependent and is there a way to parameterize that in our
system?

At what level are the steps taken by the theorem prover and is there a specific
theorem prover that is most appropriate for this job?

With what data do we test this?

# Finding the right tool

Tools like $\Omega\text{mega}$, Dialog, and Tramp, which reconstruct proofs at the
assertion level, seem not to exist anymore.

## First thought: Observe the output of tactics like `lia` in Coq

This seems not to be feasible. Even for a really trivial proof like $\forall x,
y, x + y = y + x$, the underlying proof script is

<details>

```
simpler_arith =
fun x y : nat =>
ZifyClasses.rew_iff_rev (x + y = y + x)
  (BinInt.Z.add (BinInt.Z.of_nat x) (BinInt.Z.of_nat y) = BinInt.Z.add (BinInt.Z.of_nat y) (BinInt.Z.of_nat x))
  (ZifyClasses.mkrel nat BinNums.Z eq BinInt.Z.of_nat eq (fun x0 y0 : nat => iff_sym (Znat.Nat2Z.inj_iff x0 y0))
     (x + y) (BinInt.Z.add (BinInt.Z.of_nat x) (BinInt.Z.of_nat y))
     (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat
        BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add x (BinInt.Z.of_nat x) eq_refl y 
        (BinInt.Z.of_nat y) eq_refl) (y + x) (BinInt.Z.add (BinInt.Z.of_nat y) (BinInt.Z.of_nat x))
     (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat
        BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add y (BinInt.Z.of_nat y) eq_refl x 
        (BinInt.Z.of_nat x) eq_refl))
  (let cstr : BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat y) := Znat.Nat2Z.is_nonneg y in
   let cstr0 : BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat x) := Znat.Nat2Z.is_nonneg x in
   let __arith : forall __x2 __x1 : BinNums.Z, BinInt.Z.add __x1 __x2 = BinInt.Z.add __x2 __x1 :=
     fun __x2 __x1 : BinNums.Z =>
     let __wit := nil in
     let __varmap := VarMap.Branch (VarMap.Elt __x2) __x1 VarMap.Empty in
     let __ff :=
       Tauto.A Tauto.isProp
         {|
           RingMicromega.Flhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xO BinNums.xH));
           RingMicromega.Fop := RingMicromega.OpEq;
           RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO BinNums.xH)) (EnvRing.PEX BinNums.xH)
         |} tt in
     ZMicromega.ZTautoChecker_sound __ff __wit (eq_refl <: ZMicromega.ZTautoChecker __ff __wit = true)
       (VarMap.find BinNums.Z0 __varmap) in
   __arith (BinInt.Z.of_nat y) (BinInt.Z.of_nat x))
     : forall x y : nat, x + y = y + x

Arguments simpler_arith (x y)%nat_scope
```

</details>

## Second thought: Using Vampire as a starting point, implement my own reconstruction at the assertion level? Or scrap that and implement CoRe calculus?

## Alternate second thought: Learn about Isabelle/Isar and Sledgehammer?

This seems promising because it uses HOL and you can specify a logic/theorem for
it to use. [These](https://wwwbroy.in.tum.de/~berghofe/papers/CHIT_slides.pdf)
slides talk about examining the underlying proof object/looking at extracted
code. [These](https://isabelle.in.tum.de/~berghofe/papers/TYPES2003_slides.pdf)
slides use some sort of code extraction for theorems but I can't figure out how
it works. Would need to deep dive learn Isabelle and then code extraction.

## Alternate' second thought: Metamath/Automath? I don't really know what these are.
