# Experiments with Universal Algebra in Lean

This repository contains some constructions arising from universal algebra, formalized in the lean proof assistant.

We define the following structures:
1. A *language* defined as a structure in the following way:
  ```lean
  structure lang := (op : ℕ → Type v)
  ```
  Here `op n` should be thought of as the type of `n`-ary operations.
  We introduce a `has_coe_to_fun` for languages, so that we can just write `L n` for the type of `n`-ary operations associated to a language `L`.
 
2. Given any language `L`, we defined a type of raw algebras for `L`, i.e. types endowed with an interpretation of each such `n`-ary operation.
  We implement a bundled approach for this, as follows.
  ```lean
  structure ralg (L : lang.{v}) :=
  (carrier : Type u)
  (appo {n} : L n → vector carrier n → carrier)
  ```
3. Given a language `L`, we defined *terms* of `L` by an inductive procedure as follows:
  ```lean
  inductive term (L : lang.{v}) : ℕ → ℕ → Type v
  | of {n} : L n → term n 1
  | proj {m n} : (fin m → fin n) → term n m
  | comp {a b c} : term a b → term b c → term a c
  | liftl {a b c} : term a b → term (a + c) (b + c)
  | liftr {a b c} : term a b → term (c + a) (c + b)
  ```
  A term of type `L.term m n` should be thought of as an operations which sends `m`-tuples to `n`-tuples.
  Any type with an interpretation of `L` obtains an interpretation for any such term by applying structural induction.

4. Given a language `L`, we defined the type of *rules* on `L`, which are relations on the terms of `L`.
5. Given a language `L` and rules `R`, an *algebra* for the pair `(L,R)` is a raw algebra which satisfies the axioms outlined by the rules.
  Our construction for this, denoted `ualg` extends `ralg` as follows
  ```lean
  structure ualg (L : lang) (R : rules L) extends ralg L :=
  (cond_eq {m n} {t1 t2 : L.term m n} {as : vector carrier m} : R t1 t2 → applyt t1 as = applyt t2 as)
  ```
  Here `L.term` is the (dependent) type of terms generated by the given language `L`, and `applyt` is the interpretation of such terms in the given raw algebra. 

# Morphisms of languages/rules

Given two languages `L1` and `L2`, a morphism `L1 -> L2` is simply the data of a function `L1 n -> L2 n` for every natural `n`.
This is extended to morphisms of pairs `(L1,R1) -> (L2,R2)` where `Ri : rules Li` in the obvious way as follows:
```lean
structure rulesHom {L1 : lang} {L2 : lang} (R1 : rules L1) (R2 : rules L2) :=
(lhom : L1 →# L2)
(map_cond {m n} {t1 t2 : L1.term m n} : R1 t1 t2 → R2 (t1.mapt lhom) (t2.mapt lhom))
```
We use the notation `→#` to denote morphisms of languages.
In the code above, for a morphism `f` from `L1` to `L2`, the function `t.mapt f` maps a term in `L1` to a term in `L2`.
We also introduce the notation `→$` to denote morphisms of pairs consisting of a language and associated rules.
If `Ri`, ` i = 1,2` are rules on languages `Li`, then we can simply write `R1 →$ R2` for the type of morphisms of pairs `(L1,R1) -> (L2,R2)`.

# Left adjoints

Given a morphism of pairs `(L1,R1) -> (L2,R2)` as above, there is an obvious forgetful functor from `(L2,R2)`-algebras to `(L1,R1)`-algebras.
The most substantial portion of this work is in the construction of the *left adjoint* to this forgetful functor. 
This left adjoint is construted by combining three steps, and the resulting construction can be found in the file `src/fron_ualg.lean`.
It is perhaps important to mention that all of the usual "free" constructions in algebra are special cases of this.