import data.equiv.fin

/-!

# Finite Tuples

This file contains some definitions and results around finite tuples in an arbitrary type.
We have chosen to implement finite `n`-tuples in `A` as maps `fin n → A`.
This is primarily due to some restrictions arising from our inductive constructions.

-/

def ftuple (A : Type*) (n : ℕ) := fin n → A

namespace ftuple
section definitions
/-!
## Definitions
This section contains some basic definitions.
-/

variables {A : Type*} {B : Type*}

local notation `η` := sum_fin_sum_equiv.to_fun 
local notation `δ` := sum_fin_sum_equiv.inv_fun

def cast {m n} (h : m = n) (as : ftuple A m) : ftuple A n := eq.rec_on h as
def cast_to {m} (as : ftuple A m) (n) (h : m = n) : ftuple A n := as.cast h
def of (a : A) : ftuple A 1 := λ _, a
def append {m n} (as : ftuple A m) (bs : ftuple A n) : ftuple A (m+n) := λ i, sum.cases_on (δ i) as bs
def map {n} (as : ftuple A n) (f : A → B) : ftuple B n := f ∘ as
def proj {m n} (f : fin m → fin n) (as : ftuple A n) : ftuple A m := as ∘ f
def init {m n} (as : ftuple A (m + n)) : ftuple A m := λ i, as (η $ sum.inl i)
def last {m n} (as : ftuple A (m + n)) : ftuple A n := λ i, as (η $ sum.inr i)
def compl {m n} (as : ftuple A (m+n)) (f : ftuple A m → A) (g : ftuple A (1 + n) → A) : A := 
  g $ append (of $ f as.init) as.last
def compr {m n} (as : ftuple A (n+m)) (f : ftuple A m → A) (g : ftuple A (n + 1) → A) : A := 
  g $ append as.init $ of $ f as.last
end definitions

section map_lemmas

variables {A : Type*} {B : Type*} 

@[simp]
lemma map_of (a : A) (f : A → B) : (of a).map f = of (f a) := sorry

@[simp]
lemma map_append {m n} (as : ftuple A m) (bs : ftuple A n) (f : A → B) : 
  (as.append bs).map f = (as.map f).append (bs.map f) := sorry

@[simp]
lemma map_proj {m n} (f : fin m → fin n) (g : A → B) (as : ftuple A n) : 
  (as.proj f).map g = (as.map g).proj f := rfl

@[simp]
lemma map_init {m n} (f : A → B) (as : ftuple A (m+n)) : as.init.map f = (as.map f).init := sorry

@[simp]
lemma map_last {m n} (f : A → B) (as : ftuple A (m+n)) : as.last.map f = (as.map f).last := sorry

end map_lemmas

end ftuple