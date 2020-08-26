import .to_mathlib

/-! 

# Languages and raw algebras.

A language is just a dependent type `ℕ → Type*`.
We wrap this in a structure in order to avoid writing `@L` in certain cases, but we immediately introduce a coersion to functions which allows us to write `L n`.
The idea is that `L n` is the type of `n`-ary functions in our language.

A *raw algebra* on a language `L` is just a type with interpretation of terms of `L n` as an `n`-ary function.
A morphism of raw algebras `A →$[L] B` is a function `A → B` which is compatible with the `n`-ary operations from the language.

-/

structure lang := (op : ℕ → Type*)

namespace lang
instance : has_coe_to_fun lang := ⟨_,op⟩
end lang


/-!
# Terms 

TODO: explain this.
-/

namespace lang
universe v
inductive term (L : lang.{v}) : ℕ → Type v 
| of {n} : L n → term n
| get : term 1
| proj {m n} : (fin n → fin m) → term n → term m
| compl {m n : ℕ} : term m → term (1 + n) → term (m + n)
| compr {m n : ℕ} : term m → term (n + 1) → term (n + m)
-- think about whether to put n + m or m + n here

def gen (L : lang.{v}) : lang.{v} := ⟨L.term⟩
end lang
/-!
# Rules
-/

structure rules (L : lang) := (cond {n} : L.gen n → L.gen n → Prop)

namespace rules
instance {L} : has_coe_to_fun (rules L) := ⟨_,cond⟩
end rules

namespace lang
def vac (L : lang) : rules L := ⟨λ _ _ _, false⟩
end lang

/-!
# lang_hom and rules_hom
-/

structure lang_hom (L1 : lang) (L2 : lang) := (map_op {n} : L1 n → L2 n)

namespace lang_hom
instance {L1} {L2} : has_coe_to_fun (lang_hom L1 L2) := ⟨_,map_op⟩

def mapt {n} {L1} {L2} (f : lang_hom L1 L2) (t : L1.term n) : L2.term n :=
  lang.term.rec_on t 
  (λ _ u, lang.term.of $ f u) 
  (lang.term.get)
  (λ _ _ g _, lang.term.proj g)
  (λ _ _ _ _, lang.term.compl) 
  (λ _ _ _ _, lang.term.compr)

def gen {L1} {L2} (f : lang_hom L1 L2) : lang_hom L1.gen L2.gen := ⟨λ n, mapt f⟩
end lang_hom

structure rules_hom {L1 : lang} (R1 : rules L1) {L2 : lang} (R2 : rules L2) := 
(lhom : lang_hom L1 L2)
(cond_imp {n} {t1 t2 : L1.gen n} : R1 t1 t2 → R2 (lhom.gen t1) (lhom.gen t2))

namespace rules_hom
instance {L1} {R1 : rules L1} {L2} {R2 : rules L2} : has_coe_to_fun (rules_hom R1 R2) := ⟨_,cond_imp⟩
end rules_hom

infixr ` →# `:25 := lang_hom
infixr ` →# `:25 := rules_hom
