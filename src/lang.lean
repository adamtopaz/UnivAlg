import .ftuple

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

/-
The `has_app` typeclass provides an interpretation of a language.
-/
class has_app (L : lang) (A : Type*) :=
(app {n} : L n → ftuple A n → A)

notation `applyo` := has_app.app

/-
A morphism of raw algebras relative to a language L.
Use the notation `A →$[L] B`.
-/
structure ralg_hom (L : lang) (A : Type*) (B : Type*) [has_app L A] [has_app L B] :=
(to_fn : A → B)
(applyo_map' {n} {t : L n} {as : ftuple A n} : applyo t (as.map to_fn) = to_fn (applyo t as))

notation A ` →$[`:25 L:25 `] `:0 B:0 := ralg_hom L A B

namespace ralg_hom
instance {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B] : has_coe_to_fun (A →$[L] B ) := ⟨_,to_fn⟩

theorem applyo_map {n} {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B] 
  (f : A →$[L] B) (t : L n) (as : ftuple A n) : applyo t (as.map f) = f (applyo t as) := by apply ralg_hom.applyo_map'
end ralg_hom


/-!
# Terms 
-/

namespace lang
universe v
inductive term (L : lang.{v}) : ℕ → Type v 
| of {n} : L n → term n
| proj {m n} : (fin n → fin m) → term n → term m
| compl {m n} : term m → term (1 + n) → term (m + n)
| compr {m n} : term m → term (n + 1) → term (n + m)

def gen (L : lang.{v}) : lang.{v} := ⟨L.term⟩

namespace gen

def applyt {n} {L : lang} {A : Type*} [has_app L A] (t : L.gen n) : ftuple A n → A :=
  lang.term.rec_on t 
  (λ _, applyo) 
  (λ _ _ f _ h as, h (as.proj f)) 
  (λ _ _ _ _ h1 h2 as, as.compl h1 h2) 
  (λ _ _ _ _ h1 h2 as, as.compr h1 h2) 

lemma applyt_map {n} {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B]
  (f : A →$[L] B) (t : L.gen n) (as : ftuple A n) : applyt t (as.map f) = f (applyt t as) := 
begin
  induction t with _ _ _ _ _ _ h _ _ t1 t2 h1 h2 _ _ t1 t2 h1 h2,
  { apply ralg_hom.applyo_map,},
  { apply h },
  { change applyt t2 (ftuple.append (ftuple.of $ applyt t1 _) _) = _,
    simp only [←ftuple.map_init, h1, ←ftuple.map_of, ←ftuple.map_last, ←ftuple.map_append, h2],
    refl },
  { change applyt t2 (ftuple.append _ (ftuple.of $ applyt t1 _)) = _, 
    simp only [←ftuple.map_init, h1, ←ftuple.map_of, ←ftuple.map_last, ←ftuple.map_append, h2],
    refl }
end

instance {L : lang} {A : Type*} [has_app L A] : has_app L.gen A := ⟨λ n, applyt⟩
    
instance {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B] : has_coe (A →$[L] B) (A →$[L.gen] B) := 
{ coe := λ f, ⟨f,λ _, by apply applyt_map⟩ }

end gen
end lang