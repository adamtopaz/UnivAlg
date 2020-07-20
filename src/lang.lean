import .ftuple

/-! 
# Languages and raw algebras.
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