import .lang

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

def comp {L : lang} {A : Type*} {B : Type*} {C : Type*} [has_app L A] [has_app L B] [has_app L C] : 
  (A →$[L] B) → (B →$[L] C) → (A →$[L] C) := λ f g, 
{ to_fn := g ∘ f,
  applyo_map' :=
  begin
    intros n t as, 
    change _ = g _,
    simp_rw ←applyo_map, 
    refl,
  end }

@[ext]
theorem ext {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B] (f g : A →$[L] B) : ⇑f = g → f = g := 
  by {cases f, cases g, finish}

theorem comp_assoc {L : lang} {A : Type*} {B : Type*} {C : Type*} {D : Type*} 
  [has_app L A] [has_app L B] [has_app L C] [has_app L D]
  (f : A →$[L] B) (g : B →$[L] C) (h : C →$[L] D) : (f.comp g).comp h = f.comp (g.comp h) := by {apply ext, refl}
end ralg_hom

def applyt {n} {L : lang} {A : Type*} [has_app L A] (t : L.gen n) : ftuple A n → A :=
  lang.term.rec_on t 
  (λ _, applyo) 
  (λ _ _ f _ h as, h (as.proj f)) 
  (λ _ _ _ _ h1 h2 as, as.compl h1 h2) 
  (λ _ _ _ _ h1 h2 as, as.compr h1 h2) 

namespace ralg_hom
lemma applyt_map {n} {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B]
  (f : A →$[L] B) (t : L.gen n) (as : ftuple A n) : applyt t (as.map f) = f (applyt t as) := 
begin
  induction t with _ _ _ _ _ _ h _ _ t1 t2 h1 h2 _ _ t1 t2 h1 h2,
  { apply ralg_hom.applyo_map,},
  { apply h },
  repeat { change applyt t2 (ftuple.append (ftuple.of $ applyt t1 _) _) = _ <|>
    change applyt t2 (ftuple.append _ (ftuple.of $ applyt t1 _)) = _, 
    simp only [←ftuple.map_init, h1, ←ftuple.map_of, ←ftuple.map_last, ←ftuple.map_append, h2],
    refl },
end
end ralg_hom

--instance {L : lang} {A : Type*} [has_app L A] : has_app L.gen A := ⟨λ n, applyt⟩

/-
namespace ralg_hom
def gen {L : lang} {A : Type*} {B : Type*} [has_app L A] [has_app L B] (f : A →$[L] B) : A →$[L.gen] B := 
  ⟨f,λ _, by apply gen.applyt_map⟩ 
end ralg_hom
-/

class ualg {L : lang} (R : rules L) (A : Type*) extends has_app L A :=
(cond_eq {n} (t1 t2 : L.gen n) (as : ftuple A n) : R t1 t2 → applyt t1 as = applyt t2 as)

/-
namespace vac
instance {L} {A : Type*} [has_app L A] : ualg L.vac A := 
{ cond_eq := by tauto, 
  ..show has_app L A, by apply_instance } 
end vac
-/