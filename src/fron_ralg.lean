import .lang
import .forget
import .free_ralg
import .ualg

namespace lang_hom

variables {L0 : lang} {L1 : lang} (ι : L0 →# L1)
variables (A : Type*) [has_app L0 A]

-- goal is to construct the free has_app L1
-- compatible with the has_app L0 

namespace fron -- ι.fron A
open lang
include ι
def rel : (L1.free A) → (L1.free A) → Prop := λ a b, 
  ∀ (B : Type*) (h1 : has_app L1 B), 
  by letI := h1; exact ∀ (h2 : compat ι B),  
  by letI := h2; exact ∀ (g : A →$[L0] B), (free.lift L1 g) a = (free.lift L1 g) b

def setoid : setoid (L1.free A) := ⟨rel ι A,
begin
  refine ⟨_,_,_⟩,
  { intros x B _ _ _ _ g, refl },
  { intros x y h B _ _ _ _ g, symmetry, apply h },
  { intros x y z h1 h2 B _ _ _ _ g, rw [h1,h2] },
end⟩
end fron

def fron := quotient (fron.setoid ι A)

namespace fron

instance : has_app L1 (ι.fron A) := 
{ app := λ n t, by letI := fron.setoid ι A; exact ftuple.quotient_lift 
  (λ as, ⟦applyo t as⟧) 
  begin
    intros as bs hyp, 
    apply quotient.sound,
    intros B _ _ _ _ g,
    simp_rw ←ralg_hom.applyo_map,
    apply congr_arg,
    ext,
    apply hyp,
  end }

private def compat_instance := ι.forget_along (ι.fron A)
local attribute [instance] compat_instance

def quot : L1.free A →$[L1] (ι.fron A) := 
{ to_fn := by letI := fron.setoid ι A; exact λ a, ⟦a⟧,
  applyo_map' := 
  begin
    intros n t as,  
    dsimp only [],
    letI := fron.setoid ι A,
    change ftuple.quotient_lift _ _ _ = _,
    rw ftuple.quotient_lift_beta,
  end }

def univ : A →$[L0] (ι.fron A) := 
{ to_fn := by letI := fron.setoid ι A; exact λ a, ⟦lang.free.univ L1 A a⟧,
  applyo_map' := 
  begin
    intros n t as,
    letI := fron.setoid ι A,
    dsimp only [],
    change applyo t ((as.map (lang.free.univ L1 A)).map (quot ι A)) = _,    
    simp_rw compat.compat,
    rw ralg_hom.applyo_map,
    apply quotient.sound,
    intros B _ _ _ _ g,
    simp_rw ←ralg_hom.applyo_map,
    letI := h1,
    change _ = ((lang.free.lift L1 g) ∘ (lang.free.univ L1 A)) _,
    rw ←ftuple.map_map,
    simp_rw lang.free.univ_comp_lift,
    rw [←ralg_hom.applyo_map,compat.compat],
  end }

variable {A}
def lift {B : Type*} [has_app L1 B] [compat ι B] (f : A →$[L0] B) :
  ι.fron A →$[L1] B := 
{ to_fn := by letI := fron.setoid ι A; exact quotient.lift (lang.free.lift L1 f) 
  begin
    intros a b h, 
    apply h,
  end,
  applyo_map' := 
  begin
    intros n t as, 
    letI := fron.setoid ι A,
    dsimp only [],
    change _ = quotient.lift _ _ _,
    rcases ftuple.exists_rep as quotient.exists_rep with ⟨as,rfl⟩,
    change _ = quotient.lift _ _ (applyo  _ (as.map (quot ι A))),
    simp_rw ralg_hom.applyo_map,
    erw quotient.lift_beta,
    simp_rw ←ralg_hom.applyo_map,
    apply congr_arg,
    ext,
    simp only [ftuple.map_eval,quotient.lift_beta],
  end }

end fron

end lang_hom