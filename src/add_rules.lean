import .lang
import .ualg

namespace rules

variables {L : lang} (R : rules L)
variables (A : Type*) [has_app L A]

namespace add
def rel : A → A → Prop := λ a b, ∀ (B : Type*) (h : ualg R B), 
  by letI := h; exact ∀ (g : A →$[L] B), g a = g b

def setoid : setoid A := ⟨rel R A,
begin
  refine ⟨_,_,_⟩,
  { intros x B _ _ g, refl },
  { intros x y h B _ _ g, symmetry, apply h },
  { intros x y z h1 h2 B _ _ g, rw [h1,h2] },
end⟩
end add

def add := quotient (add.setoid R A)

namespace add
instance : has_app L (R.add A) := 
{ app := λ n t, by letI := add.setoid R A; exact ftuple.quotient_lift 
  (λ as, ⟦applyo t as⟧) 
  (begin
    intros as bs hyp, 
    apply quotient.sound,
    intros B _ _ g, 
    simp_rw ←ralg_hom.applyo_map,
    apply congr_arg,
    ext,
    apply hyp
  end) }

def univ : A →$[L] (R.add A) := 
{ to_fn := by letI := add.setoid R A; exact λ a, ⟦a⟧,
  applyo_map' := 
  begin
    letI := add.setoid R A,
    intros n t as, 
    dsimp only [],
    change ftuple.quotient_lift _ _ _ = _,
    rw ftuple.quotient_lift_beta,
  end }

instance : ualg R (R.add A) := 
{ cond_eq := 
  begin
    intros n t1 t2 as hyp, 
    letI := add.setoid R A,
    rcases ftuple.exists_rep as (quotient.exists_rep) with ⟨as,rfl⟩,
    have : as.map (λ a, ⟦a⟧) = as.map (univ R A), by refl,
    simp_rw this, clear this,
    simp_rw ralg_hom.applyt_map,
    apply quotient.sound,
    intros B _ _ g,
    simp_rw ←ralg_hom.applyt_map,
    apply ualg.cond_eq,
    apply hyp,
  end }

variable {A}
def lift {B : Type*} [ualg R B] (f : A →$[L] B) : R.add A →$[L] B := 
{ to_fn := by letI := add.setoid R A; exact quotient.lift f 
  begin
    intros a b h, 
    apply h,
  end,
  applyo_map' := 
  begin
    intros n t as, 
    letI := add.setoid R A,
    rcases ftuple.exists_rep as (quotient.exists_rep) with ⟨as,rfl⟩,
    change _ = quotient.lift f _ (applyo _ (as.map (univ R A))),
    rw ralg_hom.applyo_map,
    change _ = quotient.lift f _ (quotient.mk _),
    rw quotient.lift_beta,
    rw ←ralg_hom.applyo_map,
    apply congr_arg,
    ext,
    simp only [ftuple.map_eval, quotient.lift_beta],
  end }

theorem univ_comp_lift {B : Type*} [ualg R B] (f : A →$[L] B) :
  (univ R A).comp (lift R f) = f := by {ext, refl}

theorem lift_unique {B : Type*} [ualg R B] (f : A →$[L] B) (g : (R.add A) →$[L] B) :
  (univ R A).comp g = f → g = lift R f := λ hyp,
begin
  ext,
  rcases quot.exists_rep x with ⟨x,rfl⟩,
  letI := add.setoid R A,
  change g ⟦x⟧ = ((univ R A).comp (lift R f)) x,
  rw univ_comp_lift,
  rw ←hyp,
  refl,
end

end add

end rules