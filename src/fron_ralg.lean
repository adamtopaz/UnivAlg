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
inductive rel : (L1.free A) → (L1.free A) → Prop
| of {n} (as : ftuple A n) (t : L0 n) :
    rel (applyo (ι t) (as.map (free.univ L1 A))) (free.univ L1 A (applyo t as))
| refl (a) : rel a a
| symm (a b) : rel a b → rel b a
| trans (a b c) : rel a b → rel b c → rel a c
| compat {n} {t : L1 n} {as bs : ftuple (L1.free A) n} : 
    (∀ i, rel (as i) (bs i)) → rel (applyo t as) (applyo t bs)

/-
λ a b, 
  ∀ (B : Type*) (h1 : has_app L1 B), 
  by letI := h1; exact ∀ (h2 : compat ι B),  
  by letI := h2; exact ∀ (g : A →$[L0] B), (free.lift L1 g) a = (free.lift L1 g) b
-/

def setoid : setoid (L1.free A) := ⟨rel ι A, rel.refl, rel.symm, rel.trans⟩
end fron

def fron := quotient (fron.setoid ι A)

namespace fron

instance : has_app L1 (ι.fron A) := 
{ app := λ n t, by letI := fron.setoid ι A; exact ftuple.quotient_lift 
  (λ as, ⟦applyo t as⟧)
  (λ as bs hyp, quotient.sound $ rel.compat hyp) }

instance : compat ι (ι.fron A) := ι.forget_along (ι.fron A)

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
    apply rel.of,
  end }

variable {A}
def lift {B : Type*} [has_app L1 B] [compat ι B] (f : A →$[L0] B) :
  ι.fron A →$[L1] B := 
{ to_fn := by letI := fron.setoid ι A; exact quotient.lift (lang.free.lift L1 f) 
  begin
    intros a b h, 
    induction h,
    {sorry,},
    repeat {cc,},
    { dsimp only [] at h_ih,
      simp_rw ←ralg_hom.applyo_map,
      apply congr_arg,
      ext,
      apply h_ih},
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

theorem univ_comp_lift {B : Type*} [has_app L1 B] [compat ι B] (f : A →$[L0] B) : 
  (univ ι A).comp ((lift ι f).drop ι) = f :=
  by {ext, refl}

open lang
theorem lift_unique {B : Type*} [has_app L1 B] [compat ι B] (f : A →$[L0] B)
  (g : ι.fron A →$[L1] B) : (univ ι A).comp (g.drop ι) = f → g = lift ι f := 
begin
  intro hyp,
  ext,
  letI := fron.setoid ι A,
  have : ∃ y : L1.free A, (quot ι A) y = x, by apply quotient.exists_rep,
  rcases this with ⟨y,rfl⟩,
  change _ = free.lift _ _ y,
  induction y with _ n t as ind,
  { change _ = f y,
    rw ←hyp,
    refl },
  { change _ = (free.lift L1 f) (applyo t as),
    change g ( (quot ι A) (applyo t as)) = _,
    simp_rw ←ralg_hom.applyo_map,
    apply congr_arg,
    ext,
    apply ind }
end

end fron

end lang_hom