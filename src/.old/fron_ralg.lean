import .free_ralg

namespace ralg

variables {L0 : lang} {L : lang} (ι : L0 →# L)
variables (A : ralg L0)

namespace fron

def rel : (free L A) → (free L A) → Prop := λ x y, 
  ∀ (B : ralg L) (g : A →% B{ι}), (free.lift L g) x = (free.lift L g) y

def setoid : setoid (free L A) := ⟨rel ι A,
begin
  refine ⟨_,_,_⟩,
  { intros x B g, refl },
  { intros x y h B g, symmetry, apply h },
  { intros x y z h1 h2 B g, rw [h1,h2] }
end ⟩

end fron

def fron : ralg L := 
{ carrier := quotient (fron.setoid ι A),
  appo := λ n t, @vector.quotient_lift _ (quotient (fron.setoid ι A)) (fron.setoid ι A) 
    _ (λ as, quotient.mk' (applyo t as)) 
    begin
      intros as bs h, 
      dsimp only [],
      apply quotient.sound',
      intros B g,
      simp_rw ←ralg.applyo_map,
      apply congr_arg,
      simp_rw [vector.eq_iff_to_fn_eq_to_fn,vector.map_to_fn],
      ext,
      apply h,
    end }

namespace fron

def fquot : (free L A) →% (fron ι A) := 
{ to_fn := quotient.mk',
  applyo_map := λ n t as, 
  begin
    change vector.quotient_lift _ _ (vector.map quotient.mk _) = _, 
    rw vector.quotient_lift_eq,
  end }

def univ : A →% (fron ι A){ι} := 
{ to_fn := (fquot ι A) ∘ (free.univ L A),
  applyo_map := λ n t as, 
  begin
    rw ←vector.map_map, 
    change applyo (ι t) (vector.map (fquot _ _) _)  = (fquot ι A) _,
    rw ralg.applyo_map,
    apply quotient.sound',
    intros B g, 
    change _ = ((free.lift _ _) ∘ (free.univ _ _)) _,
    rw [←ralg.applyo_map,vector.map_map,free.univ_comp_lift],
    change applyo _ (vector.map ((free.lift _ _) ∘ (free.univ _ _)) _) = _,
    rw [free.univ_comp_lift,←ralg.applyo_map],
    refl,
  end }

variable {A}
def lift {B : ralg L} (f : A →% B{ι}) : fron ι A →% B := 
{ to_fn := @quotient.lift _ _ (fron.setoid ι A) (free.lift L f) 
  begin
    intros a b h,  
    apply h,
  end,
  applyo_map := λ n t as, 
  begin
    rcases vector.exists_rep quotient.mk' as (quot.exists_rep) with ⟨as,rfl⟩,
    rw vector.map_map,
    have : @quotient.mk' _ (fron.setoid ι A) = (fquot ι A), by refl,
    rw this,
    erw ralg.applyo_map,
    erw ralg.applyo_map,
    change _ = quotient.lift _ _ (quotient.mk _),
    rw quotient.lift_beta,
  end }

theorem univ_comp_lift {B : ralg L} (f : A →% B{ι}) : 
  (univ ι A).comp ((lift ι f){%ι}) = f := 
begin
  ext,
  change (lift ι f) (quotient.mk' ((free.univ _ _) _)) = _,
  unfold_coes,
  dsimp only [],
  erw quotient.lift_beta,
  refl,
end

theorem lift_unique {B : ralg L} (f : A →% B{ι}) (g : fron ι A →% B) :
  (univ ι A).comp (g{%ι}) = f → g = lift ι f := λ hyp,
begin
  ext,
  rcases quot.exists_rep x with ⟨x,rfl⟩,
  unfold_coes,
  dsimp only [],
  erw quotient.lift_beta,
  change _ = (free.lift _ _) x,
  change (g ∘ (fquot _ _)) _ = _,
  apply congr_fun,
  suffices : (fquot ι A).comp g = free.lift L f, 
  { replace this := congr_arg  (ralgHom.to_fn) this,
    assumption },
  apply free.lift_unique,
  ext y,
  change ((univ ι A).comp (g{%ι})) y = _,
  rw hyp,
end

end fron

end ralg