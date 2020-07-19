import .lang

namespace ualg

variables {L : lang} (A : ralg L) (R : rules L)

namespace addr 
def rel : A → A → Prop := λ x y, ∀ (B : ualg L R) (f : A →% B), f x = f y 
def setoid : setoid A := ⟨rel A R,
begin
  refine ⟨_,_,_⟩,
  { intros x B g, refl },
  { intros x y h B g, symmetry, apply h },
  { intros x y z h1 h2 B g, rw [h1,h2] }
end⟩

def pre : ralg L :=
{ carrier := quotient (addr.setoid A R),
  appo := λ n t, @vector.quotient_lift _ (quotient (addr.setoid A R)) (addr.setoid A R) _ 
  (λ as, quotient.mk' $ applyo t as) 
  begin
    intros as bs h,  
    dsimp only [],
    apply quotient.sound',
    intros B g,
    simp_rw ←ralg.applyo_map,
    apply congr_arg,
    rw vector.eq_iff_to_fn_eq_to_fn,
    ext,
    simp_rw vector.map_to_fn,
    apply h,
  end }

def rquot : A →% (pre A R) := 
{ to_fn := quotient.mk',
  applyo_map := λ n t as, 
  begin
    change vector.quotient_lift _ _ (vector.map quotient.mk _) = _,  
    rw vector.quotient_lift_eq,
  end }

end addr

def addr : ualg L R := 
{ cond_eq := 
  begin
    intros m n t1 t2 as h,  
    rcases vector.exists_rep (@quotient.mk' _ (addr.setoid A R)) as (quot.exists_rep) with ⟨bs,rfl⟩,
    change applyt t1 (vector.map (addr.rquot A R) _) = _,
    change _ = applyt t2 (vector.map (addr.rquot A R) _),
    simp_rw [ralg.applyt_map,vector.eq_iff_to_fn_eq_to_fn,vector.map_to_fn],
    ext,
    change quotient.mk' ((applyt t1 bs) x) = quotient.mk' ((applyt t2 bs) x),
    apply quotient.sound',
    intros B g,
    suffices : (applyt t1 bs).map g = (applyt t2 bs).map g, 
    { rw vector.eq_iff_to_fn_eq_to_fn at this,
      simp_rw vector.map_to_fn at this,
      change (g ∘ (applyt t1 bs)) x = _, -- should also have a lemma to avoid this suffices
      rw this },
    simp_rw ←ralg.applyt_map,
    exact B.cond_eq h, -- the B.cond_eq should be made a lemma in lang.lean file
  end,
  ..addr.pre A R
  }

namespace addr
def univ : A →% (addr A R) := addr.rquot A R
variable {A}
def lift {B : ualg L R} (f : A →% B) : addr A R →% B :=
{ to_fn := @quotient.lift _ _ (addr.setoid A R) f (λ a b h, by {apply h}),
  applyo_map := λ n t as, 
  begin
    rcases vector.exists_rep (@quotient.mk' _ (addr.setoid A R)) as (quot.exists_rep) with ⟨bs,rfl⟩,
    have : @quotient.mk' _ (addr.setoid A R) = rquot A R, by refl,
    erw [this,ralg.applyo_map,quotient.lift_beta,vector.map_map],
    conv_rhs {rw ←ralg.applyo_map},
    apply congr_arg,
    rw vector.eq_iff_to_fn_eq_to_fn,
    ext,
    simp only [vector.map_to_fn,function.comp_apply],
    erw quotient.lift_beta,
  end }

theorem univ_comp_lift {B : ualg L R} (f : A →% B) :
  (univ A R).comp (lift R f) = f := 
begin
  ext,
  unfold ralgHom.comp,
  unfold_coes,
  dsimp only [],
  simp only [ralgHom.comp, function.comp_apply, function.comp_apply],
  erw quotient.lift_beta,
end

theorem lift_unique {B : ualg L R} (f : A →% B) (g : addr A R →% B) : 
  (univ A R).comp g = f → g = lift R f := λ hyp,
begin
  ext,
  replace hyp := congr_arg ralgHom.to_fn hyp,
  unfold ralgHom.comp at hyp,
  dsimp only [] at hyp,
  unfold univ at hyp,
  rcases quot.exists_rep x with ⟨x,rfl⟩,
  change (g ∘ (rquot A R)) _ = _,
  rw hyp,
  refl,
end

end addr

end ualg