import .lang

namespace ralg
universes v u

variables (L : lang.{v}) (S : Type u)

namespace free

inductive tp : Type (max v u)
| of : S → tp
| op {n} : L n → (fin n → tp) → tp

end free

def free : ralg L := 
{ carrier := free.tp L S,
  appo := λ _ t as, free.tp.op t as }

namespace free

def univ : S → free L S := tp.of

variables (L) {S}
def lift {B : ralg L} (f : S → B) : (free L S) →% B := 
{ to_fn := λ t, tp.rec_on t f 
    (λ _ t _ bs, applyo t $ vector.of_fn bs),
  applyo_map := λ n t as, 
  begin
    have : as = vector.of_fn as, by rw vector.of_fn_to_fn,
    conv_lhs {rw this},
    rw vector.map_of_fn,
    refl,
  end }

theorem univ_comp_lift {B : ralg L} (f : S → B) : (lift _ f) ∘ (univ L S) = f := rfl

theorem lift_unique {B : ralg L} (f : S → B) (g : (free L S) →% B) :
  g ∘ (univ _ _) = f → g = lift _ f := λ hyp,
begin
  ext,
  induction x with _ n t as h,
  { change (g ∘ (univ _ _)) x = _,
    rw hyp, refl },
  { have : as = vector.of_fn as, 
    { change _ = vector.to_fn _,
      rw vector.to_fn_of_fn },
    dsimp only [] at h,
    rw this,
    change g.to_fn (applyo _ _) = (lift _ f).to_fn (applyo _ _),
    simp_rw ←ralgHom.applyo_map,
    apply congr_arg,
    simp only [vector.map_of_fn],
    rw vector.eq_iff_to_fn_eq_to_fn,
    funext,
    change vector.to_fn _ _ = vector.to_fn _ _,
    simp only [vector.to_fn_of_fn], apply h }
end

end free

end ralg