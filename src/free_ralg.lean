import .lang
import .ualg

namespace lang

universes v u
variables (L : lang.{v}) (S : Type u)

inductive free : Type (max v u)
| of : S → free
| op {n} : L n → (fin n → free) → free

namespace free
instance : has_app L (L.free S) :=  
{ app := λ _, op }

def univ : S → L.free S := of

variable {S} 
def lift {B : Type*} [has_app L B] (f : S → B) : L.free S →$[L] B := 
{ to_fn := λ t, free.rec_on t f (λ n t as bs, applyo t bs),
  applyo_map' := by tauto }

theorem univ_comp_lift {B : Type*} [has_app L B] (f : S → B) : (lift L f) ∘ (univ L S) = f := rfl

theorem lift_unique {B : Type*} [has_app L B] (f : S → B) (g : L.free S →$[L] B) (hyp : g ∘ (univ L S) = f) : g = lift L f := 
begin
  apply ralg_hom.ext,
  ext,
  induction x with _ _ t as ind, 
  { change (g ∘ (univ _ _)) x = _,
    rw hyp, refl },
  { change g (applyo t as) = (lift L f) (applyo t as),
    simp_rw ←ralg_hom.applyo_map,
    apply congr_arg,
    ext,
    apply ind }
end

end free

end lang