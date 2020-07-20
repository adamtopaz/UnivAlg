import .add_rules
import .fron_ralg

namespace ualg

variables {L0 : lang} {R0 : rules L0}
variables {L : lang} {R : rules L}
variables (ι : R0 →$ R) (A : ualg L0 R0)

include ι A
def fron : ualg L R := addr (ralg.fron ι.lhom A.raw) R

namespace fron
def univ : A →% (fron ι A)⦃ι⦄ := 
  (ralg.fron.univ ι.lhom A.raw).comp ((ualg.addr.univ (ralg.fron ι.lhom A.raw) R){%ι.lhom})
variable {A}
def lift {B : ualg L R} (f : A →% B⦃ι⦄) : (fron ι A) →% B := ualg.addr.lift R (ralg.fron.lift ι.lhom f)

theorem univ_comp_lift {B : ualg L R} (f : A →% B⦃ι⦄) : (univ ι A).comp ((lift ι f){%ι.lhom}) = f := 
  by apply ralg.fron.univ_comp_lift

theorem lift_unique {B : ualg L R} (f : A →% B⦃ι⦄) (g : (fron ι A) →% B) : 
  (univ ι A).comp (g{%ι.lhom}) = f → g = lift ι f := 
begin
  intro hyp,
  apply ualg.addr.lift_unique,
  apply ralg.fron.lift_unique,
  assumption,
end

end fron
end ualg