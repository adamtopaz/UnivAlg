import .lang
import .forget
import .free_ralg
import .fron_ralg
import .add_rules
import .ualg

namespace rules_hom

variables {L0 : lang} {R0 : rules L0} {L1 : lang} {R1 : rules L1} 
variables (ι : R0 →# R1)
variables (A : Type*) [ualg R0 A]

include ι
def fron := R1.add (ι.lhom.fron A)

namespace fron

instance : has_app L1 (ι.fron A) := rules.add.has_app R1 _
instance : compat ι.lhom (ι.fron A) := ι.lhom.forget_along _

def univ : A →$[L0] (ι.fron A) := 
  (lang_hom.fron.univ ι.lhom A).comp 
  ((rules.add.univ R1 (ι.lhom.fron A)).drop ι.lhom)

variable {A}
def lift {B : Type*} [ualg R1 B] [compat ι.lhom B] (f : A →$[L0] B) :
  ι.fron A →$[L1] B := 
    rules.add.lift R1 $ 
    lang_hom.fron.lift _ f

theorem univ_comp_lift {B : Type*} [ualg R1 B] [compat ι.lhom B] (f : A →$[L0] B) :
  (univ ι A).comp ((lift ι f).drop ι.lhom) = f := by {ext, refl}

theorem lift_unique {B : Type*} [ualg R1 B] [compat ι.lhom B] (f : A →$[L0] B)
  (g : ι.fron A →$[L1] B) : (univ ι A).comp (g.drop ι.lhom) = f → g = lift ι f := 
begin
  intro hyp,
  apply rules.add.lift_unique,
  apply lang_hom.fron.lift_unique,
  assumption,
end

end fron

end rules_hom