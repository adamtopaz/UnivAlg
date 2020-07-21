import .ualg
import .lang

class compat {L1 : lang} {L2 : lang} (ι : L1 →# L2) (A : Type*) [has_app L2 A] extends has_app L1 A :=
(compat {n} {t : L1 n} {as : ftuple A n} : applyo t as = applyo (ι t) as)

namespace lang_hom

def forget_along {L1 : lang} {L2 : lang} (ι : L1 →# L2) (A : Type*) [has_app L2 A] : compat ι A :=
{ app := λ n t, applyo (ι t),
  compat := by tauto }

end lang_hom

namespace ralg_hom
variables {L0 : lang} {L1 : lang}
def drop {A : Type*} [has_app L1 A] {B : Type*} [has_app L1 B] (f : A →$[L1] B) (ι : L0 →# L1) 
  [compat ι A]  [compat ι B] : A →$[L0] B := 
{ to_fn := f,
  applyo_map' := 
  begin
    intros n t as,  
    simp_rw compat.compat,
    apply ralg_hom.applyo_map,
  end }

#check drop
end ralg_hom