import .ualg
import .lang

class compat {L1 : lang} {L2 : lang} (ι : L1 →# L2) (A : Type*) [has_app L2 A] extends has_app L1 A :=
(compat {n} {t : L1 n} {as : ftuple A n} : applyo t as = applyo (ι t) as)

namespace lang_hom

def forget_along {L1 : lang} {L2 : lang} (ι : L1 →# L2) (A : Type*) [has_app L2 A] : compat ι A :=
{ app := λ n t, applyo (ι t),
  compat := by tauto }

end lang_hom