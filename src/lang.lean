import data.vector
import .for_mathlib

--------------- lang ---------------
section 
universe v
structure lang := (op : ℕ → Type v)

namespace lang
instance : has_coe_to_fun lang := ⟨_,op⟩
end lang
end

--------------- ralg ---------------
section 
universes v u
structure ralg (L : lang.{v}) :=
(carrier : Type u)
(appo {n} : L n → vector carrier n → carrier)

namespace ralg
instance {L} : has_coe_to_sort (ralg L) := ⟨_,carrier⟩
end ralg
end

notation `applyo` := ralg.appo _

----------- terms -----------------
section 
universes v
namespace lang
inductive term (L : lang.{v}) : ℕ → ℕ → Type v
| of {n} : L n → term n 1
| proj {m n} : (fin m → fin n) → term n m
| comp {a b c} : term a b → term b c → term a c
| liftl {a b c} : term a b → term (a + c) (b + c)
| liftr {a b c} : term a b → term (c + a) (c + b)
end lang
end

def applyt {L : lang} {A : ralg L} {m n} (t : L.term m n) : vector A m → vector A n := lang.term.rec_on t 
  (λ _ t as, vector.of $ applyo t as) 
  (λ _ _, vector.proj) 
  (λ _ _ _ _ _ f g, g ∘ f) 
  (λ _ _ _ _, vector.liftl) 
  (λ _ _ _ _, vector.liftr)

------------------- rules -------------------------
structure rules (L : lang) := 
(cond {m n} : L.term m n → L.term m n → Prop)

namespace rules
instance {L} : has_coe_to_fun (rules L) := ⟨_,cond⟩
end rules

-----------------  ualg --------------------------
structure ualg (L : lang) (R : rules L) extends ralg L :=
(cond_eq {m n} {t1 t2 : L.term m n} {as : vector carrier m} : R t1 t2 → applyt t1 as = applyt t2 as)

namespace ualg
instance {L} {R} : has_coe_to_sort (ualg L R) := ⟨_,λ A, A.carrier⟩
end ualg

namespace ualg
def raw {L} {R} : ualg L R → ralg L := to_ralg
end ualg

------------------ langHom -----------------
structure langHom (L1 : lang) (L2 : lang) := (map_op {n} : L1 n → L2 n) 

infixr ` →# `:25 := langHom 

namespace langHom
instance {L1} {L2} : has_coe_to_fun (L1 →# L2) := ⟨_,map_op⟩
end langHom

namespace lang.term
variables {L1 : lang} {L2 : lang} (ι : L1 →# L2)
include ι
def mapt {m n} (t : L1.term m n) : L2.term m n := lang.term.rec_on t 
  (λ _ t, of $ ι t) 
  (λ _ _, proj) 
  (λ _ _ _ _ _, comp) 
  (λ _ _ _ _, liftl) 
  (λ _ _ _ _, liftr) 

end lang.term

------------------- rulesHom ------------------
structure rulesHom {L1 : lang} {L2 : lang} (R1 : rules L1) (R2 : rules L2) :=
(lhom : L1 →# L2)
(map_cond {m n} {t1 t2 : L1.term m n} : R1 t1 t2 → R2 (t1.mapt lhom) (t2.mapt lhom))

infixr ` →$ `:25 := rulesHom

-------------------- algHom's ------------------
structure ralgHom {L : lang} (A : ralg L) (B : ralg L) := 
(to_fn : A → B)
(applyo_map {n} {t : L n} {as : vector A n}: applyo t (as.map to_fn) = to_fn (applyo t as))
def ualgHom {L : lang} {R1 R2 : rules L} (A : ualg L R1) (B : ualg L R2) := ralgHom A.raw B.raw
def ralgualgHom {L : lang} {R : rules L} (A : ralg L) (B : ualg L R) := ralgHom A B.raw
def ualgralgHom {L : lang} {R : rules L} (A : ualg L R) (B : ralg L) := ralgHom A.raw B

namespace ralgHom
instance {L} {A : ralg L} {B : ralg L} : has_coe_to_fun (ralgHom A B) := ⟨_,to_fn⟩
end ralgHom
namespace ualgHom
instance {L} {R1 R2 : rules L} {A : ualg L R1} {B : ualg L R2} : has_coe_to_fun (ualgHom A B) := ⟨_,λ f, f.to_fn⟩
end ualgHom
namespace ralgualgHom
instance {L} {R : rules L} {A : ralg L} {B : ualg L R} : has_coe_to_fun (ralgualgHom A B) := ⟨_,λ f, f.to_fn⟩
end ralgualgHom
namespace ualgralgHom
instance {L} {R : rules L} {A : ualg L R} {B : ralg L} : has_coe_to_fun (ualgralgHom A B) := ⟨_,λ f, f.to_fn⟩
end ualgralgHom


infixr ` →% `:25 := ralgHom
infixr ` →% `:25 := ualgHom
infixr ` →% `:25 := ralgualgHom
infixr ` →% `:25 := ualgralgHom

---------------- theorems abouts homs -----------

namespace ralgHom
variables {L : lang} {A : ralg L} {B : ralg L}
@[ext]
theorem ext (f g : A →% B) : ⇑f = g → f = g := λ hyp, by {cases f, cases g, simpa}
end ralgHom

namespace ralg

variables {L : lang} {A : ralg L} {B : ralg L}


/-
A ralg hom commutes with applyo.
-/
theorem applyo_map {n} (f : A →% B) (t : L n) (as : vector A n) : 
  applyo t (as.map f) = f (applyo t as) := by apply ralgHom.applyo_map

/-
A ralg hom commutes with applyt.
-/
theorem applyt_map {m n} (f : A →% B) (t : L.term m n) (as : vector A m) :
  applyt t (as.map f) = (applyt t as).map f := 
begin
  induction t with _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ _ _ h3 _ _ _ _ h4, 
  { change vector.of _ = _,
    rw [applyo_map, ←vector.map_of],
    refl },
  { change vector.proj _ _ = vector.map _ (vector.proj _ _),
    rw vector.map_proj },
  { change (applyt _ (applyt _ _)) = _,
    rw [h1,h2], refl },
  { change _ = vector.map f (vector.append (applyt _ _) _),
    rw vector.map_append,
    rw ←h3,
    change vector.append (applyt _ _) _ = _,
    congr,
    { rw vector.map_init },
    { rw vector.map_last } },
  { change _ = vector.map f (vector.append _ (applyt _ _)),
    rw vector.map_append,
    rw ←h4,
    change vector.append _ (applyt _ _) = _,
    congr,
    { rw vector.map_init },
    { rw vector.map_last } },
end

end ralg

--------------------- composition -------------------------

namespace ralgHom
variables {L : lang} {A : ralg L} {B : ralg L} {C : ralg L}
def comp : (A →% B) → (B →% C) → (A →% C) := λ f g, 
{ to_fn := g ∘ f,
  applyo_map := λ n t as, by rw ←vector.map_map; simp only [ralg.applyo_map] }

end ralgHom



-------------------- forget_along -----------------------
/-
Here we construct some forgetful functors.
-/

namespace ralg
variables {L0 : lang} {L : lang} (ι : L0 →# L) (A : ralg L)
include ι A
def forget_along : ralg L0 := 
{ carrier := A,
  appo := λ n t, applyo (ι t) }

end ralg

notation A `{`:1000 ι `}`:1000 := ralg.forget_along ι A

namespace ralg
variables {L0 : lang} {L : lang} (ι : L0 →# L)
def cast {A : ralg L} : A → A{ι} := id 
def uncast {A : ralg L} : A{ι} → A := id
include ι

theorem applyt_mapt {m n} {A : ralg L} (t : L0.term m n) (as : vector (A{ι}) m):
  applyt t as = vector.map (cast ι) (applyt (t.mapt ι) (as.map (uncast ι))) := 
begin
  simp only [cast, uncast, vector.map_id],
  induction t with _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ _ _ h3 _ _ _ _ h4,  
  { refl },
  { refl },
  { change applyt _ (applyt _ _) = _,
    rw [h1,h2], 
    refl },
  { change vector.append (applyt _ _) _ = _, 
    rw h3, 
    refl },
  { change vector.append _ (applyt _ _) = _,
    rw h4, 
    refl },
end

end ralg

namespace ualg
variables {L0 : lang} {L : lang} {R0 : rules L0} {R : rules L} 
variables (ι : R0 →$ R) (A : ualg _ R)
include ι A
def forget_along : ualg _ R0  :=
{ cond_eq := λ m n t1 t2 as h, 
  begin
    rw ralg.applyt_mapt,
    rw ralg.applyt_mapt,
    apply congr_arg,
    apply A.cond_eq,
    apply ι.map_cond,
    assumption,
  end,
  ..show ralg L0, by exact A.raw{ι.lhom} }
end ualg

notation A `⦃`:1000 ι `⦄`:1000 := ualg.forget_along ι A

example {L0 : lang} {L : lang} {R0 : rules L0} {R : rules L} 
  (ι : R0 →$ R) (A : ualg _ R) : A⦃ι⦄.raw = A.raw{ι.lhom} := rfl


----------------- forget_along for morphisms ----------------------

namespace ralgHom 

variables {L0 : lang} {L1 : lang} (ι : L0 →# L1)
variables {A : ralg L1} {B : ralg L1} 

def forget_along (f : A →% B) : A{ι} →% B{ι} := 
{ to_fn := f,
  applyo_map := λ n t as, by {erw ralg.applyo_map, refl} }

end ralgHom

notation A `{%`:1000 ι `}`:1000 := ralgHom.forget_along ι A
