import tactic
import data.vector
import data.nat.basic
--import category_theory.types

--------------------- Vector Stuff ----------------------
namespace vector
variables {A : Type*} {B : Type*} {C : Type*}

def of : A → vector A 1 := λ a, ⟨[a],rfl⟩
def of₂ : A → A → vector A 2 := λ a b, ⟨[a,b],rfl⟩
def of₃ : A → A → A → vector A 3 := λ a b c, ⟨[a,b,c],rfl⟩
def to_fn {n} : vector A n →  (fin n → A) := λ as, as.nth
def proj {m n} : (fin m → fin n) → vector A n → vector A m :=
  λ f as, of_fn (λ i, as.to_fn $ f i)
def cast {m n : ℕ} : m = n → vector A m → vector A n := λ h, eq.rec_on h 
def init {m n : ℕ} : vector A (m+n) → vector A m := λ as, cast (by simp) (take m as)
def last {m n : ℕ} : vector A (m+n) → vector A n := λ as, cast (by simp) (drop m as)
def liftl {a b c : ℕ} : (vector A a → vector A b) → vector A (a + c) → vector A (b + c) := 
  λ f as, append (f as.init) as.last
def liftr {a b c : ℕ} : (vector A a → vector A b) → vector A (c + a) → vector A (c + b) := 
  λ f as, append as.init (f as.last)
def curry {n} : (vector A (n+1) → B) → (A → (vector A n → B)) := 
  λ f a as, f $ a :: as
def uncurry {n} : (A → (vector A n → B)) → (vector A (n+1) → B) := 
  λ f as, f as.head as.tail

-- Any vector can be considered as a function
instance {n} : has_coe_to_fun (vector A n) := ⟨_,λ as, as.to_fn⟩

-- lemmas around the "of" things
theorem of_0th (a : A) : (of a) 0 = a := rfl

theorem of_eq_iff (a b : A) : of a = of b ↔ a = b := 
begin
  refine ⟨λ h, _,λ h, by rw h⟩,
  rw [←of_0th a, ←of_0th b, h],
end

-- Some other useful lemmas
theorem one_eq_of (as : vector A 1) : as = of (as 0) := 
begin
  rcases as with ⟨as,h⟩,
  induction as,
  { contradiction, },
  { congr, simp only [list.length] at h,
    have : as_tl.length = 0, by exact nat.succ.inj h,
    exact list.eq_nil_of_length_eq_zero this }
end

theorem one_eq_iff (as bs : vector A 1) : as = bs ↔ as 0 = bs 0 := 
begin
  rw one_eq_of as, rw one_eq_of bs,
  unfold of,
  finish,
end

-- Map lemmas
theorem map_of (f : A → B) (a : A) : (of a).map f = of (f a) := sorry
theorem map_to_fn {m} (f : A → B) (as : vector A m) : ⇑(as.map f) = f ∘ as := sorry
theorem map_of_fn {m} (f : A → B) (as : fin m → A) : (of_fn as).map f = of_fn (f ∘ as) := sorry
theorem map_ith {m} (f : A → B) (as : vector A m) (i : fin m) : (as.map f) i = f (as i) := sorry
theorem map_proj {m n} (f : A → B) (g : fin m → fin n) (as : vector A n) :
  (as.map f).proj g = (as.proj g).map f := sorry
theorem map_init {m n} (f : A → B) (as : vector A (m+n)) :
  as.init.map f = (as.map f).init := sorry
theorem map_last {m n} (f : A → B) (as : vector A (m+n)) :
  as.last.map f = (as.map f).last := sorry
theorem map_append {m n} (f : A → B) (as : vector A m) (bs : vector A n) :
  (as.append bs).map f = (as.map f).append (bs.map f) := sorry
theorem to_fn_zero_eq_head {n} (a : A) (as : vector A n) : (a :: as) 0 = a := sorry

theorem map_map {n} (f : A → B) (g : B → C) (as : vector A n) :
  (as.map f).map g = as.map (g ∘ f) := by {cases as, unfold map, finish}

@[simp]
theorem map_id {n} (as : vector A n) : as.map id = as := 
  by {cases as, unfold map, finish}

@[simp]
theorem map_id' {n} (as : vector A n) : as.map (λ x, x) = as := by apply map_id

theorem map_to_fn_eq {n} {f g : A → B} {as : vector A n} : 
  (∀ i, f (as i) = g (as i)) → as.map f = as.map g := sorry

theorem exists_rep {n} (f : A → B) (bs : vector B n) : 
  function.surjective f → (∃ as : vector A n, as.map f = bs) := sorry

-- of/to_fn lemmas
theorem of_fn_to_fn {m} (as : vector A m) : vector.of_fn as = as := sorry
theorem to_fn_of_fn {m} (as : fin m → A) : (vector.of_fn as).to_fn = as := sorry
theorem eq_iff_to_fn_eq_to_fn {m} (as bs : vector A m) : as = bs ↔ ⇑as = bs := sorry

-- Stuff involving quotients and a setoid
section quotient_stuff
variable [S : setoid A]
include S

theorem rel_head {n} (a b : A) (as : vector A n) : 
  (∀ i, ((a :: as) i) ≈ ((b :: as) i)) ↔ a ≈ b := 
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { specialize h 0, repeat{rw to_fn_zero_eq_head at h}, assumption },
  { by_cases i = 0, 
    { simpa only [h, to_fn_zero_eq_head], },
    { sorry, } }
end

theorem rel_tail {n} (a : A) (as bs : vector A n) : 
  (∀ i, ((a :: as) i) ≈ ((a :: bs) i)) ↔ (∀ i, (as i) ≈ (bs i)) := sorry

def quotient_lift : Π {n} (f : vector A n → B),
  (∀ as bs : vector A n, (∀ i, as i ≈ bs i) → f as = f bs) → vector (quotient S) n → B := λ n,
  nat.rec_on n
  (λ f h _, f nil) $ 
  λ m ind f h, uncurry $ 
  λ x, quotient.lift_on x 
  (λ a, ind (curry f a) 
  begin
    intros as bs cond, 
    change f _ = f _,
    apply h,
    rw rel_tail,
    assumption,
  end)
  begin
    intros a b cond, 
    dsimp only [],
    suffices : curry f a = curry f b, by simp_rw this,
    funext,
    change f _ = f _,
    apply h,
    rw rel_head,
    assumption,
  end

theorem quotient_lift_eq : Π {n} (f : vector A n → B)
  (h : ∀ as bs : vector A n, (∀ i, as i ≈ bs i) → f as = f bs) (as : vector A n),  
  quotient_lift f h (as.map quotient.mk) = f as := sorry

end quotient_stuff

end vector


namespace function

theorem epi_of_surj {X Y Z : Type*} (f : X → Y) (g1 g2 : Y → Z) : 
  surjective f → g1 ∘ f = g2 ∘ f → g1 = g2 := sorry

end function