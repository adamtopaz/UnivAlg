import data.equiv.fin
import data.fin

namespace fin
variable {α : Type*}

def breakl {m n : ℕ} (as : fin (m + n) → α) : fin m → α := λ i, as (sum_fin_sum_equiv $ sum.inl i)
def breakr {m n : ℕ} (as : fin (m + n) → α) : fin n → α := λ i, as (sum_fin_sum_equiv $ sum.inr i)
def compl {m n : ℕ} (as : fin (m + n) → α) (f : (fin m → α) → α) (g : (fin n.succ → α) → α) : α := 
  g $ fin.cons (f $ breakl as) (breakr as)
def compr {m n : ℕ} (as : fin (n + m) → α) (f : (fin m → α) → α) (g : (fin n.succ → α) → α) : α := 
  g $ fin.snoc (breakl as) (f $ breakr as)

variables {A B : Type*}


def of (a : A) : fin 1 → A := λ x, a

def proj {m n} (f : fin m → fin n) (as : fin n → A) : fin m → A := as ∘ f
def append {m n} (as : fin m → A) (bs : fin n → A) : fin (m + n) → A := 
  λ i, sum.cases_on (sum_fin_sum_equiv.inv_fun i) as bs

def swap {m n : ℕ} : fin (m + n) → fin (n + m) :=
  λ i, fin.cast (nat.add_comm m n) i

@[simp]
lemma map_append {m n} (as : fin m → A) (bs : fin n → A) (f : A → B) : 
  f ∘ (fin.append as bs) = fin.append (f ∘ as) (f ∘ bs) :=
begin
  sorry,
  /-
  ext,
  by_cases x.val < m,
  { let y : fin m := ⟨x.val, h⟩,
    change f (as.append bs (inl y)) = (as.map f).append (bs.map f) (inl y),
    repeat {rw append_eval_inl},
    refl, },
  { rw not_lt at h,
    let y := fin.sub_nat m x.swap_args h,
    repeat {rw eval_sub _ _  x h},
    rw map_eval, }
    -/
end

@[reducible]
def succ_helper {n} (as : fin (1 + n) → A) : fin n.succ → A := as ∘ (@swap n 1)

@[simp]
lemma swap_swap {m n : ℕ} (i : fin (m + n)) : swap (swap i) = i := by ext; refl

@[simp]
lemma swap_val {m n : ℕ} (i : fin (m + n)) : (swap i).val = i.val := rfl

@[simp]
lemma map_of (a : A) (f : A → B) : f ∘ (of a) = of (f a) := rfl

@[simp]
lemma map_proj {m n} (f : fin m → fin n) (g : A → B) (as : fin n → A) : 
  g ∘ (proj f as) = proj f (g ∘ as) := rfl

@[simp]
lemma map_breakl {m n} (f : A → B) (as : fin (m + n) → A) : f ∘ (breakl as) = breakl (f ∘ as) := rfl

@[simp]
lemma map_breakr {m n} (f : A → B) (as : fin (m + n) → A) : f ∘ (breakr as) = breakr (f ∘ as) := rfl

end fin