import data.equiv.fin
import data.fin

namespace fin
variables {α : Type*} {β : Type*}

def of (a : α) : fin 1 → α := λ x, a
def append {m n} (as : fin m → α) (bs : fin n → α) : fin (m + n) → α := 
  λ i, sum.cases_on (sum_fin_sum_equiv.inv_fun i) as bs
def breakl {m n : ℕ} (as : fin (m + n) → α) : fin m → α := λ i, as (sum_fin_sum_equiv $ sum.inl i)
def breakr {m n : ℕ} (as : fin (m + n) → α) : fin n → α := λ i, as (sum_fin_sum_equiv $ sum.inr i)
def compl {m n : ℕ} (as : fin (m + n) → α) (f : (fin m → α) → α) (g : (fin (1 + n) → α) → α) : α := 
  g $ (append (of $ f $ breakl as) (breakr as))
def compr {m n : ℕ} (as : fin (n + m) → α) (f : (fin m → α) → α) (g : (fin (n + 1) → α) → α) : α := 
  g $ (append (breakl as) (of $ f $ breakr as))
def swap {m n : ℕ} : fin (m + n) → fin (n + m) :=
  λ i, fin.cast (nat.add_comm m n) i

@[simp] lemma map_append {m n} (as : fin m → α) (bs : fin n → α) (f : α → β) : 
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

@[simp] lemma swap_swap {m n : ℕ} (i : fin (m + n)) : swap (swap i) = i := by {ext, refl}
@[simp] lemma swap_val {m n : ℕ} (i : fin (m + n)) : (swap i).val = i.val := rfl
@[simp] lemma map_of (a : α) (f : α → β) : f ∘ (of a) = of (f a) := rfl
@[simp] lemma map_breakl {m n} (f : α → β) (as : fin (m + n) → α) : f ∘ (breakl as) = breakl (f ∘ as) := rfl
@[simp] lemma map_breakr {m n} (f : α → β) (as : fin (m + n) → α) : f ∘ (breakr as) = breakr (f ∘ as) := rfl

end fin