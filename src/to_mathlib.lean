import data.equiv.fin
import data.fin

namespace fin
variables {α : Type*} {β : Type*}

@[reducible]
def inl {m n} : fin m → fin (m + n) := sum_fin_sum_equiv ∘ sum.inl  
@[reducible]
def inr {m n} : fin n → fin (m + n) := sum_fin_sum_equiv ∘ sum.inr  

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

@[simp] lemma append_eval_inl {m n} (as : fin m → α) (bs : fin n → α) (i : fin m) : 
  (append as bs) i.inl = as i := 
begin
  unfold append,
  dsimp only [],
  have : sum_fin_sum_equiv.inv_fun i.inl = sum.inl i, by simp,
  rw this, 
end

@[simp] lemma append_eval_inr {m n} (as : fin m → α) (bs : fin n → α) (i : fin n) : 
  (append as bs) i.inr = bs i := 
begin
  unfold append,
  dsimp only [],
  have : sum_fin_sum_equiv.inv_fun i.inr = sum.inr i, by simp,
  rw this, 
end

@[simp] lemma map_append {m n} (as : fin m → α) (bs : fin n → α) (f : α → β) : 
  f ∘ (fin.append as bs) = fin.append (f ∘ as) (f ∘ bs) := 
begin
  ext i,
  have : i = sum_fin_sum_equiv (sum_fin_sum_equiv.symm i), by simp,
  rw this, clear this,
  cases sum_fin_sum_equiv.symm i; simp
end

@[simp] lemma swap_swap {m n : ℕ} (i : fin (m + n)) : swap (swap i) = i := by {ext, refl}
@[simp] lemma swap_val {m n : ℕ} (i : fin (m + n)) : (swap i).val = i.val := rfl
@[simp] lemma map_of (a : α) (f : α → β) : f ∘ (of a) = of (f a) := rfl
@[simp] lemma map_breakl {m n} (f : α → β) (as : fin (m + n) → α) : f ∘ (breakl as) = breakl (f ∘ as) := rfl
@[simp] lemma map_breakr {m n} (f : α → β) (as : fin (m + n) → α) : f ∘ (breakr as) = breakr (f ∘ as) := rfl

end fin