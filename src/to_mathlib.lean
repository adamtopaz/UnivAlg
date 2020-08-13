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

end fin