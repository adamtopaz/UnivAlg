import data.equiv.fin
import data.fin

namespace fin
variables {α : Type*} {β : Type*}

@[reducible]
def inl {m n} : fin m → fin (m + n) := sum_fin_sum_equiv ∘ sum.inl  
@[reducible]
def inr {m n} : fin n → fin (m + n) := sum_fin_sum_equiv ∘ sum.inr  

@[simp] def of (a : α) : fin 1 → α := λ x, a
def append {m n} (as : fin m → α) (bs : fin n → α) : fin (m + n) → α := 
  λ i, sum.cases_on (sum_fin_sum_equiv.inv_fun i) as bs
@[simp] def breakl {m n : ℕ} (as : fin (m + n) → α) : fin m → α := λ i, as (sum_fin_sum_equiv $ sum.inl i)
@[simp] def breakr {m n : ℕ} (as : fin (m + n) → α) : fin n → α := λ i, as (sum_fin_sum_equiv $ sum.inr i)
@[simp] def compl {m n : ℕ} (as : fin (m + n) → α) (f : (fin m → α) → α) (g : (fin (1 + n) → α) → α) : α := 
  g $ (append (of $ f $ breakl as) (breakr as))
@[simp] def compr {m n : ℕ} (as : fin (n + m) → α) (f : (fin m → α) → α) (g : (fin (n + 1) → α) → α) : α := 
  g $ (append (breakl as) (of $ f $ breakr as))
def swap {m n : ℕ} : fin (m + n) → fin (n + m) :=
  λ i, fin.cast (nat.add_comm m n) i
def nil : fin 0 → α := λ i, fin.elim0 i
 
#check function.curry
 
--def curry {n} (f : ftuple A (n+1) → B) : A → (ftuple A n → B) := λ a as, f (cons a as) 
--def uncurry {n} (f : A → (ftuple A n → B)) : ftuple A (n+1) → B := λ as, f as.head as.tail
@[simp] def curry {n : ℕ} (f : (fin (n + 1) → α) → β) : α → ((fin n → α) → β) := 
  λ a as, f (cons a as)
@[simp] def uncurry {n : ℕ} (f : α → ((fin n → α) → β)) : (fin (n + 1) → α) → β := 
  λ as, f (as 0) (tail as) 

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

theorem exists_rep {n} (bs : fin n → β) (f : α → β) (hyp : function.surjective f) : ∃ as : fin n → α, f ∘ as = bs := 
begin
  induction n,
  { simp },
  { rcases n_ih (tail bs) with ⟨cs,h⟩,
    rcases hyp (bs 0) with ⟨b,h1⟩,
    use cons b cs,
    ext,
    by_cases h2 : x = 0,
    { rw h2, simpa },
    { -- x = succ of something
      rw ←fin.succ_pred x h2,
      rw function.comp_app,
      simp only [cons_succ],
      change (f ∘ cs) _ = _,
      rw h,
      refl } } 
end

section quotient_stuff

variable [I : setoid α]
include I


lemma tail_rel {n : ℕ} (a : α) (as bs : fin n → α) :
  (∀ (i : fin (n+1)), (cons a as : fin _ → α) i ≈ (cons a bs : fin _ → α) i) ↔
  (∀ (i : fin n), as i ≈ bs i) :=
begin
  split,
  { intros h j,
    replace h := h (j.succ),
    repeat {rw fin.cons_succ at h},
    exact h },
  { intros h j, 
    by_cases c : j = 0,
    { rw c,
      simp_rw fin.cons_zero },
    {  rw ← fin.succ_pred j c,
      finish, } }
end

lemma head_rel {n : ℕ} (a b : α) (as : fin n → α) : 
  (∀ i, (cons a as : fin _ → α) i ≈ (cons b as : fin _ → α) i) ↔
  a ≈ b :=
begin
  split,
  { intro h,
    specialize h 0,
    repeat {rw cons_at_zero at h},
    exact h, },
  { intros h i,
    by_cases hi : i = 0,
    { rw hi,
      repeat {rw cons_at_zero},
      exact h, },
    { rw ← fin.succ_pred i hi,
      repeat {rw fin.cons_succ}}, }
end

def quotient_lift : Π {n} (f : (fin n → α) → β)
  (hyp : ∀ (as bs : fin n → α), (∀ i, as i ≈ bs i) → f as = f bs), 
  (fin n → quotient I) → β := λ n, nat.rec_on n
  (λ f _ _, f $ inhabited.default _) 
  (λ n ind f hyp, uncurry $ quotient.lift (λ a, ind (curry f a)
  begin
    intros as bs h,
    simp,
    apply hyp,
    rw tail_rel,
    assumption,
  end) 
  begin
    intros a b h, 
    dsimp only [],
    suffices : curry f a = curry f b, by simp_rw this,
    funext,
    change f _ = f _,
    apply hyp,
    rw head_rel, assumption,
  end)
 
@[simp] theorem quotient_lift_beta {n} (f : (fin n → α) → β)
  (hyp : ∀ (as bs : fin n → α), (∀ i, as i ≈ bs i) → f as = f bs) (as : fin n → α):  
  (quotient_lift f hyp) ((λ a, ⟦a⟧) ∘ as) = f as :=
begin
  induction n with n ind,
  { have h : as = nil, by simp,
    rw h,
    refl,},
  { erw ind,
    unfold curry,
    apply congr_arg,
    exact fin.cons_self_tail as, }
end
  
end quotient_stuff

end fin
