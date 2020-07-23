import data.equiv.fin
import data.nat.basic
import tactic

/-!

# Finite Tuples

This file contains some definitions and results around finite tuples in an arbitrary type.
We have chosen to implement finite `n`-tuples in `A` as maps `fin n → A`.
This is primarily due to some restrictions arising from our inductive constructions.

-/

def ftuple (A : Type*) (n : ℕ) := fin n → A

local notation `η` := sum_fin_sum_equiv.to_fun 
local notation `δ` := sum_fin_sum_equiv.inv_fun

namespace ftuple
section definitions
/-!
## Definitions
This section contains some basic definitions.
-/

variables {A : Type*} {B : Type*}


def inl {m n} : fin m → fin (m + n) := η ∘ sum.inl 
def inr {m n} : fin n → fin (m + n) := η ∘ sum.inr

def nil : ftuple A 0 := λ i, fin.elim0 i
def cast {m n} (h : m = n) (as : ftuple A m) : ftuple A n := as ∘ (fin.cast h.symm)
def cast_to {m} (as : ftuple A m) (n) (h : m = n) : ftuple A n := as.cast h
def of (a : A) : ftuple A 1 := λ i, a
def append {m n} (as : ftuple A m) (bs : ftuple A n) : ftuple A (m+n) := λ i, sum.cases_on (δ i) as bs
def map {n} (as : ftuple A n) (f : A → B) : ftuple B n := f ∘ as
def proj {m n} (f : fin m → fin n) (as : ftuple A n) : ftuple A m := as ∘ f
def init {m n} (as : ftuple A (m + n)) : ftuple A m := λ i, as (η $ sum.inl i)
def last {m n} (as : ftuple A (m + n)) : ftuple A n := λ i, as (η $ sum.inr i)
def compl {m n} (as : ftuple A (m+n)) (f : ftuple A m → A) (g : ftuple A (1 + n) → A) : A := 
  g $ append (of $ f as.init) as.last
def compr {m n} (as : ftuple A (n+m)) (f : ftuple A m → A) (g : ftuple A (n + 1) → A) : A := 
  g $ append as.init $ of $ f as.last

def cons {n} (a : A) (as : ftuple A n) : ftuple A (n+1) := ((of a).append as).cast (by rw add_comm)
def head {n} (as : ftuple A (n+1)) := as 0
def tail {n} (as : ftuple A (n+1)) : ftuple A n := (as.cast_to (1+n) (by rw add_comm)).last

def curry {n} (f : ftuple A (n+1) → B) : A → (ftuple A n → B) := λ a as, f (cons a as) 
def uncurry {n} (f : A → (ftuple A n → B)) : ftuple A (n+1) → B := λ as, f as.head as.tail

end definitions

section map_lemmas

variables {A : Type*} {B : Type*} {C : Type*}

@[simp]
lemma map_of (a : A) (f : A → B) : (of a).map f = of (f a) := rfl

@[simp]
lemma map_proj {m n} (f : fin m → fin n) (g : A → B) (as : ftuple A n) : 
  (as.proj f).map g = (as.map g).proj f := rfl

@[simp]
lemma map_init {m n} (f : A → B) (as : ftuple A (m+n)) : as.init.map f = (as.map f).init := rfl

@[simp]
lemma map_last {m n} (f : A → B) (as : ftuple A (m+n)) : as.last.map f = (as.map f).last := rfl

@[simp]
lemma map_map {n} (f : A → B) (g : B → C) (as : ftuple A n) : as.map (g ∘ f) = (as.map f).map g := rfl

@[simp]
lemma map_eval {n} (f : A → B) (as : ftuple A n) : ∀ i, (as.map f) i = f (as i) := by tauto

end map_lemmas

section quotient_stuff

variables {A : Type*} [I : setoid A] 
variables {B : Type*}

lemma cast_eval {m n} (h : m = n) (as : ftuple A m) (i : fin n):
  (cast h as) i = as (fin.cast h.symm i) := rfl

lemma cons_at_zero {n} (a : A) (as : ftuple A n) :
  cons a as 0 = a := rfl

lemma append_eval_inl {m n} (as : ftuple A m) (bs : ftuple A n) (i : fin m) :
  (as.append bs) (inl i) = as i := 
begin
  unfold append,
  dsimp only [],
  have : inl i = η (sum.inl i), by refl, rw this, clear this,
  rw equiv.left_inv,
end

lemma append_eval_inr {m n} (as : ftuple A m) (bs : ftuple A n) (i : fin n) :
  (as.append bs) (inr i) = bs i := 
begin
  unfold append, 
  dsimp only [],
  have : inr i = η (sum.inr i), by refl, rw this, clear this,
  rw equiv.left_inv,
end

@[simp]
lemma map_append {m n} (as : ftuple A m) (bs : ftuple A n) (f : A → B) : 
  (as.append bs).map f = (as.map f).append (bs.map f) :=
begin
  ext,
  unfold map,
  simp,
  by_cases hp : x.val ≤ m,  
  -- I think this is how to do it?
  -- Then use append_eval_inr?
  {
    sorry,
  },
  {
    sorry,
  }
end

lemma cons_shift {n} (a : A) (as : ftuple A n) 
  : ∀ i : fin n, ((cons a as) (i.succ) = as i) :=
begin
  intro i,
  have : fin.cast (show n + 1 = 1 + n, by rw add_comm) i.succ = inr i, 
  { ext,
    have : (inr i).val = 1 + i.1, by refl,
    rw this, clear this,
    have : (fin.cast (show n + 1 = 1 + n, by rw add_comm) i.succ).val = (i.succ).val, by refl,
    rw this, clear this, 
    cases i,
    unfold fin.succ,
    dsimp only [],
    rw add_comm },
  change (of a).append as _ = _,
  rw this,
  apply append_eval_inr,
end

lemma val_nonzero_of_fin_nonzero {n : ℕ} (i : fin n.succ) (h : i ≠ 0) : i.val ≠ 0 :=
begin
  -- Library search didn't get this one
  intro contra,
  exact h ((fin.ext_iff i 0).mpr contra),
end

def zero_lt_val {n : ℕ} (i : fin n.succ) (h : i ≠ 0) : 0 < i.val := 
begin
  have hi := val_nonzero_of_fin_nonzero i h,
  exact nat.pos_of_ne_zero hi,
end

lemma nat.exists_pred_of_ne_zero (n : ℕ) (hn : n ≠ 0) : ∃ m, m + 1 = n :=
begin
  -- Library search didn't get this one
  induction n with n ind,
  {
    exfalso,
    exact hn (by refl),
  },
  by_cases n = 0,
  {
    use 0,
    rw h,
  },
  {
    specialize ind h,
    cases ind with m hm,
    use m + 1,
    rw hm,
  }
end

def exists_pred_of_ne_zero {n : ℕ} (f1 : fin n.succ) (hf1 : f1 ≠ 0) 
  : ∃ f2 : fin n, f2.succ = f1 :=
begin
  have h1 := zero_lt_val f1 hf1,
  have f1_val_pred := nat.exists_pred_of_ne_zero f1.val (ne_of_lt h1).symm,
  cases f1_val_pred with f1_val_pred hpred,
  use f1_val_pred,
  {
    cases f1 with vf1 pf1,
    change _ = vf1 at hpred,
    rw ←hpred at pf1,
    rw nat.succ_eq_add_one at pf1,
    exact (add_lt_add_iff_right 1).mp pf1,
  },
  {
    tidy,
  }
end

def prev {n : ℕ} (i : fin n.succ) : i ≠ 0 → fin n := λ h, ⟨i.1 - 1, 
begin
  cases i,
  have := zero_lt_val _ h,
  dsimp only [] at *,
  change i_val < n + 1 at i_is_lt,
  exact (nat.sub_lt_right_iff_lt_add this).mpr i_is_lt,
end⟩

include I
lemma tail_rel {n} (a : A) (as bs : ftuple A n) : 
  (∀ i, (cons a as) i ≈ (cons a bs) i) ↔
  (∀ i, as i ≈ bs i) :=
begin
  split,
  { intros h j,
    replace h := h (j.succ),
    repeat {rw cons_shift at h},
    exact h },
  { intros h j, 
    by_cases c : j = 0,
    { rw c,
      simp_rw cons_at_zero },
    { 
      have pred := exists_pred_of_ne_zero j c,
      cases pred with pred hpred,
      rw ← hpred,
      repeat {rw cons_shift},
      exact h pred,
    }
  }
end

lemma head_rel {n} (a b : A) (as : ftuple A n) : 
  (∀ i, (cons a as) i ≈ (cons b as) i) ↔
  a ≈ b :=
begin
  split,
  {
    intro h,
    specialize h 0,
    repeat {rw cons_at_zero at h},
    exact h,
  },
  {
    intros h i,
    by_cases hi : i = 0,
    {
      rw hi,
      repeat {rw cons_at_zero},
      exact h,
    },
    {
      have pred := exists_pred_of_ne_zero i hi,
      cases pred with pred hpred,
      rw ← hpred,
      repeat {rw cons_shift},
    },
  }
end

def quotient_lift : Π {n} (f : ftuple A n → B) 
  (hyp : ∀ (as bs : ftuple A n), (∀ i, as i ≈ bs i) → f as = f bs),  
  ftuple (quotient I) n → B := λ n, nat.rec_on n 
  (λ f hyp, λ _, f nil) 
  (λ n ind f hyp, uncurry $ quotient.lift (λ a, ind (curry f a) 
  begin
    intros as bs h, 
    change f _ = f _,
    apply hyp,
    rw tail_rel, assumption,
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

-- by induction on n
theorem quotient_lift_beta {n} (f : ftuple A n → B)
  (hyp : ∀ (as bs : ftuple A n), (∀ i, as i ≈ bs i) → f as = f bs) (as : ftuple A n):  
  (quotient_lift f hyp) (as.map (λ a, ⟦a⟧)) = f as := 
begin
  induction n with n ind,
  { sorry, },
  { sorry, }
end

#check @quotient.lift_beta

end quotient_stuff

section other_lemmas

variables {A : Type*} {B : Type*}

-- There is only one empty tuple
lemma nil_unique (ft1 ft2 : ftuple A 0) : ft1 = ft2 :=
begin
  ext,
  exfalso,
  exact nat.not_lt_zero x.1 x.2,
end

lemma eq_zero_of_lt_one (n : ℕ) (hn : n < 1) : n = 0 :=
begin
  -- Oddly, library search didn't work here either. Am I not using it right?
  induction n with n ind,
  refl,
  exfalso,
  have : n < 1 := nat.lt_of_succ_lt hn,
  specialize ind this,
  rw ind at hn,
  have problem : ¬ 1 < 1 := asymm hn,
  exact problem hn,
end

lemma cons_nil (a : A)
  : (cons a nil) = of a :=
begin
  ext,
  have hx : x = 0, by
  {
    cases x with x hx,
    have := eq_zero_of_lt_one x hx,
    exact subsingleton.elim ⟨x, hx⟩ 0,
  },
  rw hx,
  rw cons_at_zero,
  refl,
end


lemma tail_shift {n : ℕ} (as : ftuple A n.succ)
  : ∀ i, as.tail i = as i.succ :=
begin
  sorry,
end

lemma map_cons {n} (as : ftuple A n) (a : A) (f : A → B)
  : (cons a as).map f = cons (f a) (as.map f) :=
begin
  sorry,
end

-- This will let us split up ftuples for the following theorem
lemma is_append {n : ℕ} (as : ftuple A (n.succ))
  : cons (as 0) as.tail = as :=
begin
  ext,
  by_cases x = 0,
  {
    rw [h, cons_at_zero],
  },
  {
    have pred := exists_pred_of_ne_zero x h,
    cases pred with pred hpred,
    rw ←hpred,
    rw cons_shift,
    apply tail_shift as,
  }
end

-- by induction on n.
theorem exists_rep {n} {f : A → B} (bs : ftuple B n) (surj : function.surjective f) :
  ∃ as : ftuple A n, as.map f = bs :=
begin
  induction n with n hn,
  {
    use nil,
    apply nil_unique,
  },
  {
    rw ←is_append bs,
    specialize surj (bs 0),
    cases surj with a ha,
    specialize hn bs.tail,
    cases hn with as has,
    use cons a as,
    ext,
    by_cases x = 0,
    {
      rw h,
      rw cons_at_zero,
      rw map_cons,
      rw cons_at_zero,
      exact ha,
    },
    {
      have pred := exists_pred_of_ne_zero x h,
      cases pred with pred hpred,
      rw ←hpred,
      repeat {rw map_cons},
      repeat {rw cons_shift},
      rw has,
    }
  }
end

end other_lemmas

end ftuple