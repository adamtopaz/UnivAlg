import data.equiv.fin
import data.fin
import data.nat.basic
import tactic
import init.data.nat.lemmas

/-!

# Finite Tuples

This file contains some definitions and results around finite tuples in an arbitrary type.
We have chosen to implement finite `n`-tuples in `A` as maps `fin n → A`.
This is primarily due to some restrictions arising from our inductive constructions.

-/

def ftuple (A : Type*) (n : ℕ) := fin n → A

local notation `η` := sum_fin_sum_equiv.to_fun 
local notation `δ` := sum_fin_sum_equiv.inv_fun

def fin.swap_args {m n} (f : fin (m + n)) : fin (n + m) := f.cast (by rwa add_comm)

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
def swap_args {m n} (as : ftuple A (m + n)) : ftuple A (n + m) := cast (by rwa add_comm) as
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

def cons {n} (a : A) (as : ftuple A n) : ftuple A (n+1) := fin.cons a as --((of a).append as).cast (by rw add_comm)
def head {n} (as : ftuple A (n+1)) := as 0
def tail {n} (as : ftuple A (n+1)) : ftuple A n := fin.tail as --(as.cast_to (1+n) (by rw add_comm)).last

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


section other_lemmas

variables {A : Type*} {B : Type*}

-- There is only one empty tuple
lemma nil_unique (ft1 ft2 : ftuple A 0) : ft1 = ft2 :=
begin
  ext,
  exact fin_zero_elim x,
end

lemma cast_eval {m n} (h : m = n) (as : ftuple A m) (i : fin n):
  (cast h as) i = as (fin.cast h.symm i) := rfl

@[simp]
lemma cons_at_zero {n} (a : A) (as : ftuple A n) :
  cons a as 0 = a := rfl

@[simp]
lemma append_eval_inl {m n} (as : ftuple A m) (bs : ftuple A n) (i : fin m) :
  (as.append bs) (inl i) = as i := 
begin
  unfold append,
  dsimp only [],
  have : inl i = η (sum.inl i), by refl, rw this, clear this,
  rw equiv.left_inv,
end

@[simp]
lemma append_eval_inr {m n} (as : ftuple A m) (bs : ftuple A n) (i : fin n) :
  (as.append bs) (inr i) = bs i := 
begin
  unfold append,
  dsimp only [],
  have : inr i = η (sum.inr i), by refl, rw this, clear this,
  rw equiv.left_inv,
end

private lemma sub_helper {m n} (x : fin (m + n)) (hx : m ≤ x.val)
  : x.val - m < n :=
begin
  cases x with xv xp,
  apply (nat.sub_lt_left_iff_lt_add hx).mpr,
  exact xp,
end

lemma lt_swap {m n} (x : fin (m + n))
  : x.val < n + m :=
begin
  cases x with xv xp,
  rw add_comm at xp,
  exact xp,
end

lemma inr_val {m n} (x : fin n)
  : (@inr m n x).val = x.val + m:=
begin
  unfold inr,
  exact add_comm m x.val,
end

lemma inr_sub {m n} (x : fin (m + n)) (hx : m ≤ x.val)
  : inr (fin.sub_nat m x.swap_args hx) = x :=
begin
  ext,
  rw inr_val,
  rw fin.sub_nat_val _ _,
  exact nat.sub_add_cancel hx,
end

lemma eval_sub {m n} (as : ftuple A m) (bs : ftuple A n) (x : fin (m + n)) (hx : m ≤ x.val)
  : (as.append bs) x = bs (fin.sub_nat m x.swap_args hx) :=
begin
  conv_lhs
  { rw ← (inr_sub x hx), },
  rw append_eval_inr,
end

@[simp]
lemma map_append {m n} (as : ftuple A m) (bs : ftuple A n) (f : A → B) : 
  (as.append bs).map f = (as.map f).append (bs.map f) :=
begin
  ext,
  rw map_eval,
  by_cases x.val < m,
  { let y : fin m := ⟨x.val, h⟩,
    change f (as.append bs (inl y)) = (as.map f).append (bs.map f) (inl y),
    repeat {rw append_eval_inl},
    refl, },
  { rw not_lt at h,
    let y := fin.sub_nat m x.swap_args h,
    repeat {rw eval_sub _ _  x h},
    rw map_eval, }
end

lemma cons_shift {n} (a : A) (as : ftuple A n) 
  : ∀ i : fin n, ((cons a as) (i.succ) = as i) := by apply fin.cons_succ

lemma val_nonzero_of_fin_nonzero {n : ℕ} (i : fin n.succ) (h : i ≠ 0) : i.val ≠ 0 :=
begin
  intro contra,
  exact h ((fin.ext_iff i 0).mpr contra),
end

def zero_lt_val {n : ℕ} (i : fin n.succ) (h : i ≠ 0) : 0 < i.val := 
begin
  have hi := val_nonzero_of_fin_nonzero i h,
  exact nat.pos_of_ne_zero hi,
end

lemma cons_nil (a : A)
  : (cons a nil) = of a :=
begin
  ext,
  have hx : x = 0, by exact subsingleton.elim x 0,
  rw hx,
  rw cons_at_zero,
  refl,
end

lemma tail_shift {n : ℕ} (as : ftuple A n.succ)
  : ∀ i, as.tail i = as i.succ := 
begin
  intro i,
  symmetry, 
  have : as = cons as.head as.tail,
  { unfold cons,
    erw fin.cons_self_tail },
  conv_lhs {rw this},
  apply fin.cons_succ,
end

lemma map_cons {n} (as : ftuple A n) (a : A) (f : A → B)
  : (cons a as).map f = cons (f a) (as.map f) :=
begin
  ext,
  by_cases hx : x = 0,
  { rw hx,
    rw cons_at_zero,
    refl, },
  { rw ← fin.succ_pred x hx,
    rw cons_shift,
    rw map_eval,
    rw cons_shift,
    refl, }
end

-- This will let us split up ftuples for the following theorem
lemma is_append {n : ℕ} (as : ftuple A (n.succ))
  : cons (as 0) as.tail = as :=
begin
  ext,
  by_cases x = 0,
  { rw [h, cons_at_zero], },
  { rw ← fin.succ_pred x h,
    rw cons_shift,
    apply tail_shift as, }
end

-- by induction on n.
theorem exists_rep {n} {f : A → B} (bs : ftuple B n) (surj : function.surjective f) :
  ∃ as : ftuple A n, as.map f = bs :=
begin
  induction n with n hn,
  { use nil,
    apply nil_unique, },
  { rw ←is_append bs,
    specialize surj (bs 0),
    cases surj with a ha,
    specialize hn bs.tail,
    cases hn with as has,
    use cons a as,
    ext,
    by_cases x = 0,
    { rw h,
      rw cons_at_zero,
      rw map_cons,
      rw cons_at_zero,
      exact ha, },
    { rw ← fin.succ_pred x h,
      repeat {rw map_cons},
      repeat {rw cons_shift},
      rw has, } }
end

end other_lemmas


section quotient_stuff

variables {A : Type*} [I : setoid A] 
variables {B : Type*}

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
    {  rw ← fin.succ_pred j c,
      repeat {rw cons_shift},
      finish, } }
end

lemma head_rel {n} (a b : A) (as : ftuple A n) : 
  (∀ i, (cons a as) i ≈ (cons b as) i) ↔
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
      repeat {rw cons_shift}, } }
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
  { have : as = nil, by apply nil_unique,
    rw this,
    refl },
  { erw ind,
    unfold curry,
    apply congr_arg,
    exact is_append as }
end

end quotient_stuff

end ftuple