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


@[reducible]
def inl {m n} : fin m → fin (m + n) := η ∘ sum.inl 
@[reducible]
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
lemma map_append {m n} (as : ftuple A m) (bs : ftuple A n) (f : A → B) : 
  (as.append bs).map f = (as.map f).append (bs.map f) :=
begin
  ext,
  unfold map,
  simp,
  by_cases hp : x.val ≤ m,  -- I think this is how to do it?
  {
    sorry,
  },
  {
    sorry,
  }
end

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

--example {n : ℕ} : n.succ = n + 1 := rfl

lemma cons_shift {n} (a : A) (as : ftuple A n) :
  ∀ i : fin n, ((cons a as) (i.succ) = as i) :=
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

-- #check fin.exists_eq_succ_of_ne_zero error!

example (n : ℕ) (hn : n ≠ 0) : ∃ k : ℕ, n = k.succ :=
begin
  exact nat.exists_eq_succ_of_ne_zero hn,
end

def ne_zero_val {n : ℕ} (i : fin n.succ) (h : i ≠ 0) : 0 < i.val := 
begin
  sorry,
end

def prev {n : ℕ} (i : fin n.succ) : i ≠ 0 → fin n := λ h, ⟨i.1 - 1, 
begin
  cases i,
  have := ne_zero_val _ h,
  dsimp only [] at *,
  change i_val < n + 1 at i_is_lt,
  exact (nat.sub_lt_right_iff_lt_add this).mpr i_is_lt,
end⟩

#check nat.sub_lt_left_iff_lt_add

/-
lemma append_eval {m n} (as : ftuple A m) (bs : ftuple A n) (i : fin (m+n)) :
  (as.append bs) i = if h : i.1 < m then as ⟨i.1,h⟩ else bs ⟨i.1 - m, 
    (nat.nat.sub_lt_left_iff_lt_add (not_lt.mp h)).mpr i.2⟩ := 
begin
  have : (as.append bs) i = sum.cases_on (δ i) as bs, by refl, rw this, clear this,
  sorry,
end
-/

example (n : ℕ) (fn : fin n.succ) (hfn : fn ≠ 0) : ∃ k : fin n, fn = k.succ :=
begin
  library_search!,
end

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
    { have : j.1 - 1 < n, 
      { 
        
      },
      have claim : j = (⟨j.1 - 1, this⟩ : fin n).succ, by sorry,
      rw claim at *,
      simp_rw cons_shift,
      apply h }}
end

lemma head_rel {n} (a b : A) (as : ftuple A n) : 
  (∀ i, (cons a as) i ≈ (cons b as) i) ↔
  a ≈ b := sorry

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

-- by induction on n.
theorem exists_rep {n} {f : A → B} (bs : ftuple B n) (surj : function.surjective f) :
  ∃ as : ftuple A n, as.map f = bs := sorry

end other_lemmas

end ftuple