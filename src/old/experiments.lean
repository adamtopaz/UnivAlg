import algebra

variables (M : Type*) [monoid M]

def foo0 : M → Prop := λ x,
  ∀ (N : Type*) [monoid N] 
    (g : M →* N), g x = 1 -- fails to find the monoid instance for N.

def foo1 : M → Prop := λ x, 
  ∀ (N : Type*) (h : monoid N), by letI := h; exact ∀ (g : M →* N), g x = 1

def comm_rel_2 : M → Prop := λ x,
  ∀ (N : Type*) (h : monoid N)
    (g : @monoid_hom M N _ h), g x = (@monoid.to_has_one _ h).one -- this works 
