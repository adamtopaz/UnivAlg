import ..lang
import data.nat.basic

namespace langs

namespace monoid

inductive preL : ℕ → Type
| one   : preL 0
| mul   : preL 2
--| const : preL 1 

def L : lang := ⟨preL⟩

open lang.term

inductive preR : Π n, L.gen n → L.gen n → Prop 
| one_mul : preR 1 get $ proj (fin.cast $ show 0 + 1 = 1, by simp) 
    (compl (of preL.one) 
    (proj (fin.cast $ show 2 = 1 + 1, by simp) (of preL.mul)))
| mul_one : preR 1 get $ proj (fin.cast $ show 1 + 0 = 1, by simp) 
    (compr (of preL.one) 
    (proj (fin.cast $ show 2 = 1 + 1, by simp) (of preL.mul)))
| mul_assoc : preR 3
    (proj (fin.cast $ show 2 + 1 = 3, by simp) $ compl 
      (of preL.mul) 
      (proj (fin.cast $ show 2 = 1 + 1, by simp) $ of preL.mul))
    (proj (fin.cast $ show 1 + 2 = 3, by simp) $ compr 
      (of preL.mul) 
      (proj (fin.cast $ show 2 = 1 + 1, by simp) $ of preL.mul))

def R : rules L := ⟨preR⟩

end monoid

end langs