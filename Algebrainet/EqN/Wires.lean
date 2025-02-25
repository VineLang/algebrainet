import Algebrainet.EqN

namespace EqN
open Net

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}

set_option autoImplicit false

def wires₁ : EqN (S := S) # (wires 1) wire := nil_mix
def wires₂ : EqN (S := S) # (wires 2) (mix wire wire) := mix₀ wires₁
def cat_wire {h : _} : EqN S # (cat h a wire) a := trans (cat₁ (h₂ := h) (symm wires₁)) (cat_wires)
def wire_cat {h : _} : EqN S # (cat h wire a) a := trans (cat₀ (h₂ := h) (symm wires₁)) (wires_cat)
def wires_ {n₁ n₂ : Nat} : {h : n₁ = n₂} -> EqN (S := S) # (wires n₁) (wires n₂)
  | rfl => refl

def wires_mix_wires {a b x : Nat} {h : a + b = x} : EqN (S := S) # (mix (wires a) (wires b)) (wires x) := by
  revert x
  induction b
  intro x h
  apply trans
  exact mix_nil
  apply wires_
  assumption
  rename_i ih
  simp only [wires]
  intro x h
  apply trans
  apply symm
  exact mix_assoc
  apply trans
  apply mix₀
  apply ih
  rfl
  apply wires_
  simp [*]

def wire_mix_wires {a : Nat} : EqN (S := S) # (mix wire (wires a)) (wires (a + 1)) := by
  apply trans
  apply mix₀ (symm wires₁)
  apply wires_mix_wires
  simp
