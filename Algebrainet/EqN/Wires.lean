import Algebrainet.EqN

namespace EqN
open Net

variable
  {S : System}
  {aᵢ aₒ : Nat} {A : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {B : Net S bᵢ bₒ}
  {a b n n₁ n₂ : Nat}

set_option autoImplicit false

def wires₁ : EqN S # (wires 1) wire := nil_mix
def wires₂ : EqN S # (wires 2) (mix wire wire) := mix₀ wires₁
def cat_wire {h : _} : EqN S # (cat h A wire) A := trans (cat₁ (h₂ := h) (symm wires₁)) (cat_wires)
def wire_cat {h : _} : EqN S # (cat h wire A) A := trans (cat₀ (h₂ := h) (symm wires₁)) (wires_cat)
def wires_ : {h : n₁ = n₂} -> EqN S # (wires n₁) (wires n₂)
  | rfl => refl

def wires_mix_wires {h : a + b = n} : EqN S # (mix (wires a) (wires b)) (wires n) := by
  revert n
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

def wire_mix_wires : EqN S # (mix wire (wires a)) (wires (a + 1)) := by
  apply trans
  apply mix₀ (symm wires₁)
  apply wires_mix_wires
  simp

def wire_mix_wires_ {h : a + 1 = n} : EqN S # (mix wire (wires a)) (wires n) := by
  apply trans
  apply mix₀ (symm wires₁)
  apply wires_mix_wires
  simp [*]

def up_down : EqN S # (mix A B) (cat # (mix (wires aᵢ) B) (mix A (wires bₒ))) := by
  apply trans
  apply mix_
  apply symm (wires_cat (n := aᵢ)); simp
  apply symm (cat_wires (n := bₒ)); simp
  apply symm exch

def down_up : EqN S # (mix A B) (cat # (mix A (wires bᵢ)) (mix (wires aₒ) B)) := by
  apply trans
  apply mix_
  apply symm (cat_wires (n := aₒ)); simp
  apply symm (wires_cat (n := bᵢ)); simp
  apply symm exch
