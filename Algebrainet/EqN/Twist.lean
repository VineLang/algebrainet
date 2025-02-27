import Algebrainet.EqN
import Algebrainet.EqN.Wires

namespace EqN
open Net

variable {S : System} {n a b : Nat}
set_option autoImplicit false

def twist₁_1 : EqN S # (twist₁ 1) swap := by
  apply trans cast_
  apply trans; apply cat_
  . apply wires₂.symm
  . apply nil_mix
  simp
  apply wires_cat

def twist_1_n : EqN S # (twist 1 n) (twist₁ n) := by
  apply trans cast_
  apply trans; apply cat_
  . apply trans (mix₁ cast_) wire_mix_wires
  . apply mix_nil
  simp
  apply wires_cat

def twist_1_1 : EqN S # (twist 1 1) swap := trans twist_1_n twist₁_1

def twist₁_succ : EqN S # (twist₁ (n + 1)) (cat # (mix swap (wires n)) (mix wire (twist₁ n))) := by
  induction n
  apply trans twist₁_1
  apply symm
  apply trans
  apply cat_
  apply mix_nil
  apply symm wires₂
  simp
  apply cat_wires

  rename_i n ih
  apply trans
  apply trans cast_
  apply cat₀
  apply trans
  apply mix₀
  assumption
  apply trans
  apply mix₁
  apply symm wire_cat
  simp
  apply symm exch
  repeat simp
  apply trans cat_assoc
  apply cat_
  apply mix_assoc
  apply trans
  apply cat_
  apply mix_assoc
  apply trans
  apply mix₀
  apply trans (symm (wires_mix_wires_ (a := 1) (b := n)))
  apply mix₀
  apply wires₁
  simp
  apply mix_assoc
  simp
  apply trans exch
  apply mix_
  apply wire_cat
  apply symm
  apply cast_
  repeat simp

def untwist₁ (n : Nat) : Net S (n + 1) (1 + n) := twist n 1

def untwist₁_succ : EqN S # (untwist₁ (n + 1)) (cat # (mix (wires n) swap) (mix (untwist₁ n) wire)) := by
  induction n
  simp only [twist₁, untwist₁, twist, wires]
  apply trans cast_
  apply trans
  apply cat_
  apply trans
  apply mix₁
  apply cast_
  apply trans
  apply mix₀
  apply symm wires₁
  apply wires_mix_wires
  simp
  apply trans mix_nil
  apply twist₁_1
  simp
  apply trans wires_cat
  apply symm
  apply trans
  apply cat_
  apply nil_mix
  apply mix₀
  apply cast_
  simp
  apply cat_wires

  rename_i n ih
  apply trans cast_
  apply trans
  apply cat_
  apply trans
  apply mix_
  apply symm cat_wire
  simp
  assumption
  apply trans
  apply symm exch
  simp
  apply cat₀
  apply trans
  apply symm mix_assoc
  apply mix₀
  apply refl
  repeat simp
  apply refl
  simp
  apply trans
  apply cat_assoc
  repeat simp
  apply cat_
  apply mix₀
  apply trans
  apply mix₀
  apply symm wires₁
  apply wires_mix_wires_
  simp
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm mix_assoc
  simp
  apply trans exch
  apply mix_
  apply symm
  apply cast_
  simp
  apply wire_cat
  repeat simp


def twist₁_untwist₁ : EqN S # (cat # (twist₁ n) (untwist₁ n)) (wires (n + 1)) := by
  induction n
  simp only [twist₁, untwist₁, twist, wires]
  apply trans wire_cat
  apply cast_

  rename_i n ih
  apply trans
  simp only [twist₁]
  apply cat_
  apply cast_
  apply untwist₁_succ
  simp
  apply trans cat_assoc
  apply trans
  apply cat₁
  apply trans (symm cat_assoc)
  apply trans
  apply cat₀
  apply trans exch
  apply trans
  apply mix_
  apply wires_cat
  apply swap_swap
  apply trans
  apply mix₁
  apply symm wires₂
  apply wires_mix_wires
  repeat simp
  apply wires_cat
  repeat simp
  apply trans exch
  apply mix_
  assumption
  apply wire_cat
  repeat simp

def twist_n_0 : EqN S # (twist n 0) (wires n) := by
  induction n
  exact cast_
  rename_i n ih
  simp only [twist]
  apply trans cast_
  apply trans
  apply cat_
  apply trans
  apply mix_
  exact symm wires₁
  assumption
  apply wires_mix_wires
  simp
  apply trans
  apply mix₀
  exact symm wires₁
  apply wires_mix_wires_ (n := n + 1)
  repeat simp
  apply wires_cat

def twist_s_n : EqN S # (twist (a + 1) b) (cat # (mix (wires a) (twist₁ b)) (mix (twist a b) wire)) := by
  induction a
  simp only [twist, twist₁, wires]
  apply trans cast_
  apply trans
  apply cat_
  apply trans (mix_ (symm wires₁) cast_)
  apply wires_mix_wires
  simp
  apply mix_nil
  simp
  apply trans wires_cat
  apply symm
  apply trans
  apply cat_
  apply nil_mix
  apply mix₀ cast_
  simp
  apply cat_wires

  rename_i a ih
  apply trans cast_
  apply trans
  apply cat₀
  apply trans
  apply mix_
  apply symm wire_cat
  simp
  assumption
  apply symm exch
  repeat simp
  apply trans cat_assoc
  apply cat_
  apply trans (symm mix_assoc)
  apply mix₀
  apply trans (mix₀ (symm wires₁))
  apply wires_mix_wires_
  simp
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm mix_assoc
  simp
  apply trans exch
  apply mix_
  apply symm
  apply cast_
  apply wire_cat
  repeat simp

def twist_n_s : EqN S # (twist a (b + 1)) (cat # (mix (twist a b) wire) (mix (wires b) (untwist₁ a))) := by
  revert b
  induction a
  intro b
  simp only [twist, wires, untwist₁]
  apply trans cast_
  apply symm
  apply trans
  apply cat_
  apply mix₀ (cast_)
  apply trans (mix₁ cast_)
  apply wires_mix_wires
  repeat simp
  apply wires_cat

  rename_i a ih
  intro b
  apply trans
  apply twist_s_n
  apply trans
  apply cat₁
  apply mix₀
  apply ih
  simp
  apply trans
  apply cat₁
  apply trans
  apply mix₁
  apply symm wire_cat
  simp
  apply symm exch
  repeat simp
  apply trans (symm cat_assoc)
  apply trans
  apply cat₀
  apply trans
  apply cat₀
  apply trans
  apply mix_
  apply symm (wires_cat (n := a))
  simp
  apply cast_
  apply trans (symm exch)
  apply cat₁
  apply trans (symm mix_assoc)
  apply mix₀ wires_mix_wires
  repeat simp
  apply trans
  apply cat₁
  apply mix_assoc
  simp
  apply trans cat_assoc
  apply trans
  apply cat₁
  apply trans exch
  apply trans
  apply mix_
  apply trans wires_cat
  apply symm (cat_wires (n := a + b))
  repeat simp
  apply trans (cat₁ (symm wires₂))
  apply trans cat_wires
  apply symm (wires_cat (n := 2))
  repeat simp
  apply symm exch
  repeat simp
  apply trans (symm (cat_assoc))
  apply cat₀
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm (mix_assoc (z := wire))
  repeat simp
  apply trans exch
  apply mix_
  apply trans
  apply cat₁
  apply mix₁
  apply wires₁
  simp
  apply symm
  apply twist_s_n
  apply wire_cat
  repeat simp
  apply trans cat_assoc
  apply cat₁
  apply trans
  apply cat₀
  apply mix₀
  apply symm (wires_mix_wires_ (a := b) (b := a))
  repeat simp
  apply trans
  apply cat_
  apply mix_assoc
  apply mix_assoc
  repeat simp
  apply trans exch
  apply mix_
  apply cat_wires
  apply symm
  apply untwist₁_succ
  repeat simp

def twist_untwist : EqN S # (cat # (twist a b) (twist b a)) (wires (a + b)) := by
  induction a
  apply trans
  apply cat_
  apply cast_
  apply twist_n_0
  simp
  apply trans cat_wires
  apply wires_
  simp

  rename_i a ih
  apply trans
  apply cat_
  apply twist_s_n
  apply twist_n_s
  simp
  apply trans cat_assoc
  apply trans
  apply cat₁
  apply trans (symm cat_assoc)
  apply trans
  apply cat₀
  apply trans exch
  apply mix_
  assumption
  apply wire_cat
  repeat simp
  apply wires_cat
  repeat simp
  apply trans exch
  apply trans
  apply mix_
  apply wires_cat
  apply twist₁_untwist₁
  apply wires_mix_wires_
  repeat simp

def twist_add_n : EqN S # (twist (a + b) n) (cat # (mix (wires a) (twist b n)) (mix (twist a n) (wires b))) := by
  induction b with
  | zero =>
    apply symm
    apply trans; apply cat_
    . apply trans (mix₁ cast_) wires_mix_wires
    . apply mix_nil
    simp
    apply wires_cat
  | succ b ih =>
    apply trans twist_s_n
    apply trans; apply cat₁; .
      apply trans (mix_ ih wire_cat.symm)
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc.symm
    apply cat_
    . apply trans; apply cat_
      . apply trans (mix₀ (symm wires_mix_wires))
        apply mix_assoc
      . apply mix_assoc
      repeat simp
      apply trans exch
      apply mix_
      . apply cat_wires
      . apply twist_s_n.symm
      repeat simp
    . apply mix_assoc
    repeat simp

def twist_n_add : EqN S # (twist n (a + b)) (cat # (mix (twist n a) (wires b)) (mix (wires a) (twist n b))) := by
  apply trans (cat_wires (n := (a + b + n))).symm
  apply trans; apply cat₁; .
    apply trans (wires_mix_wires_ (a := a) (b := b + n)).symm
    apply trans; apply mix_
    . apply (cat_wires (n := a)).symm; simp
    . apply twist_untwist.symm
    apply trans exch.symm
    apply trans; apply cat₀; .
      apply trans (cat_wires (n := (a + n + b))).symm
      apply cat₁
      apply trans (wires_mix_wires (a := a + n) (b := b)).symm
      apply trans; apply mix_
      . apply twist_untwist.symm
      . apply (cat_wires (n := b)).symm; simp
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc
    apply trans (cat₁ cat_assoc)
    apply trans cat_assoc.symm
    apply cat₀ twist_add_n.symm
    repeat simp
  simp
  apply trans cat_assoc.symm
  apply trans (cat₀ twist_untwist)
  apply wires_cat
  repeat simp

def twist_2_1 : EqN S # (twist 2 1) (cat # (mix wire swap) (mix swap wire)) := by
  apply trans (twist_add_n (a := 1) (b := 1))
  apply cat_
  . apply mix_
    . apply wires₁
    . apply twist_1_1
  . apply mix_
    . apply twist_1_1
    . apply wires₁

def twist_1_2 : EqN S # (twist 1 2) (cat # (mix swap wire) (mix wire swap)) := by
  apply trans (twist_n_add (a := 1) (b := 1))
  apply cat_
  . apply mix_
    . apply twist_1_1
    . apply wires₁
  . apply mix_
    . apply wires₁
    . apply twist_1_1
