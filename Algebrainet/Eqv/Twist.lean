import Algebrainet.Eqv
import Algebrainet.Eqv.Wires

namespace Eqv
open Net

variable {S : System} {n a b : Nat}
set_option autoImplicit false

def twist₁_1 : Eqv S # (twist₁ 1) swap := by
  apply trans cast_
  apply trans; apply cat_
  . apply wires₂.symm
  . apply nil_mix
  simp
  apply wires_cat

def twist_1_n : Eqv S # (twist 1 n) (twist₁ n) := by
  apply trans cast_
  apply trans; apply cat_
  . apply trans (mix₁ cast_) wire_mix_wires
  . apply mix_nil
  simp
  apply wires_cat

def twist_1_1 : Eqv S # (twist 1 1) swap := trans twist_1_n twist₁_1

def twist₁_succ : Eqv S # (twist₁ (n + 1)) (cat # (mix swap (wires n)) (mix wire (twist₁ n))) := by
  induction n with
  | zero =>
    apply trans twist₁_1
    apply symm
    apply trans (cat_ mix_nil wires₂.symm)
    apply cat_wires
    simp
  | succ n ih =>
    apply trans cast_
    apply trans; apply cat₀; .
      apply trans (mix_ ih wire_cat.symm)
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc
    apply cat_
    . apply mix_assoc
    . apply trans; apply cat_
      . apply mix_assoc
      . apply trans; apply mix₀; .
          apply trans (wires_mix_wires_ (a := 1) (b := n)).symm
          apply mix₀ wires₁
          simp
        apply mix_assoc
      simp
      apply trans exch
      apply mix_ wire_cat cast_.symm
      repeat simp
    repeat simp

abbrev untwist₁ (n : Nat) : Net S (n + 1) (1 + n) := twist n 1

def untwist₁_succ : Eqv S # (untwist₁ (n + 1)) (cat # (mix (wires n) swap) (mix (untwist₁ n) wire)) := by
  induction n with
  | zero =>
    apply trans cast_
    apply trans; apply cat_
    . apply trans (mix₁ cast_)
      apply wire_mix_wires
    . apply trans mix_nil twist₁_1
    simp
    apply trans wires_cat
    apply symm
    apply trans (cat_ nil_mix (mix₀ cast_))
    apply cat_wires
    simp
  | succ n ih =>
    apply trans cast_
    apply trans; apply cat₀; .
      apply trans (mix_ cat_wire.symm ih)
      apply trans exch.symm
      apply cat₀ mix_assoc.symm
      repeat simp
    simp
    apply trans cat_assoc
    apply cat_
    . apply mix₀ wire_mix_wires
    . apply trans (cat_ mix_assoc.symm mix_assoc.symm)
      apply trans exch
      apply mix_ cast_.symm wire_cat
      repeat simp
    simp

def twist₁_untwist₁ : Eqv S # (cat # (twist₁ n) (untwist₁ n)) (wires (n + 1)) := by
  induction n with
  | zero => apply trans wire_cat cast_
  | succ n ih =>
    apply trans (cat_ cast_ untwist₁_succ)
    apply trans cat_assoc
    apply trans; apply cat₁; .
      apply trans cat_assoc.symm
      apply trans; apply cat₀; .
        apply trans exch
        apply trans (mix_ wires_cat swap_swap)
        apply trans (mix₁ wires₂.symm)
        apply wires_mix_wires
        repeat simp
      simp
      apply wires_cat
      repeat simp
    simp
    apply trans exch
    apply mix_ ih wire_cat
    repeat simp

def twist_n_0 : Eqv S # (twist n 0) (wires n) := by
  induction n with
  | zero => apply cast_
  | succ n ih =>
    apply trans cast_
    apply trans; apply cat_
    . apply trans (mix₁ ih)
      apply wire_mix_wires
    . apply wire_mix_wires
    simp
    apply wires_cat

def twist_s_n : Eqv S # (twist (a + 1) b) (cat # (mix (wires a) (twist₁ b)) (mix (twist a b) wire)) := by
  induction a with
  | zero =>
    apply trans cast_
    apply trans; apply cat_
    . apply trans (mix₁ cast_)
      apply wire_mix_wires
    . apply mix_nil
    simp
    apply trans wires_cat
    apply symm
    apply trans (cat_ nil_mix (mix₀ cast_))
    apply cat_wires
    simp
  | succ a ih =>
    apply trans cast_
    apply trans; apply cat₀
    . apply trans (mix_ wire_cat.symm ih)
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc
    apply cat_
    . apply trans mix_assoc.symm
      apply mix₀ wire_mix_wires
    . apply trans (cat_ mix_assoc.symm mix_assoc.symm)
      apply trans exch
      apply mix_ cast_.symm wire_cat
      repeat simp
    simp

def twist_n_s : Eqv S # (twist a (b + 1)) (cat # (mix (twist a b) wire) (mix (wires b) (untwist₁ a))) := by
  induction a with
  | zero =>
    apply trans cast_
    apply symm
    apply trans; apply cat_
    . apply mix₀ cast_
    . apply trans (mix₁ cast_)
      apply wires_mix_wires
    simp
    apply wires_cat
  | succ a ih =>
    apply trans twist_s_n
    apply trans; apply cat₁; .
      apply trans (mix_ ih wire_cat.symm)
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc.symm
    apply trans; apply cat₀; .
      apply trans; apply cat_
      . apply trans (mix_ (wires_cat (n := a)).symm cast_)
        apply trans exch.symm
        apply cat₁
        apply trans mix_assoc.symm
        apply mix₀ wires_mix_wires
        repeat simp
      . apply mix_assoc
      simp
      apply trans cat_assoc
      apply trans; apply cat₁; .
        apply trans (cat₁ (mix₁ wires₂.symm))
        apply trans up_down.symm down_up
        simp
      simp
      apply trans cat_assoc.symm
      apply cat₀
      apply trans (cat_ mix_assoc.symm (mix_assoc (c := wire)).symm)
      apply trans exch
      apply mix_
      . apply trans (cat₁ (mix₁ wires₁))
        apply twist_s_n.symm
        simp
      . apply wire_cat
      repeat simp
    simp
    apply trans cat_assoc
    apply cat₁
    apply trans (cat₀ (mix₀ (wires_mix_wires_ (a := b) (b := a)).symm))
    apply trans (cat_ mix_assoc mix_assoc)
    apply trans exch
    apply mix_ cat_wires untwist₁_succ.symm
    repeat simp

def twist_untwist : Eqv S # (cat # (twist a b) (twist b a)) (wires (a + b)) := by
  induction a with
  | zero =>
    apply trans (cat_ cast_ twist_n_0)
    apply trans cat_wires wires_
    repeat simp
  | succ a ih =>
    apply trans (cat_ twist_s_n twist_n_s)
    apply trans cat_assoc
    apply trans; apply cat₁; .
      apply trans cat_assoc.symm
      apply trans; apply cat₀; .
        apply trans exch
        apply mix_ ih wire_cat
        repeat simp
      simp
      apply wires_cat
      repeat simp
    simp
    apply trans exch
    apply trans (mix_ wires_cat twist₁_untwist₁)
    apply wires_mix_wires_
    repeat simp

def twist_add_n : Eqv S # (twist (a + b) n) (cat # (mix (wires a) (twist b n)) (mix (twist a n) (wires b))) := by
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

def twist_n_add : Eqv S # (twist n (a + b)) (cat # (mix (twist n a) (wires b)) (mix (wires a) (twist n b))) := by
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

def twist_2_1 : Eqv S # (twist 2 1) (cat # (mix wire swap) (mix swap wire)) := by
  apply trans (twist_add_n (a := 1) (b := 1))
  apply cat_
  . apply mix_
    . apply wires₁
    . apply twist_1_1
  . apply mix_
    . apply twist_1_1
    . apply wires₁

def twist_1_2 : Eqv S # (twist 1 2) (cat # (mix swap wire) (mix wire swap)) := by
  apply trans (twist_n_add (a := 1) (b := 1))
  apply cat_
  . apply mix_
    . apply twist_1_1
    . apply wires₁
  . apply mix_
    . apply wires₁
    . apply twist_1_1
