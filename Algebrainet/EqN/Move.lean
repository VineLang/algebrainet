import Algebrainet.Net
import Algebrainet.EqN.Twist

open Net
namespace EqN

variable {S : System}

set_option autoImplicit false

def twist_net_wire
  {aᵢ aₒ: Nat}
  {A : Net S aᵢ aₒ}
: EqN S #
  (cat # (mix A wire) (twist aₒ 1))
  (cat # (twist aᵢ 1) (mix wire A))
:= by
  match A with
  | nil =>
    apply trans
    . apply trans (cat₀ nil_mix) wire_cat; simp
    . apply symm (trans (cat₁ mix_nil) cat_wire); simp
  | wire =>
    apply trans
    . apply trans (cat₀ wires₂.symm) wires_cat; simp
    . apply trans (cat_wires.symm) (cat₁ wires₂); simp
  | swap =>
    apply trans (cat₁ twist_2_1)
    apply trans move_swap.symm
    apply trans cat_assoc.symm
    apply cat₀ twist_2_1.symm
    repeat simp
  | cup =>
    apply trans (cat₁ twist_2_1)
    apply trans cat_assoc.symm
    apply trans (cat₀ move_cup)
    apply trans cat_assoc
    apply trans; apply cat₁; .
      apply trans exch
      apply mix_
      . apply trans swap_swap
        apply wires₂.symm
      . apply wire_cat
      repeat simp
    simp
    apply trans cat_wires
    apply symm
    apply trans (cat₀ cast_)
    apply wires_cat
    repeat simp
  | cap =>
    apply symm
    apply trans (cat₀ twist_2_1)
    apply trans cat_assoc
    apply trans (cat₁ move_cap.symm)
    apply trans cat_assoc.symm
    apply trans; apply cat₀; .
      apply trans exch
      apply mix_
      . apply wire_cat
      . apply trans swap_swap
        apply wires₂.symm
      repeat simp
    simp
    apply trans (cat₀ wire_mix_wires)
    apply trans wires_cat
    apply symm
    apply trans (cat₁ cast_)
    apply cat_wires
    repeat simp
  | cat rfl X Y =>
    apply trans; apply cat₀; .
      apply trans (mix₁ wire_cat.symm)
      apply exch.symm
      repeat simp [*]
    simp
    apply trans cat_assoc
    apply trans (cat₁ twist_net_wire)
    apply trans cat_assoc.symm
    apply trans (cat₀ twist_net_wire)
    apply trans cat_assoc
    apply cat₁
    apply trans exch
    apply mix₀
    apply cat_wire
    repeat simp
  | mix X Y =>
    rename_i i₁ i₂ o₁ o₂
    apply trans; apply cat_
    . apply trans; apply mix_
      . apply down_up
      . apply cat_wire.symm; simp
      apply exch.symm
      repeat simp
    . apply twist_add_n
    simp
    apply trans cat_assoc
    apply trans; apply cat₁; .
      apply trans cat_assoc.symm
      apply trans; apply cat₀; .
        apply trans (cat₀ mix_assoc)
        apply trans exch
        apply trans (mix₁ twist_net_wire)
        apply exch.symm
        repeat simp
      simp
      apply cat_assoc
      repeat simp
    simp
    apply trans cat_assoc.symm
    apply trans; apply cat_
    . apply trans (cat₀ mix_assoc)
      apply trans down_up.symm up_down
      simp
    . apply trans (cat₀ mix_assoc.symm)
      apply trans up_down.symm down_up
    simp
    apply trans cat_assoc
    apply trans; apply cat₁; .
      apply trans cat_assoc.symm
      apply trans; apply cat₀; .
        apply trans; apply cat₀; .
          apply trans (mix₁ (wire_mix_wires_ (a := i₂)).symm)
          apply mix_assoc.symm
          simp
        simp
        apply trans exch
        apply trans (mix₀ twist_net_wire)
        apply exch.symm
        repeat simp
      simp
      apply cat_assoc
      repeat simp
    simp
    apply trans cat_assoc.symm
    apply cat_
    . apply twist_add_n.symm
    . apply trans; apply cat_
      . apply mix_assoc
      . apply trans (mix₀ (wire_mix_wires_ (a := o₁)).symm)
        apply mix_assoc
        simp
      simp
      apply trans exch
      apply mix_
      . apply cat_wire
      . apply down_up.symm
      simp
    repeat simp
  | agent _ =>
    apply trans (cat₁ twist_1_1)
    apply move_agent

def twist_net_wires
  {aᵢ aₒ b : Nat}
  {A : Net S aᵢ aₒ}
: EqN S #
  (cat # (mix A (wires b)) (twist aₒ b))
  (cat # (twist aᵢ b) (mix (wires b) A))
:= by
  induction b with
  | zero =>
    apply trans
    . apply trans (cat_ mix_nil twist_n_0)
      apply cat_wires
      simp
    . apply symm
      apply trans (cat_ twist_n_0 nil_mix)
      apply wires_cat
      simp
  | succ b ih =>
    apply trans (cat_ mix_assoc.symm twist_n_s)
    apply trans cat_assoc.symm
    apply trans; apply cat₀; .
      apply trans exch
      apply trans (mix₀ ih)
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc
    apply trans; apply cat₁; .
      apply trans (cat₀ mix_assoc)
      apply trans exch
      apply trans (mix₁ twist_net_wire)
      apply exch.symm
      repeat simp
    simp
    apply trans cat_assoc.symm
    apply cat_ twist_n_s.symm mix_assoc.symm
    repeat simp

def twist_wires_net
  {a bᵢ bₒ : Nat} {B : Net S bᵢ bₒ}
  : EqN S #
    (cat # (mix (wires a) B) (twist a bₒ))
    (cat # (twist a bᵢ) (mix B (wires a)))
:= by
  apply trans (symm (wires_cat (n := a + bᵢ)))
  apply trans (cat₀ twist_untwist.symm)
  apply trans cat_assoc.symm
  apply trans; apply cat₀; .
    apply trans cat_assoc
    apply cat₁ (twist_net_wires (A := B) (b := a)).symm
    repeat simp
  simp
  apply trans cat_assoc
  apply cat₁
  apply trans cat_assoc
  apply trans (cat₁ twist_untwist)
  apply cat_wires
  repeat simp

def twist_nets
  {aᵢ aₒ : Nat} {A : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {B : Net S bᵢ bₒ}
  : EqN S #
    (cat # (mix A B) (twist aₒ bₒ))
    (cat # (twist aᵢ bᵢ) (mix B A))
:= by
  apply trans
  apply cat₀ up_down; simp
  apply trans cat_assoc
  apply trans; apply cat₁ twist_net_wires; repeat simp
  apply trans (symm cat_assoc)
  apply trans; apply cat₀ twist_wires_net; repeat simp
  apply trans cat_assoc
  apply cat₁ (symm down_up)
  repeat simp

def cap_cup : EqN S # (cat # (mix wire cup) (mix cap wire)) wire := by
  apply trans; apply cat₀; .
    apply trans (mix_ wire_cat.symm cup_swap.symm)
    apply exch.symm
    repeat simp
  simp
  apply trans cat_assoc
  apply trans (cat₁ move_cap)
  apply trans cat_assoc.symm
  apply trans (cat₀ move_cup.symm)
  apply trans cat_assoc
  apply trans; apply cat₁; .
    apply trans exch
    apply (mix_ wire_cat swap_cap)
    repeat simp
  simp
  apply cup_cap
  repeat simp
