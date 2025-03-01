import Algebrainet.Net

open Net

inductive EqvA (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | mix_nil :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqvA S # (mix x nil) x
  | nil_mix :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqvA S # (mix nil x) x
  | mix_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    EqvA S # (mix (mix x y) z) (mix x (mix y z))
  | mix_unassoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    EqvA S # (mix x (mix y z)) (mix (mix x y) z)

  -- | wire_cat_wire: EqvA S # (cat # wire wire) wire
  -- | cat_nil :
  --   {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
  --   {h : _} ->
  --   EqvA S # (cat h x nil) x
  -- | nil_cat :
  --   {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
  --   {h : _} ->
  --   EqvA S # (cat h nil x) x
  -- | swap_wires : EqvA S # (cat # swap (mix wire wire)) swap
  -- | wires_swap : EqvA S # (cat # (mix wire wire) swap) swap
  -- | wires_cap : EqvA S # (cat # (mix wire wire) cap) cap
  -- | cup_wires : EqvA S # (cat # cup (mix wire wire)) cup
  -- | agent_wire : {a : S.Agent} -> EqvA S # (cat # (agent a) wire) (agent a)
  -- | wires_agent : {a : S.Agent} -> EqvA S # (cat # (wires_ (S.arity a)) (agent a)) (agent a)

  | cat_wires :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqvA S # (cat h x (wires_ n)) x
  | wires_cat :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqvA S # (cat h (wires_ n) x) x

  | cat_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₀ h₁ h₂ h₃ : _} ->
    EqvA S # (cat h₀ (cat h₁ x y) z) (cat h₂ x (cat h₃ y z))

  | swap_swap : EqvA S # (cat # swap swap) (mix wire wire)
  | cup_swap : EqvA S # (cat # cup swap) cup
  | swap_cap : EqvA S # (cat # swap cap) cap

  | move_cup : EqvA S # (cat # (mix cup wire) (mix wire swap)) (cat # (mix wire cup) (mix swap wire))
  | move_cap : EqvA S # (cat # (mix wire swap) (mix cap wire)) (cat # (mix swap wire) (mix wire cap))
  | move_swap : EqvA S # (cat # (mix wire swap) (cat # (mix swap wire) (mix wire swap))) (cat # (mix swap wire) (cat # (mix wire swap) (mix swap wire)))
  | move_agent {A : S.Agent} : EqvA S # (cat # ((agent A).mix wire) swap) (cat # (twist (S.arity A) 1) (wire.mix (agent A)))

  | cup_cap : EqvA S # (cat # (mix cup wire) (mix wire cap)) wire

  | exch :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {wᵢ wₒ : Nat} -> {w : Net S wᵢ wₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqvA S # (cat h₀ (mix x y) (mix z w)) (mix (cat h₁ x z) (cat h₂ y w))

  | unexch :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {wᵢ wₒ : Nat} -> {w : Net S wᵢ wₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqvA S # (mix (cat h₁ x z) (cat h₂ y w)) (cat h₀ (mix x y) (mix z w))

inductive EqvB (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | atom :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {h : _} -> EqvA S h a b ->
    EqvB S h a b

  | cat₀ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqvB S h₀ a b ->
    EqvB S # (cat h₁ a c) (cat h₂ b c)

  | cat₁ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqvB S h₀ a b ->
    EqvB S # (cat h₁ c a) (cat h₂ c b)

  | mix₀ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    EqvB S h a b ->
    EqvB S # (mix a c) (mix b c)

  | mix₁ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    EqvB S h a b ->
    EqvB S # (mix c a) (mix c b)

inductive EqvF (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | refl : {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} -> EqvF S # x x
  | apply :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqvB S h₀ a b -> EqvF S h₁ b c ->
    EqvF S # a c

inductive Eqv (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | mk :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqvF S h₀ a c -> EqvF S h₁ b c ->
    Eqv S # a b

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}
  {n : Nat}

namespace Eqv

def cat₀ {h₀ : _} (e : Eqv S h₀ a b) {h₁ h₂ : _} : Eqv S # (cat h₁ a c) (cat h₂ b c) := sorry
def cat₁ {h₀ : _} (e : Eqv S h₀ a b) {h₁ h₂ : _} : Eqv S # (cat h₁ c a) (cat h₂ c b) := sorry
def mix₀ {h : _} (e : Eqv S h a b) : Eqv S # (mix a c) (mix b c) := sorry
def mix₁ {h : _} (e : Eqv S h a b) : Eqv S # (mix c a) (mix c b) := sorry
def symm {h : _} (e : Eqv S h a b) : Eqv S # b a := by sorry
