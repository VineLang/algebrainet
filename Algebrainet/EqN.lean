import Algebrainet.Net

open Net

inductive EqN (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Type
  | refl :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqN S # x x
  | trans :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₀ h₁ : _} -> EqN S h₀ x y -> EqN S h₁ y z ->
    EqN S # x z
  | symm :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {h : _} -> EqN S h x y ->
    EqN S # y x

  | cast_ :
    {i₁ o₁ i₂ o₂ : Nat} -> {x : Net S i₁ o₁} ->
    {h : (i₁ = i₂) ∧ (o₁ = o₂)} ->
    EqN S # (.cast h x) x

  | mix_nil :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqN S # (mix x nil) x
  | nil_mix :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqN S # (mix nil x) x
  | mix_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    EqN S # (mix (mix x y) z) (mix x (mix y z))

  | cat_wires :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqN S # (cat h x (wires n)) x
  | wires_cat :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqN S # (cat h (wires n) x) x
  | cat_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₀ h₁ h₂ h₃ : _} ->
    EqN S # (cat h₀ (cat h₁ x y) z) (cat h₂ x (cat h₃ y z))

  | swap_swap : EqN S # (cat # swap swap) (mix wire wire)
  | untwist_cup : EqN S # (cat # cup swap) cup
  | untwist_cap : EqN S # (cat # swap cap) cap

  | cup_swap : EqN S # (cat # (mix cup wire) (mix wire swap)) (cat # (mix wire cup) (mix swap wire))
  | cap_swap : EqN S # (cat # (mix wire swap) (mix cap wire)) (cat # (mix swap wire) (mix wire cap))

  | mix_twist :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    EqN S # (cat # (mix x y) (twist xₒ yₒ)) (cat # (twist xᵢ yᵢ) (mix y x))

  | cup_cap : EqN S # (cat # (mix cup wire) (mix wire cap)) wire

  | exch :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {wᵢ wₒ : Nat} -> {w : Net S wᵢ wₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqN S # (cat h₀ (mix x y) (mix z w)) (mix (cat h₁ x z) (cat h₂ y w))

  | cat_ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {dᵢ dₒ : Nat} -> {d : Net S dᵢ dₒ} ->
    {h₀ h₁ : _} ->
    EqN S h₀ a c ->
    EqN S h₁ b d ->
    {h₂ h₃ : _} ->
    EqN S # (cat h₂ a b) (cat h₃ c d)

  | mix_ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {dᵢ dₒ : Nat} -> {d : Net S dᵢ dₒ} ->
    {h₀ h₁ : _} ->
    EqN S h₀ a c ->
    EqN S h₁ b d ->
    EqN S # (mix a b) (mix c d)

namespace EqN

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}

def cat₀ {h₀ : _} (e : EqN S h₀ a b) {h₁ h₂ : _} : EqN S # (cat h₁ a c) (cat h₂ b c) := cat_ e refl
def cat₁ {h₀ : _} (e : EqN S h₀ a b) {h₁ h₂ : _} : EqN S # (cat h₁ c a) (cat h₂ c b) := cat_ refl e
def mix₀ {h : _} (e : EqN S h a b) : EqN S # (mix a c) (mix b c) := mix_ e refl
def mix₁ {h : _} (e : EqN S h a b) : EqN S # (mix c a) (mix c b) := mix_ refl e
