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
  -- | wires_agent : {a : S.Agent} -> EqvA S # (cat # (wires (S.arity a)) (agent a)) (agent a)

  | cat_wires :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqvA S # (cat h x (wires n)) x
  | wires_cat :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqvA S # (cat h (wires n) x) x
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

  | cat₀ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqvA S h₀ a b ->
    EqvA S # (cat h₁ a c) (cat h₂ b c)

  | cat₁ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqvA S h₀ a b ->
    EqvA S # (cat h₁ c a) (cat h₂ c b)

  | mix₀ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    EqvA S h a b ->
    EqvA S # (mix a c) (mix b c)

  | mix₁ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    EqvA S h a b ->
    EqvA S # (mix c a) (mix c b)

inductive EqvF (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | refl : {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} -> EqvF S # x x
  | apply :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqvA S h₀ a b -> EqvF S h₁ b c ->
    EqvF S # a c

inductive EqvN (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | mk :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqvF S h₀ a c -> EqvF S h₁ b c ->
    EqvN S # a b

inductive Eqv (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | refl : {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} -> Eqv S # x x
  | fw :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqvA S h₀ a b -> Eqv S h₁ b c ->
    Eqv S # a c
  | bk :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqvA S h₀ b a -> Eqv S h₁ b c ->
    Eqv S (by rcases h₀ with ⟨⟨⟩,⟨⟩⟩; simp [*]) a c

namespace Eqv

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}
  {n : Nat}

def cast_ {i₁ o₁ i₂ o₂ : Nat} {x : Net S i₁ o₁} :
  {h : (i₁ = i₂) ∧ (o₁ = o₂)} -> Eqv S # (castₙ h x) x
  | (And.intro rfl rfl) => refl

def trans {h₀ h₁ : _} (e : Eqv S h₀ a b) (f : Eqv S h₁ b c) : Eqv S # a c := by
  induction e with
  | refl => exact f
  | fw a _ ih => exact fw a (ih f)
  | bk a _ ih => exact bk a (ih f)

def symm {h : _} (e : Eqv S h a b) : Eqv S # b a := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact trans ih (bk a refl)
  | bk a _ ih => exact trans ih (fw a refl)

def cat₀ {h₀ : _} (e : Eqv S h₀ a b) {h₁ h₂ : _} : Eqv S # (cat h₁ a c) (cat h₂ b c) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (b := (cat # _ _)) (.cat₀ a) ih
  | bk a _ ih => exact bk (b := (cat # _ _)) (.cat₀ a) ih

def cat₁ {h₀ : _} (e : Eqv S h₀ a b) {h₁ h₂ : _} : Eqv S # (cat h₁ c a) (cat h₂ c b) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (b := (cat # _ _)) (.cat₁ a) ih
  | bk a _ ih => exact bk (b := (cat # _ _)) (.cat₁ a) ih

def mix₀ {h : _} (e : Eqv S h a b) : Eqv S # (mix a c) (mix b c) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (.mix₀ a) ih
  | bk a _ ih => exact bk (.mix₀ a) ih

def mix₁ {h : _} (e : Eqv S h a b) : Eqv S # (mix c a) (mix c b) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (.mix₁ a) ih
  | bk a _ ih => exact bk (.mix₁ a) ih

def cat_ {h₀ h₁ : _} (e : Eqv S h₀ a b) (f : Eqv S h₁ c d) {h₁ h₂ : _} : Eqv S # (cat h₁ a c) (cat h₂ b d) := by
  apply trans (cat₀ e) (cat₁ f); simp [*]

def mix_ {h₀ h₁ : _} (e : Eqv S h₀ a b) (f : Eqv S h₁ c d) : Eqv S # (mix a c) (mix b d) :=
  trans (mix₀ e) (mix₁ f)

-- def mix_nil : Eqv S # (mix a nil) a := fw .mix_nil refl
-- def nil_mix : Eqv S # (mix nil a) a := fw .nil_mix refl
-- def mix_assoc : Eqv S # (mix (mix a b) c) (mix a (mix b c)) := fw .mix_assoc refl

-- def cat_wires {h : _} : Eqv S # (cat h a (wires n)) a := fw .cat_wires refl
-- def wires_cat {h : _} : Eqv S # (cat h (wires n) a) a := fw .wires_cat refl
-- def cat_assoc {h₀ h₁ h₂ h₃ : _} : Eqv S # (cat h₀ (cat h₁ a b) c) (cat h₂ a (cat h₃ b c)) := fw .cat_assoc refl

-- def swap_swap : Eqv S # (cat # swap swap) (mix wire wire) := fw .swap_swap refl
-- def cup_swap : Eqv S # (cat # cup swap) cup := fw .cup_swap refl
-- def swap_cap : Eqv S # (cat # swap cap) cap := fw .swap_cap refl

-- def move_cup : Eqv S # (cat # (mix cup wire) (mix wire swap)) (cat # (mix wire cup) (mix swap wire)) := fw .move_cup refl
-- def move_cap : Eqv S # (cat # (mix wire swap) (mix cap wire)) (cat # (mix swap wire) (mix wire cap)) := fw .move_cap refl
-- def move_swap : Eqv S # (cat # (mix wire swap) (cat # (mix swap wire) (mix wire swap))) (cat # (mix swap wire) (cat # (mix wire swap) (mix swap wire))) := fw .move_swap refl
-- def move_agent {A : S.Agent} : Eqv S # (cat # ((agent A).mix wire) swap) (cat # (twist (S.arity A) 1) (wire.mix (agent A))) := fw .move_agent refl

-- def cup_cap : Eqv S # (cat # (mix cup wire) (mix wire cap)) wire := fw .cup_cap refl

-- def exch {h₀ h₁ h₂ : _} : Eqv S # (cat h₀ (mix x y) (mix z w)) (mix (cat h₁ x z) (cat h₂ y w)) := fw .exch refl

end Eqv

namespace EqvN

def cat₀ {h₀ : _} (e : EqvN S h₀ a b) {h₁ h₂ : _} : EqvN S # (cat h₁ a c) (cat h₂ b c) := sorry
def cat₁ {h₀ : _} (e : EqvN S h₀ a b) {h₁ h₂ : _} : EqvN S # (cat h₁ c a) (cat h₂ c b) := sorry
def mix₀ {h : _} (e : EqvN S h a b) : EqvN S # (mix a c) (mix b c) := sorry
def mix₁ {h : _} (e : EqvN S h a b) : EqvN S # (mix c a) (mix c b) := sorry
def symm {h : _} (e : EqvN S h a b) : EqvN S # b a := by sorry
