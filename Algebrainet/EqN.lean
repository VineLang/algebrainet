import Algebrainet.Net

open Net

inductive EqA (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | mix_nil :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqA S # (mix x nil) x
  | nil_mix :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    EqA S # (mix nil x) x
  | mix_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    EqA S # (mix (mix x y) z) (mix x (mix y z))

  | cat_wires :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqA S # (cat h x (wires n)) x
  | wires_cat :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    EqA S # (cat h (wires n) x) x
  | cat_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₀ h₁ h₂ h₃ : _} ->
    EqA S # (cat h₀ (cat h₁ x y) z) (cat h₂ x (cat h₃ y z))

  | swap_swap : EqA S # (cat # swap swap) (mix wire wire)
  | cup_swap : EqA S # (cat # cup swap) cup
  | swap_cap : EqA S # (cat # swap cap) cap

  | move_cup : EqA S # (cat # (mix cup wire) (mix wire swap)) (cat # (mix wire cup) (mix swap wire))
  | move_cap : EqA S # (cat # (mix wire swap) (mix cap wire)) (cat # (mix swap wire) (mix wire cap))
  | move_swap : EqA S # (cat # (mix wire swap) (cat # (mix swap wire) (mix wire swap))) (cat # (mix swap wire) (cat # (mix wire swap) (mix swap wire)))
  | move_agent {A : S.Agent} : EqA S # (cat # ((agent A).mix wire) swap) (cat # (twist (S.arity A) 1) (wire.mix (agent A)))

  | cup_cap : EqA S # (cat # (mix cup wire) (mix wire cap)) wire

  | exch :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {wᵢ wₒ : Nat} -> {w : Net S wᵢ wₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqA S # (cat h₀ (mix x y) (mix z w)) (mix (cat h₁ x z) (cat h₂ y w))

  | cat₀ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqA S h₀ a b ->
    EqA S # (cat h₁ a c) (cat h₂ b c)

  | cat₁ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ h₂ : _} ->
    EqA S h₀ a b ->
    EqA S # (cat h₁ c a) (cat h₂ c b)

  | mix₀ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    EqA S h a b ->
    EqA S # (mix a c) (mix b c)

  | mix₁ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    EqA S h a b ->
    EqA S # (mix c a) (mix c b)

inductive EqN (S : System) : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Prop
  | refl : {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} -> EqN S # x x
  | fw :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqA S h₀ a b -> EqN S h₁ b c ->
    EqN S # a c
  | bk :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h₀ h₁ : _} -> EqA S h₀ b a -> EqN S h₁ b c ->
    EqN S (by rcases h₀ with ⟨⟨⟩,⟨⟩⟩; simp [*]) a c

namespace EqN

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}
  {n : Nat}

def cast_ {i₁ o₁ i₂ o₂ : Nat} {x : Net S i₁ o₁} :
  {h : (i₁ = i₂) ∧ (o₁ = o₂)} -> EqN S # (castₙ h x) x
  | (And.intro rfl rfl) => refl

def trans {h₀ h₁ : _} (e : EqN S h₀ a b) (f : EqN S h₁ b c) : EqN S # a c := by
  induction e with
  | refl => exact f
  | fw a _ ih => exact fw a (ih f)
  | bk a _ ih => exact bk a (ih f)

def symm {h : _} (e : EqN S h a b) : EqN S # b a := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact trans ih (bk a refl)
  | bk a _ ih => exact trans ih (fw a refl)

def cat₀ {h₀ : _} (e : EqN S h₀ a b) {h₁ h₂ : _} : EqN S # (cat h₁ a c) (cat h₂ b c) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (b := (cat # _ _)) (.cat₀ a) ih
  | bk a _ ih => exact bk (b := (cat # _ _)) (.cat₀ a) ih

def cat₁ {h₀ : _} (e : EqN S h₀ a b) {h₁ h₂ : _} : EqN S # (cat h₁ c a) (cat h₂ c b) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (b := (cat # _ _)) (.cat₁ a) ih
  | bk a _ ih => exact bk (b := (cat # _ _)) (.cat₁ a) ih

def mix₀ {h : _} (e : EqN S h a b) : EqN S # (mix a c) (mix b c) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (.mix₀ a) ih
  | bk a _ ih => exact bk (.mix₀ a) ih

def mix₁ {h : _} (e : EqN S h a b) : EqN S # (mix c a) (mix c b) := by
  induction e with
  | refl => exact refl
  | fw a _ ih => exact fw (.mix₁ a) ih
  | bk a _ ih => exact bk (.mix₁ a) ih

def cat_ {h₀ h₁ : _} (e : EqN S h₀ a b) (f : EqN S h₁ c d) {h₁ h₂ : _} : EqN S # (cat h₁ a c) (cat h₂ b d) := by
  apply trans (cat₀ e) (cat₁ f); simp [*]

def mix_ {h₀ h₁ : _} (e : EqN S h₀ a b) (f : EqN S h₁ c d) : EqN S # (mix a c) (mix b d) :=
  trans (mix₀ e) (mix₁ f)

def mix_nil : EqN S # (mix a nil) a := fw .mix_nil refl
def nil_mix : EqN S # (mix nil a) a := fw .nil_mix refl
def mix_assoc : EqN S # (mix (mix a b) c) (mix a (mix b c)) := fw .mix_assoc refl

def cat_wires {h : _} : EqN S # (cat h a (wires n)) a := fw .cat_wires refl
def wires_cat {h : _} : EqN S # (cat h (wires n) a) a := fw .wires_cat refl
def cat_assoc {h₀ h₁ h₂ h₃ : _} : EqN S # (cat h₀ (cat h₁ a b) c) (cat h₂ a (cat h₃ b c)) := fw .cat_assoc refl

def swap_swap : EqN S # (cat # swap swap) (mix wire wire) := fw .swap_swap refl
def cup_swap : EqN S # (cat # cup swap) cup := fw .cup_swap refl
def swap_cap : EqN S # (cat # swap cap) cap := fw .swap_cap refl

def move_cup : EqN S # (cat # (mix cup wire) (mix wire swap)) (cat # (mix wire cup) (mix swap wire)) := fw .move_cup refl
def move_cap : EqN S # (cat # (mix wire swap) (mix cap wire)) (cat # (mix swap wire) (mix wire cap)) := fw .move_cap refl
def move_swap : EqN S # (cat # (mix wire swap) (cat # (mix swap wire) (mix wire swap))) (cat # (mix swap wire) (cat # (mix wire swap) (mix swap wire))) := fw .move_swap refl
def move_agent {A : S.Agent} : EqN S # (cat # ((agent A).mix wire) swap) (cat # (twist (S.arity A) 1) (wire.mix (agent A))) := fw .move_agent refl

def cup_cap : EqN S # (cat # (mix cup wire) (mix wire cap)) wire := fw .cup_cap refl

def exch {h₀ h₁ h₂ : _} : EqN S # (cat h₀ (mix x y) (mix z w)) (mix (cat h₁ x z) (cat h₂ y w)) := fw .exch refl
