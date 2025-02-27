import Algebrainet.Net
import Algebrainet.EqN

open Net

set_option autoImplicit false

structure Rules (S : System) where
  defined : S.Agent -> S.Agent -> Prop
  defined_symm : {a b : S.Agent} -> defined a b -> defined b a
  rule : {a b : S.Agent} -> defined a b -> Net S ((S.arity a) + (S.arity b)) 0
  rule_symm : {a b : S.Agent} -> (d : defined a b) -> EqN S # (rule d) (rule (defined_symm d))


def pair {S : System} (a b : S.Agent) : Net S ((S.arity a) + (S.arity b)) 0 :=
  cat # (mix (agent a) (agent b)) cap

inductive Rd (S : System) (R : Rules S) : {i o : Nat} -> (x y : Net S i o) -> Prop
  | pair : (a b : S.Agent) -> (d : R.defined a b) -> Rd S R (pair a b) (R.rule d)
  | cat₀ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    Rd S R (cat h a c) (cat h b c)
  | cat₁ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {h : _} ->
    Rd S R (cat h c a) (cat h c b)
  | mix₀ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    Rd S R (mix a c) (mix b c)
  | mix₁ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    Rd S R (mix c a) (mix c b)

variable {S : System} {R : Rules S}

abbrev vee (R : Rules S) {i o : Nat} (b c : Net S i o) : Prop :=
  b = c ∨ ∃ (d : Net S i o), Rd S R b d ∧ Rd S R c d

def make_heq {α : Type} {a b : α} : a = b -> HEq a b
  | rfl => .rfl

-- set_option pp.explicit true

def pair_eq : {a b c d : S.Agent} -> HEq (pair a b) (pair c d) -> a = c ∧ b = d := sorry

def rd_perf_conf3 {S : System} {R : Rules S}
  {i₀ o₀ : Nat} {a₀ b : Net S i₀ o₀} (r₀ : Rd S R a₀ b)
  {i₁ o₁ : Nat} {a₁ c : Net S i₁ o₁} (r₁ : Rd S R a₁ c)
  {hᵢ : i₀ = i₁} {hₒ : o₀ = o₁} {hₐ : HEq a₀ a₁}
  : vee R b (cast # c)
:= by
  cases r₀ with
  | pair x₀ y₀ d₀ =>
    cases r₁ with
    | pair x₁ y₁ d₁ =>
      obtain ⟨⟨⟩, ⟨⟩⟩ := pair_eq hₐ






      repeat sorry
    | _ => sorry
  | _ => sorry

def make_copy {α : Type} {β : Prop} (a : α) {f : (b : α) -> a = b -> β} : β := f a rfl

def rd_perf_conf2 {S : System} {R : Rules S}
  {i o : Nat} {a b c : Net S i o}
  (r₀ : Rd S R a b) (r₁ : Rd S R a c)
  : vee R b c
:= by
  apply make_copy a; intro a' ha
  apply make_copy c; intro c' hc
  rw [ha, hc] at r₁
  replace ha := ()
  replace hc := ()
  apply make_copy i; intro i' hi
  rw [hi] at a' c'








  -- generalize a = a' at r₁
  -- generalize c = c'
  -- generalize hi : i = i' at a b c' r₀


  cases r₀ with
  | pair x y d =>

    -- generalize h₀ : (pair x y) = a at *
    -- generalize (R.rule d) = b at *
    -- replace h₀ := make_heq h₀
    -- let foo := ∀ (wee : Nat) {c : Net S wee 0} (a : Net S wee 0), Rd S R a c → ∀ (b : Net S wee 0), HEq (pair x y) a → vee R b c
    -- replace h₁ := make_heq h₁
    -- generalize (S.arity x + S.arity y) = wee at *

    repeat sorry
  | _ => sorry



def rd_perf_conf {S : System} {R : Rules S}
  {i o : Nat} {a b c : Net S i o}
  (r₀ : Rd S R a b) (r₁ : Rd S R a c)
  : vee R b c
:= (
  Rd.rec (S := S) (R := R) (motive := fun {i} {o} a b _ => ({c : Net S i o} -> Rd S R a c -> vee R b c))
  (fun a b => by

    sorry
  )
  sorry
  sorry
  sorry
  sorry
  r₀ r₁
)
