import Algebrainet.Net
import Algebrainet.Eqv

open Net

set_option autoImplicit false

structure Rules (S : System) where
  defined : S.Agent -> S.Agent -> Prop
  defined_symm : {a b : S.Agent} -> defined a b -> defined b a
  rule : {a b : S.Agent} -> defined a b -> Net S ((S.arity a) + (S.arity b)) 0
  rule_symm : {a b : S.Agent} -> (d : defined a b) -> Eqv S # (rule d) (rule (defined_symm d))

def pair {S : System} (a b : S.Agent) : Net S ((S.arity a) + (S.arity b)) 0 :=
  cat # (mix (agent a) (agent b)) cap

inductive Rd (S : System) (R : Rules S) : {i o : Nat} -> (x y : Net S i o) -> Prop
  | pair : (a b : S.Agent) -> (d : R.defined a b) -> Rd S R (pair a b) (R.rule d)
  | cat₀ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    Rd S R a b ->
    {h : _} ->
    Rd S R (cat h a c) (cat h b c)
  | cat₁ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    Rd S R a b ->
    {h : _} ->
    Rd S R (cat h c a) (cat h c b)
  | mix₀ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    Rd S R a b ->
    Rd S R (mix a c) (mix b c)
  | mix₁ :
    {i o : Nat} -> {a b : Net S i o} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    Rd S R a b ->
    Rd S R (mix c a) (mix c b)

variable {S : System} {R : Rules S}

inductive Vee (R : Rules S) {i o : Nat} (b c : Net S i o) : Prop
  | eq : (b = c) -> Vee R b c
  | rd : {d : Net S i o} -> Rd S R b d -> Rd S R c d -> Vee R b c

def rd_perf_conf_ {S : System} {R : Rules S}
  {i₀ o₀ i₁ o₁ : Nat}
  {a₀ b : Net S i₀ o₀} {a₁ c : Net S i₁ o₁}
  (r₀ : Rd S R a₀ b) (r₁ : Rd S R a₁ c)
  (hₐ : EqN a₀ a₁)
  : Vee R (castₙ ⟨hₐ.i, hₐ.o⟩ b) c
:= by
  induction r₀ generalizing i₁ o₁ with
  | pair x₀ y₀ d₀ =>
    cases r₁ with
    | pair x₁ y₁ d₁ =>
      cases hₐ.cat₀.mix₀.agent
      cases hₐ.cat₀.mix₁.agent
      apply Vee.eq
      simp
    | mix₀ | mix₁ => repeat cases hₐ.kind
    | cat₀ r₁ =>
      cases r₁ <;> first
      | . cases hₐ.cat₀.kind
      | . rename_i r₁ _; cases r₁ <;> first
          | . cases hₐ.cat₀.mix₀.kind
          | . cases hₐ.cat₀.mix₁.kind
    | cat₁ r₁ => cases r₁ <;> cases hₐ.cat₁.kind
  | cat₀ r₀ ih =>
    cases r₁ with
    | cat₀ r₁ =>
      cases ih r₁ hₐ.cat₀ with
      | eq h => apply Vee.eq; cases h; cases hₐ; rfl
      | rd l r => cases hₐ; exact Vee.rd (.cat₀ l) (.cat₀ r)
    | cat₁ r₁ => cases hₐ; simp; exact Vee.rd (.cat₁ r₁) (.cat₀ r₀)
    | mix₀ | mix₁ => cases hₐ.kind
    | pair =>
      cases r₀ <;> first
      | . cases hₐ.cat₀.kind
      | . rename_i r₁ _; cases r₁ <;> first
          | . cases hₐ.cat₀.mix₀.kind
          | . cases hₐ.cat₀.mix₁.kind
  | cat₁ r₀ ih =>
    cases r₁ with
    | cat₁ r₁ =>
      cases ih r₁ hₐ.cat₁ with
      | eq h => apply Vee.eq; cases h; cases hₐ; rfl
      | rd l r => cases hₐ; exact Vee.rd (.cat₁ l) (.cat₁ r)
    | cat₀ r₁ => cases hₐ; simp; exact Vee.rd (.cat₀ r₁) (.cat₁ r₀)
    | mix₀ | mix₁ => cases hₐ.kind
    | pair => cases r₀ <;> cases hₐ.cat₁.kind
  | mix₀ r₀ ih =>
    cases r₁ with
    | mix₀ r₁ =>
      cases ih r₁ hₐ.mix₀ with
      | eq h => apply Vee.eq; cases h; cases hₐ.mix₀; cases hₐ.mix₁; cases hₐ; rfl
      | rd l r => cases hₐ.mix₀; cases hₐ.mix₁; cases hₐ; exact Vee.rd (.mix₀ l) (.mix₀ r)
    | mix₁ r₁ => cases hₐ.mix₀; cases hₐ.mix₁; cases hₐ; simp; exact Vee.rd (.mix₁ r₁) (.mix₀ r₀)
    | cat₀ | cat₁ | pair => repeat cases hₐ.kind
  | mix₁ r₀ ih =>
    cases r₁ with
    | mix₁ r₁ =>
      cases ih r₁ hₐ.mix₁ with
      | eq h => apply Vee.eq; cases h; cases hₐ.mix₀; cases hₐ.mix₁; cases hₐ; rfl
      | rd l r => cases hₐ.mix₀; cases hₐ.mix₁; cases hₐ; exact Vee.rd (.mix₁ l) (.mix₁ r)
    | mix₀ r₁ => cases hₐ.mix₀; cases hₐ.mix₁; cases hₐ; simp; exact Vee.rd (.mix₀ r₁) (.mix₁ r₀)
    | cat₀ | cat₁ | pair => repeat cases hₐ.kind

def rd_perf_conf
  {i o : Nat}
  {a b c : Net S i o}
  (r₀ : Rd S R a b) (r₁ : Rd S R a c)
  : Vee R b c
:= rd_perf_conf_ r₀ r₁ rfl
