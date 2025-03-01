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

abbrev EqN {S : System} {aᵢ aₒ bᵢ bₒ : Nat} (a : Net S aᵢ aₒ) (b : Net S bᵢ bₒ) : Prop
  := Eq (α := Σ i o, Net S i o) ⟨aᵢ, aₒ, a⟩ ⟨bᵢ, bₒ, b⟩

def extract_agent {i o : Nat} : (n : Net S i o) -> Option S.Agent
  | agent a => some a
  | _ => none

namespace EqN

variable
  {aᵢ aₒ bᵢ bₒ : Nat} {a : Net S aᵢ aₒ} {b : Net S bᵢ bₒ}

def congr
  {α : Type}
  (h : EqN a b)
  (f : {i o : Nat} -> Net S i o -> α)
  : f a = f b
:= Eq.rec (motive := fun b _ => f a = f b.snd.snd) rfl h

@[simp] def eqᵢ (h : EqN a b) : aᵢ = bᵢ := Eq.rec (motive := fun b _ => aᵢ = b.fst) rfl h
@[simp] def eqₒ (h : EqN a b) : aₒ = bₒ := Eq.rec (motive := fun b _ => aₒ = b.snd.fst) rfl h

end EqN

abbrev SNet (S : System) := Σ i o, Net S i o

def unpair {i o : Nat} : (n : Net S i o) -> Option (S.Agent × S.Agent)
  | cat _ (mix (agent a) (agent b)) cap => some (a, b)
  | _ => none

def uncat₀ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | cat _ a _ => some ⟨_, _, a⟩
  | _ => none

def uncat₁ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | cat _ _ b => some ⟨_, _, b⟩
  | _ => none

def unmix₀ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | mix a _ => some ⟨_, _, a⟩
  | _ => none

def unmix₀₀ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | mix (mix a _) _ => some ⟨_, _, a⟩
  | _ => none

def unmix₀₁ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | mix (mix _ a) _ => some ⟨_, _, a⟩
  | _ => none

def unmix₁₀ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | mix _ (mix a _) => some ⟨_, _, a⟩
  | _ => none

def unmix₁₁ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | mix _ (mix _ a) => some ⟨_, _, a⟩
  | _ => none

def unmix₁ {i o : Nat} : (n : Net S i o) -> Option (SNet S)
  | mix _ b => some ⟨_, _, b⟩
  | _ => none

def kind {i o : Nat} : (n : Net S i o) -> Nat
  | nil => 0
  | wire => 1
  | swap => 2
  | cup => 3
  | cap => 4
  | agent _ => 5
  | mix _ _ => 6
  | cat _ _ _ => 7

def cat₀_kind {i o : Nat} : (n : Net S i o) -> Option (Nat)
  | cat _ a _ => some (kind a)
  | _ => none

def cat₁_kind {i o : Nat} : (n : Net S i o) -> Option (Nat)
  | cat _ _ b => some (kind b)
  | _ => none

def mix₀_kind {i o : Nat} : (n : Net S i o) -> Option (Nat)
  | mix a _ => some (kind a)
  | _ => none

def mix₁_kind {i o : Nat} : (n : Net S i o) -> Option (Nat)
  | mix _ b => some (kind b)
  | _ => none

def cat₀_mix₀_kind {i o : Nat} : (n : Net S i o) -> Option (Nat)
  | cat _ (mix a _) _ => some (kind a)
  | _ => none

def cat₀_mix₁_kind {i o : Nat} : (n : Net S i o) -> Option (Nat)
  | cat _ (mix _ b) _ => some (kind b)
  | _ => none

abbrev unsome {α : Type} {a b : α} : some a = some b -> a = b := Option.some_inj.mp

def rd_perf_conf_ {S : System} {R : Rules S}
  {i₀ o₀ i₁ o₁ : Nat}
  {a₀ b : Net S i₀ o₀} {a₁ c : Net S i₁ o₁}
  (r₀ : Rd S R a₀ b) (r₁ : Rd S R a₁ c)
  (hₐ : EqN a₀ a₁)
  : Vee R (castₙ ⟨hₐ.eqᵢ, hₐ.eqₒ⟩ b) c
:= by
  induction r₀ generalizing i₁ o₁ a₁ c r₁ with
  | pair x₀ y₀ d₀ =>
    cases r₁ with
    | pair x₁ y₁ d₁ =>
      cases hₐ.congr unpair
      apply Vee.eq
      simp
    | mix₀ | mix₁ => repeat cases hₐ.congr kind
    | cat₀ r₁ =>
      cases r₁
      repeat . cases hₐ.congr cat₀_kind
      repeat {
        rename_i r₁ _; cases r₁
        repeat . cases hₐ.congr cat₀_mix₀_kind
        repeat . cases hₐ.congr cat₀_mix₁_kind
      }
    | cat₁ r₁ => cases r₁; repeat cases hₐ.congr cat₁_kind
  | cat₀ r₀ ih =>
    cases r₁ with
    | cat₀ r₁ =>
      cases ih r₁ (hₐ := unsome (hₐ.congr uncat₀)) with
      | eq h => apply Vee.eq; cases h; cases hₐ; rfl
      | rd l r => cases hₐ; exact Vee.rd (.cat₀ l) (.cat₀ r)
    | cat₁ r₁ => cases hₐ; simp; exact Vee.rd (.cat₁ r₁) (.cat₀ r₀)
    | mix₀ | mix₁ => repeat cases hₐ.congr kind
    | pair =>
      cases r₀
      repeat . cases hₐ.congr cat₀_kind
      repeat {
        rename_i r₁ _; cases r₁
        repeat . cases hₐ.congr cat₀_mix₀_kind
        repeat . cases hₐ.congr cat₀_mix₁_kind
      }
  | cat₁ r₀ ih =>
    cases r₁ with
    | cat₁ r₁ =>
      cases ih r₁ (hₐ := unsome (hₐ.congr uncat₁)) with
      | eq h => apply Vee.eq; cases h; cases hₐ; rfl
      | rd l r => cases hₐ; exact Vee.rd (.cat₁ l) (.cat₁ r)
    | cat₀ r₁ => cases hₐ; simp; exact Vee.rd (.cat₀ r₁) (.cat₁ r₀)
    | mix₀ | mix₁ => repeat cases hₐ.congr kind
    | pair => cases r₀; repeat . cases hₐ.congr cat₁_kind
  | mix₀ r₀ ih =>
    cases r₁ with
    | mix₀ r₁ =>
      cases ih r₁ (hₐ := unsome (hₐ.congr unmix₀)) with
      | eq h => apply Vee.eq; cases h; cases hₐ.congr unmix₀; cases hₐ.congr unmix₁; cases hₐ; rfl
      | rd l r => cases hₐ.congr unmix₀; cases hₐ.congr unmix₁; cases hₐ; exact Vee.rd (.mix₀ l) (.mix₀ r)
    | mix₁ r₁ => cases hₐ.congr unmix₀; cases hₐ.congr unmix₁; cases hₐ; simp; exact Vee.rd (.mix₁ r₁) (.mix₀ r₀)
    | cat₀ | cat₁ | pair => repeat cases hₐ.congr kind
  | mix₁ r₀ ih =>
    cases r₁ with
    | mix₁ r₁ =>
      cases ih r₁ (hₐ := unsome (hₐ.congr unmix₁)) with
      | eq h => apply Vee.eq; cases h; cases hₐ.congr unmix₀; cases hₐ.congr unmix₁; cases hₐ; rfl
      | rd l r => cases hₐ.congr unmix₀; cases hₐ.congr unmix₁; cases hₐ; exact Vee.rd (.mix₁ l) (.mix₁ r)
    | mix₀ r₁ => cases hₐ.congr unmix₀; cases hₐ.congr unmix₁; cases hₐ; simp; exact Vee.rd (.mix₀ r₁) (.mix₁ r₀)
    | cat₀ | cat₁ | pair => repeat cases hₐ.congr kind

def rd_perf_conf
  {i o : Nat}
  {a b c : Net S i o}
  (r₀ : Rd S R a b) (r₁ : Rd S R a c)
  : Vee R b c
:= rd_perf_conf_ r₀ r₁ rfl
