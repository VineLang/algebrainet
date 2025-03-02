
attribute [simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm Nat.add_zero Nat.zero_add

set_option autoImplicit false

notation:max "#" => (by simp [*])

structure System where
  Agent : Type
  arity : Agent -> Nat

variable {S : System}

inductive Net (S : System) : Nat -> Nat -> Type
  | nil : Net S 0 0
  | wire : Net S 1 1
  | swap : Net S 2 2
  | cup : Net S 0 2
  | cap : Net S 2 0
  | agent : (a : S.Agent) -> Net S (S.arity a) 1
  | mix : {i₁ i₂ o₁ o₂ : Nat} -> Net S i₁ o₁ -> Net S i₂ o₂ -> Net S (i₁ + i₂) (o₁ + o₂)
  | cat : {i₁ o₁ i₂ o₂ : Nat} -> (o₁ = i₂) -> Net S i₁ o₁ -> Net S i₂ o₂ -> Net S i₁ o₂

open Net

@[simp] def castₙ {i₁ o₁ i₂ o₂ : Nat} (h : (i₁ = i₂) ∧ (o₁ = o₂)) (n : Net S i₁ o₁) : Net S i₂ o₂ := cast # n

def wires : (n : Nat) -> Net S n n
  | 0 => nil
  | n + 1 => mix (wires n) wire

def twist₁ : (n : Nat) -> Net S (1 + n) (n + 1)
  | 0 => wire
  | n + 1 => (castₙ # (cat # (mix (twist₁ n) wire) (mix (wires n) swap)))

def twist : (a b : Nat) -> Net S (a + b) (b + a)
  | 0, b => (castₙ # (wires b))
  | a + 1, b => (castₙ # (cat # (mix wire (twist a b)) (mix (twist₁ b) (wires a))))

namespace Net

def kind {i o : Nat} : Net S i o -> Nat
| nil => 0
| wire => 1
| swap => 2
| cup => 3
| cap => 4
| agent _ => 5
| mix _ _ => 6
| cat _ _ _ => 7

end Net

abbrev ANet (S : System) := Σ i o, Net S i o

abbrev EqN {S : System} {aᵢ aₒ bᵢ bₒ : Nat} (a : Net S aᵢ aₒ) (b : Net S bᵢ bₒ) : Prop
  := Eq (α := ANet S) ⟨aᵢ, aₒ, a⟩ ⟨bᵢ, bₒ, b⟩

namespace EqN

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}

def congr
  (h : EqN a b)
  (α : Type)
  (f : {i o : Nat} -> Net S i o -> α)
  : f a = f b
:= Eq.rec (motive := fun b _ => f a = f b.snd.snd) rfl h

def i (e : EqN a b) : aᵢ = bᵢ := e.congr Nat (fun {i _} _ => i)
def o (e : EqN a b) : aₒ = bₒ := e.congr Nat (fun {_ o} _ => o)

abbrev unsome {α : Type} {a b : α} : some a = some b -> a = b := Option.some_inj.mp

def cat₀ {h₀ h₁ : _} (e : EqN (cat h₀ a b) (cat h₁ c d)) : EqN a c :=
  unsome (e.congr (Option (ANet S)) fun | cat _ n _ => some ⟨_, _, n⟩ | _ => none)

def cat₁ {h₀ h₁ : _} (e : EqN (cat h₀ a b) (cat h₁ c d)) : EqN b d :=
  unsome (e.congr (Option (ANet S)) fun | cat _ _ n => some ⟨_, _, n⟩ | _ => none)

def mix₀ (e : EqN (mix a b) (mix c d)) : EqN a c :=
  unsome (e.congr (Option (ANet S)) fun | mix n _ => some ⟨_, _, n⟩ | _ => none)

def mix₁ (e : EqN (mix a b) (mix c d)) : EqN b d :=
  unsome (e.congr (Option (ANet S)) fun | mix  _ n => some ⟨_, _, n⟩ | _ => none)

def agent {a b : S.Agent} (e : EqN (agent a) (agent b)) : a = b:=
  unsome (e.congr (Option S.Agent) fun | .agent a => some a | _ => none)

def kind (e : EqN a b) : a.kind = b.kind := (e.congr Nat Net.kind)

end EqN
