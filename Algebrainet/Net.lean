
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

def castₙ {i₁ o₁ i₂ o₂ : Nat} : ((i₁ = i₂) ∧ (o₁ = o₂)) -> Net S i₁ o₁ -> Net S i₂ o₂
  | (And.intro rfl rfl), n => n

def wires : (n : Nat) -> Net S n n
  | 0 => nil
  | n + 1 => mix (wires n) wire

def twist₁ : (n : Nat) -> Net S (1 + n) (n + 1)
  | 0 => wire
  | n + 1 => (castₙ # (cat # (mix (twist₁ n) wire) (mix (wires n) swap)))

def twist : (a b : Nat) -> Net S (a + b) (b + a)
  | 0, b => (castₙ # (wires b))
  | a + 1, b => (castₙ # (cat # (mix wire (twist a b)) (mix (twist₁ b) (wires a))))
