
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm Nat.add_zero Nat.zero_add

set

notation:max "#" => (by simp [*])

structure System where
  Agent : Type
  arity : Agent -> Nat

variable {S : System}

inductive Net (S : System) : Nat -> Nat -> Type
  | wires : (n : Nat) -> Net S n n
  | twist : (a b : Nat) -> Net S (a + b) (b + a)
  | mix : {i₁ i₂ o₁ o₂ : Nat} -> Net S i₁ o₁ -> Net S i₂ o₂ -> Net S (i₁ + i₂) (o₁ + o₂)
  | cat : {i₁ o₁ i₂ o₂ : Nat} -> (o₁ = i₂) -> Net S i₁ o₁ -> Net S i₂ o₂ -> Net S i₁ o₂
  | cup : Net S 0 2
  | cap : Net S 2 0
  | agent₁ : (a : S.Agent) -> Net S (S.arity a) 1
  | agent₂ : (a : S.Agent) -> Net S 1 (S.arity a)

open Net

@[simp] def reflect {a b : Nat} : Net S a b -> Net S b a
  | wires n => wires n
  | twist a b => twist b a
  | mix x y => mix (reflect x) (reflect y)
  | cat h a b => cat h.symm (reflect b) (reflect a)
  | cup => cap
  | cap => cup
  | agent₁ a => agent₂ a
  | agent₂ a => agent₁ a

abbrev nil : Net S 0 0 := wires 0
abbrev wire : Net S 1 1 := wires 1

abbrev castn {i₁ o₁ i₂ o₂ : Nat} (h : (i₁ = i₂) ∧ (o₁ = o₂)) (n : Net S i₁ o₁) : Net S i₂ o₂ := cast # n

theorem reflect_inv {a b : Nat} (n : Net S a b) : (reflect (reflect n)) = n := by
  induction n
  repeat simp [*]

@[simp] theorem reflect_wires {n : Nat} : (reflect (wires n)) = (wires (S := S) n) := by
  induction n
  repeat simp [*]

@[simp] theorem reflect_cast {i₁ o₁ i₂ o₂ : Nat} :
  {h : (i₁ = i₂) ∧ (o₁ = o₂)} ->
  (n : Net S i₁ o₁) -> (reflect (castn h n)) = (castn # (reflect n))
  | (And.intro rfl rfl), _ => rfl

inductive net_eq : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Type
  | refl : net_eq # x x
  | trans :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {e f : _} -> net_eq e x y -> net_eq f y z ->
    net_eq # x z
  | symm :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {e : _} -> net_eq e x y ->
    net_eq # y x

  | mix_nil :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    net_eq # (mix x nil) x
  | nil_mix :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    net_eq # (mix nil x) x
  | mix_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    net_eq # (mix (mix x y) z) (mix x (mix y z))

  | cat_wires :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    net_eq # (cat # x (wires xₒ)) x
  | wires_cat :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    net_eq # (cat # (wires xᵢ) x) x
  | cat_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₁ h₂ h₃ h₄ : _} ->
    net_eq # (cat h₁ (cat h₂ x y) z) (cat h₃ x (cat h₄ y z))

  | twist_twist {a b : Nat} : net_eq # (cat # (twist a b) (twist b a)) (wires (a + b))
  | cup_twist : net_eq # (cat # cup (twist 1 1)) cup
  | twist_cap : net_eq # (cat # (twist 1 1) cap) cap

  | mix_twist :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    net_eq # (cat # (mix x y) (twist xₒ yₒ)) (cat # (twist xᵢ yᵢ) (mix y x))

  | twist_zero : {n : Nat} -> net_eq # (twist n 0) (wires n)
  | zero_twist : {n : Nat} -> net_eq # (twist 0 n) (wires n)

  | twist_plus :
    {x a b : Nat} ->
    net_eq # (cat # (mix (twist x a) (wires b)) (mix (wires a) (twist x b))) (twist x (a + b))
  | plus_twist :
    {x a b : Nat} ->
    net_eq # (cat # (mix (wires a) (twist b x)) (mix (twist a x) (wires b))) (twist (a + b) x)

  | cup_cap : net_eq # (cat # (mix cup wire) (mix wire cap)) wire

  | exch :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {wᵢ wₒ : Nat} -> {w : Net S wᵢ wₒ} ->
    {h₁ h₂ h₃ : _} ->
    net_eq # (cat h₁ (mix x y) (mix z w)) (mix (cat h₂ x z) (cat h₃ y w))

  | cat₁ :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₁ : _} -> net_eq h₁ x y ->
    (h₂ : (xₒ = zᵢ) ∧ (yₒ = zᵢ)) ->
    net_eq # (cat # x z) (cat # y z)

  | cat₂ :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₁ : _} -> net_eq h₁ x y ->
    (h₂ : (zₒ = xᵢ) ∧ (zₒ = yᵢ)) ->
    net_eq # (cat # z x) (cat # z y)

  | mix₁ :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h : _} -> net_eq h x y ->
    net_eq # (mix x z) (mix y z)

  | mix₂ :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h : _} -> net_eq h x y ->
    net_eq # (mix z x) (mix z y)

def cap_cup : net_eq (S := S) # (cat # (mix wire cup) (mix cap wire)) wire := by
  apply net_eq.trans
  apply net_eq.cat₁
  apply net_eq.trans
  apply net_eq.trans
  apply net_eq.symm
  exact net_eq.cat_wires
  apply net_eq.cat₂
  apply net_eq.symm
  apply net_eq.twist_twist
  repeat simp
  apply net_eq.trans
  apply net_eq.symm
  apply net_eq.cat_assoc
  repeat simp
  apply net_eq.cat₁
  apply net_eq.trans
  exact net_eq.mix_twist (x := wire) (y := cup)
  repeat simp
  apply net_eq.trans
  apply net_eq.cat₁
  exact net_eq.twist_zero
  repeat simp
  exact net_eq.wires_cat
  repeat simp
  apply net_eq.trans
  apply net_eq.cat_assoc
  repeat simp
  apply net_eq.trans
  apply net_eq.cat₂
  apply net_eq.trans
  apply net_eq.cat₁
  apply net_eq.symm
  apply net_eq.plus_twist (a := 1) (b := 1) (x := 1)
  repeat simp
  apply net_eq.trans
  apply net_eq.cat_assoc
  repeat simp
  apply net_eq.cat₂
  apply net_eq.trans
  apply net_eq.exch (x := (twist 1 1)) (y := wire) (z := cap) (w := wire)
  repeat simp
  apply net_eq.trans
  apply net_eq.mix₁ (z := (cat _ wire wire))
  exact net_eq.twist_cap
  repeat simp
  apply net_eq.mix₂
  exact net_eq.cat_wires
  repeat simp
  apply net_eq.trans
  apply net_eq.cat₁
  apply net_eq.trans
  apply net_eq.mix₁ (z := wire)
  apply net_eq.symm
  exact net_eq.cup_twist
  repeat simp
  apply net_eq.trans
  apply net_eq.mix₂ (x := wire)
  apply net_eq.symm
  apply net_eq.cat_wires
  repeat simp
  apply net_eq.symm
  apply net_eq.exch (x := cup) (z := (twist 1 1)) (y := wire) (w := wire)
  repeat simp
  apply net_eq.trans
  apply net_eq.cat_assoc
  repeat simp
  apply net_eq.trans
  apply net_eq.cat₂
  apply net_eq.trans
  apply net_eq.symm
  apply net_eq.cat_assoc
  repeat simp
  apply net_eq.trans
  apply net_eq.cat₁
  exact net_eq.twist_plus (a := 1) (b := 1)
  repeat simp
  apply net_eq.trans
  apply net_eq.symm
  apply net_eq.mix_twist (x := wire) (y := cap)
  apply net_eq.trans
  apply net_eq.cat₂
  exact net_eq.twist_zero
  repeat simp
  exact net_eq.cat_wires
  repeat simp
  exact net_eq.cup_cap
  repeat simp

def reflect_equiv {h : _} : (net_eq h x y) -> (net_eq # (reflect x) (reflect y))
  | .refl => .refl
  | .trans p q => .trans (reflect_equiv p) (reflect_equiv q)
  | .symm p => .symm (reflect_equiv p)

  | .mix_nil (x := x) => cast # (net_eq.mix_nil (x := (reflect x)))
  | .nil_mix (x := x) => cast # (net_eq.nil_mix (x := (reflect x)))
  | .mix_assoc (x := x) (y := y) (z := z) => cast # (net_eq.mix_assoc (x := (reflect x)) (y := (reflect y)) (z := (reflect z)))

  | .cat_wires (x := x) => cast # (net_eq.wires_cat (x := (reflect x)))
  | .wires_cat (x := x) => cast # (net_eq.cat_wires (x := (reflect x)))
  | .cat_assoc (x := x) (y := y) (z := z) => (net_eq.symm (net_eq.cat_assoc (x := (reflect z)) (y := (reflect y)) (z := (reflect x))))

  | .twist_twist => .twist_twist
  | .cup_twist => .twist_cap
  | .twist_cap => .cup_twist

  | .mix_twist => (.symm .mix_twist)

  | .twist_zero => .zero_twist
  | .zero_twist => .twist_zero

  | .twist_plus => .plus_twist
  | .plus_twist => .twist_plus







  | _ => sorry
