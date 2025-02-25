
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm Nat.add_zero Nat.zero_add

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
  | mix : {i₁ i₂ o₁ o₂ : Nat} -> Net S i₁ o₁ -> Net S i₂ o₂ -> Net S (i₁ + i₂) (o₁ + o₂)
  | cat : {i₁ o₁ i₂ o₂ : Nat} -> (o₁ = i₂) -> Net S i₁ o₁ -> Net S i₂ o₂ -> Net S i₁ o₂
  | cup : Net S 0 2
  | cap : Net S 2 0
  | agent : (a : S.Agent) -> Net S (S.arity a) 1
  | cast : {i₁ o₁ i₂ o₂ : Nat} -> ((i₁ = i₂) ∧ (o₁ = o₂)) -> Net S i₁ o₁ -> Net S i₂ o₂

open Net

def wires : (n : Nat) -> Net S n n
  | 0 => nil
  | n + 1 => mix (wires n) wire

def twist₁ : (n : Nat) -> Net S (1 + n) (n + 1)
  | 0 => wire
  | n + 1 => (.cast # (cat # (mix (twist₁ n) wire) (mix (wires n) swap)))

def twist : (a b : Nat) -> Net S (a + b) (b + a)
  | 0, b => (.cast # (wires b))
  | a + 1, b => (.cast # (cat # (mix wire (twist a b)) (mix (twist₁ b) (wires a))))

inductive net_eq : {i₁ o₁ i₂ o₂ : Nat} -> (h : (i₁ = i₂) ∧ (o₁ = o₂)) -> (x : Net S i₁ o₁) -> (y : Net S i₂ o₂) -> Type
  | refl :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    net_eq # x x
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

  | cast_ :
    {i₁ o₁ i₂ o₂ : Nat} -> {x : Net S i₁ o₁} ->
    {h : (i₁ = i₂) ∧ (o₁ = o₂)} ->
    net_eq # (.cast h x) x

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
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    net_eq # (cat h x (wires n)) x
  | wires_cat :
    {xᵢ xₒ n : Nat} -> {x : Net S xᵢ xₒ} ->
    {h : _} ->
    net_eq # (cat h (wires n) x) x
  | cat_assoc :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {h₁ h₂ h₃ h₄ : _} ->
    net_eq # (cat h₁ (cat h₂ x y) z) (cat h₃ x (cat h₄ y z))

  | swap_swap : net_eq # (cat # swap swap) (mix wire wire)
  | untwist_cup : net_eq # (cat # cup swap) cup
  | untwist_cap : net_eq # (cat # swap cap) cap

  | cup_swap : net_eq # (cat # (mix cup wire) (mix wire swap)) (cat # (mix wire cup) (mix swap wire))
  | cap_swap : net_eq # (cat # (mix wire swap) (mix cap wire)) (cat # (mix swap wire) (mix wire cap))

  | mix_twist :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    net_eq # (cat # (mix x y) (twist xₒ yₒ)) (cat # (twist xᵢ yᵢ) (mix y x))

  | cup_cap : net_eq # (cat # (mix cup wire) (mix wire cap)) wire

  | exch :
    {xᵢ xₒ : Nat} -> {x : Net S xᵢ xₒ} ->
    {yᵢ yₒ : Nat} -> {y : Net S yᵢ yₒ} ->
    {zᵢ zₒ : Nat} -> {z : Net S zᵢ zₒ} ->
    {wᵢ wₒ : Nat} -> {w : Net S wᵢ wₒ} ->
    {h₁ h₂ h₃ : _} ->
    net_eq # (cat h₁ (mix x y) (mix z w)) (mix (cat h₂ x z) (cat h₃ y w))

  | cat_ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {dᵢ dₒ : Nat} -> {d : Net S dᵢ dₒ} ->
    {h₁ h₂ : _} ->
    net_eq h₁ a c ->
    net_eq h₂ b d ->
    {h₃ h₄ : _} ->
    net_eq # (cat h₃ a b) (cat h₄ c d)

  | mix_ :
    {aᵢ aₒ : Nat} -> {a : Net S aᵢ aₒ} ->
    {bᵢ bₒ : Nat} -> {b : Net S bᵢ bₒ} ->
    {cᵢ cₒ : Nat} -> {c : Net S cᵢ cₒ} ->
    {dᵢ dₒ : Nat} -> {d : Net S dᵢ dₒ} ->
    {h₁ h₂ : _} ->
    net_eq h₁ a c ->
    net_eq h₂ b d ->
    net_eq # (mix a b) (mix c d)

namespace net_eq

variable
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}

def cat₁ {h₁ : _} (e : net_eq h₁ a b) {h₂ h₃ : _} : net_eq # (cat h₂ a c) (cat h₃ b c) := cat_ e refl
def cat₂ {h₁ : _} (e : net_eq h₁ a b) {h₂ h₃ : _} : net_eq # (cat h₂ c a) (cat h₃ c b) := cat_ refl e
def mix₁ {h : _} (e : net_eq h a b) : net_eq # (mix a c) (mix b c) := mix_ e refl
def mix₂ {h : _} (e : net_eq h a b) : net_eq # (mix c a) (mix c b) := mix_ refl e

def wires₁ : net_eq (S := S) # (wires 1) wire := nil_mix
def wires₂ : net_eq (S := S) # (wires 2) (mix wire wire) := mix₁ wires₁
def cat_wire {h : _} : net_eq # (cat h a wire) a := trans (cat₂ (h₃ := h) (symm wires₁)) (cat_wires)
def wire_cat {h : _} : net_eq # (cat h wire a) a := trans (cat₁ (h₃ := h) (symm wires₁)) (wires_cat)
def wires_ {a b : Nat} : {h : a = b} -> net_eq (S := S) # (wires a) (wires b)
  | rfl => refl
def wires_mix_wires {a b x : Nat} {h : a + b = x} : net_eq (S := S) # (mix (wires a) (wires b)) (wires x) := by
  revert x
  induction b
  intro x h
  apply trans
  exact mix_nil
  apply wires_
  assumption
  rename_i ih
  simp only [wires]
  intro x h
  apply trans
  apply symm
  exact mix_assoc
  apply trans
  apply mix₁
  apply ih
  rfl
  apply wires_
  simp [*]
def wire_mix_wires {a : Nat} : net_eq (S := S) # (mix wire (wires a)) (wires (a + 1)) := by
  apply trans
  apply mix₁ (symm wires₁)
  apply wires_mix_wires
  simp

def twist₁₁ : net_eq (S := S) # (twist₁ 1) (swap) := by
  apply trans cast_
  apply trans
  apply cat_
  apply symm wires₂
  apply nil_mix
  simp
  apply wires_cat

def twist₁_succ (n : Nat) : net_eq (S := S) # (twist₁ (n + 1)) (cat # (mix swap (wires n)) (mix wire (twist₁ n))) := by
  induction n
  apply trans twist₁₁
  apply symm
  apply trans
  apply cat_
  apply mix_nil
  apply symm wires₂
  simp
  apply cat_wires

  rename_i n ih
  apply trans
  apply trans cast_
  apply cat₁
  apply trans
  apply mix₁
  assumption
  apply trans
  apply mix₂
  apply symm wire_cat
  simp
  apply symm exch
  repeat simp
  apply trans cat_assoc
  apply cat_
  apply mix_assoc
  apply trans
  apply cat_
  apply mix_assoc
  apply trans
  apply mix₁
  apply trans (symm (wires_mix_wires (a := 1) (b := n)))
  apply mix₁
  apply wires₁
  simp
  apply mix_assoc
  simp
  apply trans exch
  apply mix_
  apply wire_cat
  apply symm
  apply cast_
  repeat simp

def untwist₁ (n : Nat) : Net S (n + 1) (1 + n) := twist n 1

def untwist₁_succ (n : Nat) : net_eq (S := S) # (untwist₁ (n + 1)) (cat # (mix (wires n) swap) (mix (untwist₁ n) wire)) := by
  induction n
  simp only [twist₁, untwist₁, twist, wires]
  apply trans cast_
  apply trans
  apply cat_
  apply trans
  apply mix₂
  apply cast_
  apply trans
  apply mix₁
  apply symm wires₁
  apply wires_mix_wires (x := 2)
  simp
  apply trans mix_nil
  apply twist₁₁
  simp
  apply trans wires_cat
  apply symm
  apply trans
  apply cat_
  apply nil_mix
  apply mix₁
  apply cast_
  simp
  apply cat_wires

  rename_i n ih
  apply trans cast_
  apply trans
  apply cat_
  apply trans
  apply mix_
  apply symm cat_wire
  simp
  assumption
  apply trans
  apply symm exch
  simp
  apply cat₁
  apply trans
  apply symm mix_assoc
  apply mix₁
  apply refl
  repeat simp
  apply refl
  simp
  apply trans
  apply cat_assoc
  repeat simp
  apply cat_
  apply mix₁
  apply trans
  apply mix₁
  apply symm wires₁
  apply wires_mix_wires
  simp
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm mix_assoc
  simp
  apply trans exch
  apply mix_
  apply symm
  apply cast_
  apply wire_cat
  simp

def twist₁_untwist₁ (n : Nat) : net_eq (S := S) # (cat # (twist₁ n) (untwist₁ n)) (wires (n + 1)) := by
  induction n
  simp only [twist₁, untwist₁, twist, wires]
  apply trans wire_cat
  apply cast_

  rename_i n ih
  apply trans
  simp only [twist₁]
  apply cat_
  apply cast_
  apply untwist₁_succ
  simp
  apply trans cat_assoc
  apply trans
  apply cat₂
  apply trans (symm cat_assoc)
  apply trans
  apply cat₁
  apply trans exch
  apply trans
  apply mix_
  apply wires_cat
  apply swap_swap
  apply trans
  apply mix₂
  apply symm wires₂
  apply wires_mix_wires (x := n + 2)
  repeat simp
  apply wires_cat
  repeat simp
  apply trans exch
  apply mix_
  assumption
  apply wire_cat
  repeat simp

def twist_zero (n : Nat) : net_eq (S := S) # (twist n 0) (wires n) := by
  induction n
  exact cast_
  rename_i n ih
  simp only [twist]
  apply trans cast_
  apply trans
  apply cat_
  apply trans
  apply mix_
  exact symm wires₁
  assumption
  apply wires_mix_wires (x := n + 1)
  simp
  apply trans
  apply mix₁
  exact symm wires₁
  apply wires_mix_wires (x := n + 1)
  repeat simp
  apply wires_cat

def succ_twist (a b : Nat) : net_eq (S := S) # (twist (a + 1) b) (cat # (mix (wires a) (twist₁ b)) (mix (twist a b) wire)) := by
  induction a
  simp only [twist, twist₁, wires]
  apply trans cast_
  apply trans
  apply cat_
  apply trans (mix_ (symm wires₁) cast_)
  apply wires_mix_wires (x := b + 1)
  simp
  apply mix_nil
  simp
  apply trans wires_cat
  apply symm
  apply trans
  apply cat_
  apply nil_mix
  apply mix₁ cast_
  simp
  apply cat_wires

  rename_i a ih
  apply trans cast_
  apply trans
  apply cat₁
  apply trans
  apply mix_
  apply symm wire_cat
  simp
  assumption
  apply symm exch
  repeat simp
  apply trans cat_assoc
  apply cat_
  apply trans (symm mix_assoc)
  apply mix₁
  apply trans (mix₁ (symm wires₁))
  apply wires_mix_wires (x := a + 1)
  simp
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm mix_assoc
  simp
  apply trans exch
  apply mix_
  apply symm
  apply cast_
  apply wire_cat
  repeat simp

def twist_succ (a b : Nat) : net_eq (S := S) # (twist a (b + 1)) (cat # (mix (twist a b) wire) (mix (wires b) (untwist₁ a))) := by
  revert b
  induction a
  intro b
  simp only [twist, wires, untwist₁]
  apply trans cast_
  apply symm
  apply trans
  apply cat_
  apply mix₁ (cast_)
  apply trans (mix₂ cast_)
  apply wires_mix_wires (x := b + 1)
  repeat simp
  apply wires_cat

  rename_i a ih
  intro b
  apply trans
  apply succ_twist
  apply trans
  apply cat₂
  apply mix₁
  apply ih
  simp
  apply trans
  apply cat₂
  apply trans
  apply mix₂
  apply symm wire_cat
  simp
  apply symm exch
  repeat simp
  apply trans (symm cat_assoc)
  apply trans
  apply cat₁
  apply trans
  apply cat₁
  apply trans
  apply mix_
  apply symm (wires_cat (n := a))
  simp
  apply cast_
  apply trans (symm exch)
  apply cat₂
  apply trans (symm mix_assoc)
  apply mix₁ (wires_mix_wires (x := a + b))
  repeat simp
  apply trans
  apply cat₂
  apply mix_assoc
  simp
  apply trans cat_assoc
  apply trans
  apply cat₂
  apply trans exch
  apply trans
  apply mix_
  apply trans wires_cat
  apply symm (cat_wires (n := a + b))
  repeat simp
  apply trans (cat₂ (symm wires₂))
  apply trans cat_wires
  apply symm (wires_cat (n := 2))
  repeat simp
  apply symm exch
  repeat simp
  apply trans (symm (cat_assoc))
  apply cat₁
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm (mix_assoc (z := wire))
  repeat simp
  apply trans exch
  apply mix_
  apply trans
  apply cat₂
  apply mix₂
  apply wires₁
  simp
  apply symm
  apply succ_twist
  apply wire_cat
  repeat simp
  apply trans cat_assoc
  apply cat₂
  apply trans
  apply cat₁
  apply mix₁
  apply symm (wires_mix_wires (a := b) (b := a))
  repeat simp
  apply trans
  apply cat_
  apply mix_assoc
  apply mix_assoc
  repeat simp
  apply trans exch
  apply mix_
  apply cat_wires
  apply symm
  apply untwist₁_succ
  repeat simp

def twist_twist (a b : Nat) : net_eq (S := S) # (cat # (twist a b) (twist b a)) (wires (a + b)) := by
  induction a
  apply trans
  apply cat_
  apply cast_
  apply twist_zero
  simp
  apply trans cat_wires
  apply wires_
  simp

  rename_i a ih
  apply trans
  apply cat_
  apply succ_twist
  apply twist_succ
  simp
  apply trans cat_assoc
  apply trans
  apply cat₂
  apply trans (symm cat_assoc)
  apply trans
  apply cat₁
  apply trans exch
  apply mix_
  assumption
  apply wire_cat
  repeat simp
  apply wires_cat
  repeat simp
  apply trans exch
  apply trans
  apply mix_
  apply wires_cat
  apply twist₁_untwist₁
  apply wires_mix_wires
  repeat simp
