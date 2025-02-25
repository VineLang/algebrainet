
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

def cotwist₁ : (n : Nat) -> Net S (n + 1) (1 + n)
  | 0 => wire
  | n + 1 => (.cast # (cat # (mix (wires n) swap) (mix (cotwist₁ n) wire)))

def cotwist : (a b : Nat) -> Net S (b + a) (a + b)
  | 0, b => (.cast # (wires b))
  | a + 1, b => (.cast # (cat # (mix (cotwist₁ b) (wires a)) (mix wire (cotwist a b))))

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

def twist₁_cotwist₁ (n : Nat) : net_eq (S := S) # (cat # (twist₁ n) (cotwist₁ n)) (wires (n + 1)) := by
  induction n
  simp only [twist₁, cotwist₁]
  apply trans
  exact cat_wire
  exact symm wires₁
  simp only [twist₁, cotwist₁]
  apply trans
  apply cat_
  exact cast_
  exact cast_
  simp
  apply trans
  apply cat_assoc
  repeat simp
  apply trans
  apply cat₂
  apply trans
  apply symm
  apply cat_assoc
  repeat simp
  apply trans
  apply cat₁
  apply trans
  apply exch
  repeat simp
  apply trans
  apply mix_
  exact cat_wires
  exact swap_swap
  apply trans
  apply mix₂
  apply symm
  apply wires₂
  apply wires_mix_wires
  rfl
  repeat simp
  exact wires_cat
  repeat simp
  apply trans
  apply exch
  repeat simp
  apply mix_
  assumption
  exact cat_wire

def twist_cotwist (a b : Nat) : net_eq (S := S) # (cat # (twist a b) (cotwist a b)) (wires (a + b)) := by
  induction a
  simp only [twist, cotwist]
  apply trans
  apply cat_ cast_ cast_
  simp
  apply trans
  exact cat_wires
  apply wires_
  simp
  apply trans
  simp only [twist, cotwist]
  apply cat_ cast_ cast_
  simp
  apply trans
  apply cat_assoc
  repeat simp
  apply trans
  apply cat₂
  apply trans
  apply symm
  apply cat_assoc
  repeat simp
  apply trans
  apply cat₁
  apply trans
  apply exch
  repeat simp
  apply trans
  apply mix_
  apply twist₁_cotwist₁
  apply cat_wires
  apply wires_mix_wires
  rfl
  simp
  apply wires_cat
  repeat simp
  apply trans exch
  repeat simp
  apply trans
  apply mix_
  apply cat_wire
  assumption
  apply trans
  apply mix₁
  apply symm
  apply wires₁
  apply wires_mix_wires
  repeat simp

def cotwist₁_swap (n : Nat) : net_eq (S := S) # (cotwist₁ (n + 1)) (cat # (mix wire (cotwist₁ n)) (mix swap (wires n))) := by
  induction n
  simp only [cotwist₁, wires]
  apply trans cast_
  apply trans
  apply cat_
  apply nil_mix
  apply symm wires₂
  simp
  apply trans cat_wires
  apply symm
  apply trans
  apply cat_
  apply symm wires₂
  apply mix_nil
  simp
  exact wires_cat
  rename_i n ih
  apply trans cast_
  apply trans
  apply trans
  apply cat₂
  apply mix₁
  assumption
  simp
  apply trans
  apply cat₂
  apply trans
  apply mix₂
  apply symm
  apply cat_wire
  repeat simp
  apply symm
  apply exch
  repeat simp
  apply trans
  apply symm cat_assoc
  repeat simp
  apply trans
  apply cat₁
  apply trans
  apply cat₁
  apply mix₁
  apply symm
  apply wires_mix_wires (a := 1) (b := n)
  repeat simp
  apply trans
  apply cat_
  apply mix_assoc
  apply mix_assoc
  repeat simp
  apply trans exch
  apply mix_
  apply wires_cat
  apply symm
  apply cast_ (i₂ := ((n + 1) + 1)) (o₂ := (1 +(n + 1)))
  repeat simp
  apply cat₂
  apply mix_assoc
  simp
  simp only [cotwist₁, wires]
  exact refl

def twist_n_1_eq_cotwist₁ (n : Nat) : net_eq (S := S) # (twist n 1) (cotwist₁ n) := by
  induction n
  apply trans cast_
  exact wires₁
  simp only [twist]
  apply trans cast_
  apply symm
  apply trans
  apply cotwist₁_swap
  apply symm
  apply cat_
  apply mix₂
  assumption
  apply mix₁
  simp only [twist₁]
  apply trans cast_
  apply trans
  apply cat₁ (symm wires₂)
  simp
  apply trans wires_cat
  exact nil_mix

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

def twist_foo (a b : Nat) : net_eq (S := S) # (twist (a + 1) b) (cat # (mix (wires a) (twist₁ b)) (mix (twist a b) wire)) := by
  induction a
  simp only [twist, wires]
  apply trans cast_
  apply trans
  apply cat₁
  apply trans
  apply mix_
  apply symm wires₁
  apply cast_
  apply wires_mix_wires (x := 1 + b)
  repeat simp
  apply trans wires_cat
  apply trans mix_nil
  apply symm
  apply trans
  apply cat_
  apply nil_mix
  apply trans
  apply mix_
  apply cast_
  apply symm wires₁
  apply wires_mix_wires (x :=1 + b)
  repeat simp
  apply cat_wires

  rename_i a ih
  apply trans cast_
  apply trans
  apply cat₁
  apply trans
  apply mix₂
  assumption
  apply trans
  apply mix₁
  apply symm cat_wire
  simp
  apply symm exch
  repeat simp
  apply trans
  apply cat_assoc
  repeat simp
  apply trans
  apply cat₁
  apply trans
  apply symm mix_assoc
  apply mix₁
  apply trans
  apply mix₁
  apply symm wires₁
  apply wires_mix_wires (x := a + 1)
  repeat simp
  apply cat₂
  apply trans
  apply cat_
  apply symm mix_assoc
  apply symm mix_assoc
  repeat simp
  apply trans exch
  apply mix_
  apply symm
  apply cast_
  apply wire_cat
  simp

def twist₁_foo (n : Nat) : net_eq (S := S) # (twist₁ (n + 1)) (cat # (mix swap (wires n)) (mix wire (twist₁ n))) := by


def twist_succ2 (a b : Nat) : net_eq (S := S) # (twist a (b + 1)) (cat # (mix (twist a b) wire) (mix (wires b) (cotwist₁ a))) := by
  induction a
  apply trans cast_
  apply symm
  apply trans
  apply cat₁
  apply mix₁
  apply cast_
  simp
  exact wires_cat
  rename_i a ih
  apply trans
  apply twist_foo
  apply trans
  apply cat₂
  apply mix₁
  apply ih
  simp



def twist_succ (a b : Nat) : net_eq (S := S) # (twist a (b + 1)) (cat # (mix (twist a b) wire) (mix (wires b) (cotwist₁ a))) := by
  revert a
  induction b
  intro a
  apply trans
  apply twist_n_1_eq_cotwist₁
  apply symm
  apply trans
  apply cat_
  apply trans
  apply mix_
  apply twist_zero
  apply symm wires₁
  apply wires_mix_wires (x := a + 1)
  simp
  exact nil_mix
  simp
  apply wires_cat

  rename_i b bh
  intro a
  induction a
  apply trans cast_
  apply symm
  apply trans
  apply cat₁
  apply mix₁
  apply cast_
  simp
  exact wires_cat
  rename_i a ah
  apply trans cast_
  apply trans
  apply cat₁
  apply mix₂
  exact ah
  simp











def twist_eq_cotwist (a b : Nat) : net_eq (S := S) # (twist a b) (cotwist b a) := by
  induction b
  apply trans
  apply twist_zero
  apply symm
  apply trans cast_
  apply wires_
  simp

















































  -- | twist_twist {a b : Nat} : net_eq # (cat # (twist a b) (twist b a)) (wires (a + b))
  -- | cup_twist : net_eq # (cat # cup (twist 1 1)) cup
  -- | twist_cap : net_eq # (cat # (twist 1 1) cap) cap

  -- | twist_zero : {n : Nat} -> net_eq # (twist n 0) (wires n)
  -- | zero_twist : {n : Nat} -> net_eq # (twist 0 n) (wires n)

  -- | twist_plus :
  --   {x a b : Nat} ->
  --   net_eq # (cat # (mix (twist x a) (wires b)) (mix (wires a) (twist x b))) (twist x (a + b))
  -- | plus_twist :
  --   {x a b : Nat} ->
  --   net_eq # (cat # (mix (wires a) (twist b x)) (mix (twist a x) (wires b))) (twist (a + b) x)
