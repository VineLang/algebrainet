import Algebrainet.Net
import Algebrainet.Eqv
import Algebrainet.Rd

open Net

set_option autoImplicit false

variable
  {S : System}
  {aᵢ aₒ : Nat} {a : Net S aᵢ aₒ}
  {bᵢ bₒ : Nat} {b : Net S bᵢ bₒ}
  {cᵢ cₒ : Nat} {c : Net S cᵢ cₒ}
  {dᵢ dₒ : Nat} {d : Net S dᵢ dₒ}
  {eᵢ eₒ : Nat} {e : Net S eᵢ eₒ}

set_option maxHeartbeats 2000000

def ne_wires_cat {n h : _} : ¬EqN (S := S) (wires_ n) (cat h a b) := by
  intro h
  cases n
  case' succ n => cases n
  all_goals . cases h.congr kind

def ne_wires_agent_mix {n a : _} : ¬EqN (S := S) (wires_ n) (mix (agent a) b) := by
  intro h
  cases n
  case' succ n => cases n
  case' succ n => cases n
  all_goals try first
  | . cases h.congr kind
  | . cases h.congr mix₀_kind

def norm_wire_wire {h : _ } (hₐ : EqN a (mix wire wire)) : ¬EqvB S h a b := by
  stop
  intro x
  cases x; rename_i x; cases x
  all_goals first
  | . cases hₐ.congr mix₀_kind
  | . cases hₐ.congr mix₁_kind
  | . rename_i x
      cases x; rename_i x; cases x
      all_goals try first
      | . cases hₐ.congr mix₀_kind
      | . cases hₐ.congr mix₁_kind
def norm_wires {n h : _} (hₐ : EqN a (wires_ n)) : ¬EqvB S h a b := by
  stop
  cases n with
  | zero =>
    intro x
    cases x; rename_i x; cases x
    all_goals . cases hₐ.congr kind
  | succ n =>
    induction n generalizing h aᵢ aₒ bᵢ bₒ with
    | zero =>
      intro x
      cases x; rename_i x; cases x
      all_goals . cases hₐ.congr kind
    | succ n ih =>
      intro x
      cases x; rename_i x; cases x
      all_goals try . cases hₐ.congr mix₁_kind
      case nil_mix => cases n <;> cases hₐ.congr mix₀_kind
      case mix₁ x => cases x; rename_i x; cases x; all_goals . cases hₐ.congr mix₁_kind
      case mix₀ x =>
        cases hₐ.congr unmix₀
        exact ih rfl x

def comm_atom_atom
  {i₀ o₀ : Nat} {a₀ : Net S i₀ o₀}
  {i₁ o₁ : Nat} {a₁ : Net S i₁ o₁}
  {h₀ h₁ : _} (x : EqvA S h₀ a₀ b) (y : EqvA S h₁ a₁ c)
  (hₐ : EqN a₀ a₁)
  : Eqv S (by cases hₐ; simp [h₀] at h₁; simp [*]) b c := by
  stop
  cases x <;> cases y
  all_goals try first
  | . cases hₐ.congr kind
  | . cases hₐ.congr cat₀_kind
  | . cases hₐ.congr cat₁_kind
  | . cases hₐ.congr mix₀_kind
  | . cases hₐ.congr mix₁_kind
  | . cases hₐ.congr uncat₀
  | . cases hₐ.congr uncat₁
  | . try
        cases hₐ.congr unmix₀
        cases hₐ.congr unmix₁
      try
        cases hₐ.congr uncat₀
        cases hₐ.congr uncat₁
      exact .mk .refl .refl

  case nil_mix.mix_assoc =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk .refl (.apply (.mix₀ (.atom .nil_mix)) .refl)
  case mix_assoc.nil_mix =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk (.apply (.mix₀ (.atom .nil_mix)) .refl) .refl
  case mix_assoc.mix_assoc =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁₀
    cases hₐ.congr unmix₁₁
    exact .mk .refl .refl
  case move_agent.move_agent =>
    cases hₐ.congr cat₀_mix₀_agent
    exact .mk .refl .refl
  case exch.exch =>
    cases hₐ.congr un_cat_mix
    exact .mk .refl .refl
  case exch.move_cup | exch.move_cap | exch.cup_cap | cup_cap.exch | move_cap.exch | move_cup.exch =>
    cases hₐ.congr un_cat_mix
    rename_i h _
    cases h

  case cat_wires.wires_cat | wires_cat.cat_wires =>
    cases hₐ.congr uncat₀
    cases hₐ.congr uncat₁
    rename_i h
    cases h
    exact .mk .refl .refl

  case cat_wires.cat_assoc =>
    cases hₐ.congr uncat₀
    cases hₐ.congr uncat₁
    exact .mk .refl (.apply (.cat₁ (.atom .cat_wires)) .refl)
  case cat_assoc.cat_wires =>
    cases hₐ.congr uncat₀
    cases hₐ.congr uncat₁
    exact .mk (.apply (.cat₁ (.atom .cat_wires)) .refl) .refl

  case cat_wires.exch =>
    cases o₀
    . cases hₐ.congr cat₁_kind
    rename_i n _
    cases n
    . cases hₐ.congr cat₁_kind
    cases hₐ.congr uncat₀
    cases hₐ.congr uncat₁_mix₀
    cases hₐ.congr uncat₁_mix₁
    exact .mk .refl (.apply (.mix₀ (.atom .cat_wires)) (.apply (.mix₁ (.atom .cat_wires)) .refl))
  case exch.cat_wires =>
    cases o₁
    . cases hₐ.congr cat₁_kind
    rename_i n _
    cases n
    . cases hₐ.congr cat₁_kind
    cases hₐ.congr uncat₀
    cases hₐ.congr uncat₁_mix₀
    cases hₐ.congr uncat₁_mix₁
    exact .mk (.apply (.mix₀ (.atom .cat_wires)) (.apply (.mix₁ (.atom .cat_wires)) .refl)) .refl

  case wires_cat.exch =>
    cases i₀
    . cases hₐ.congr cat₀_kind
    rename_i n _
    cases n
    . cases hₐ.congr cat₀_kind
    cases hₐ.congr uncat₁
    cases hₐ.congr uncat₀_mix₀
    cases hₐ.congr uncat₀_mix₁
    exact .mk .refl (.apply (.mix₀ (.atom .wires_cat)) (.apply (.mix₁ (.atom .wires_cat)) .refl))
  case exch.wires_cat =>
    cases i₁
    . cases hₐ.congr cat₀_kind
    rename_i n _
    cases n
    . cases hₐ.congr cat₀_kind
    cases hₐ.congr uncat₁
    cases hₐ.congr uncat₀_mix₀
    cases hₐ.congr uncat₀_mix₁
    exact .mk (.apply (.mix₀ (.atom .wires_cat)) (.apply (.mix₁ (.atom .wires_cat)) .refl)) .refl

  case wires_cat.cat_assoc | cat_assoc.wires_cat =>
    cases ne_wires_cat (unsome (hₐ.congr uncat₀))
  case wires_cat.move_agent | move_agent.wires_cat =>
    cases ne_wires_agent_mix (unsome (hₐ.congr uncat₀))

def comm_mix₀_atom
  {h₀ h₁ : _} (x : EqvB S h₀ a d) (y : EqvA S h₁ c e)
  (hₐ : EqN (mix a b) c)
  : Eqv S (by cases hₐ; simp [h₀] at h₁; simp [*]) (mix d b) e := by
  stop
  cases y <;> try . cases hₐ.congr kind
  case mix_nil =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk (.apply (.atom .mix_nil) .refl) (.apply x .refl)
  case nil_mix =>
    stop
    cases x
    rename_i x
    cases x
    repeat . cases hₐ.congr mix₀_kind
  case mix_assoc =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk (.apply (.atom .mix_assoc) .refl) (.apply (.mix₀ (.mix₀ x)) .refl)
  case unexch =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk .refl (.apply (.atom .exch) (.apply (.mix₀ x) .refl))

def comm_mix₁_atom
  {h₀ h₁ : _} (x : EqvB S h₀ b d) (y : EqvA S h₁ c e)
  (hₐ : EqN (mix a b) c)
  : Eqv S (by cases hₐ; simp [h₀] at h₁; simp [*]) (mix a d) e := by
  stop
  cases y <;> try . cases hₐ.congr kind
  case mix_nil =>
    cases x
    rename_i x
    cases x
    repeat . cases hₐ.congr mix₁_kind
  case nil_mix =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk (.apply (.atom .nil_mix) .refl) (.apply x .refl)
  case mix_assoc =>
    cases hₐ.congr unmix₀
    cases x; rename_i x; cases x
    all_goals try . cases hₐ.congr mix₁_kind
    case mix_nil =>
      cases hₐ.congr unmix₁₀
      cases hₐ.congr unmix₁₁
      exact .mk .refl (.apply (.atom .mix_nil) .refl)
    case nil_mix =>
      cases hₐ.congr unmix₁₀
      cases hₐ.congr unmix₁₁
      exact .mk .refl (.apply (.mix₀ (.atom .mix_nil)) .refl)
    case mix_assoc =>
      cases hₐ.congr unmix₁₀
      cases hₐ.congr unmix₁₁
      exact .mk (.apply (.atom .mix_assoc) (.apply (.mix₁ (.atom .mix_assoc)) .refl)) (.apply (.atom .mix_assoc) .refl)
    case unexch =>
      cases hₐ.congr unmix₁₀
      cases hₐ.congr unmix₁₁
      exact .mk (.apply (.mix₁ (.atom .exch)) (.apply (.atom .mix_assoc) .refl)) .refl
    case mix₀ y =>
      cases hₐ.congr unmix₁₀
      cases hₐ.congr unmix₁₁
      exact .mk (.apply (.atom .mix_assoc) .refl) (.apply (.mix₀ (.mix₁ y)) .refl)
    case mix₁ y =>
      cases hₐ.congr unmix₁₀
      cases hₐ.congr unmix₁₁
      exact .mk (.apply (.atom .mix_assoc) .refl) (.apply (.mix₁ y) .refl)
  case unexch =>
    cases hₐ.congr unmix₀
    cases hₐ.congr unmix₁
    exact .mk .refl (.apply (.atom .exch) (.apply (.mix₁ x) .refl))

def comm_cat₀_atom
  {h₀ h₁ h₂ : _} (x : EqvB S h₀ a d) (y : EqvA S h₁ c e)
  (hₐ : EqN (cat h₂ a b) c)
  : Eqv S (by cases hₐ; simp [h₀] at h₁; simp [*]) (cat (by cases hₐ; rcases h₀ with ⟨⟨⟩,⟨⟩⟩; simp [*]) d b) e := by
  cases y
  -- all_goals try first
  -- | . cases hₐ.congr kind
  -- | . cases x; rename_i x; cases x
  --     all_goals . cases hₐ.congr cat₀_kind
  -- case cat_nil =>
  --   cases hₐ.congr uncat₀
  --   cases hₐ.congr uncat₁
  --   exact .mk (.apply (.atom .cat_nil) .refl) (.apply x .refl)
  -- case wires_swap | wires_cap =>
  --   cases hₐ.congr uncat₀
  --   cases hₐ.congr uncat₁
  --   cases norm_wire_wire rfl x
  -- case wires_agent =>
  --   cases hₐ.congr uncat₀
  --   cases hₐ.congr uncat₁
  --   cases norm_wires rfl x
  case cat_assoc =>
    cases hₐ.congr uncat₁
    cases x; rename_i x; cases x
    all_goals try . cases hₐ.congr cat₀_kind



    repeat sorry



  -- case move_cup | move_cap | move_swap | move_agent | cup_cap =>
  --   cases x; rename_i x; cases x
  --   all_goals try first
  --   | . cases hₐ.congr cat₀_kind
  --   | . cases hₐ.congr cat₀_mix₀_kind
  --   | . cases hₐ.congr cat₀_mix₁_kind
  --   case mix₀ =>
  --     rename_i x
  --     cases x; rename_i x; cases x
  --     all_goals . cases hₐ.congr cat₀_mix₀_kind
  --   case mix₁ =>
  --     rename_i x
  --     cases x; rename_i x; cases x
  --     all_goals . cases hₐ.congr cat₀_mix₁_kind
  -- case exch =>
  --   cases hₐ.congr uncat₀
  --   cases hₐ.congr uncat₁
  --   apply Eqv.mk .refl (.apply (.atom .unexch) (.apply (.cat₀ x) .refl))
  --   simp only [*]

  repeat sorry









  /-

  case exch
  S : System
  aᵢ aₒ : Nat
  a : Net S aᵢ aₒ
  bᵢ bₒ : Nat
  b : Net S bᵢ bₒ
  dᵢ dₒ : Nat
  d : Net S dᵢ dₒ
  h₀ : aᵢ = dᵢ ∧ aₒ = dₒ
  h₂ : aₒ = bᵢ
  x : EqvB S h₀ a d
  xᵢ✝ xₒ✝ : Nat
  x✝ : Net S xᵢ✝ xₒ✝
  yᵢ✝ yₒ✝ : Nat
  y✝ : Net S yᵢ✝ yₒ✝
  zᵢ✝ zₒ✝ : Nat
  z✝ : Net S zᵢ✝ zₒ✝
  wᵢ✝ wₒ✝ : Nat
  w✝ : Net S wᵢ✝ wₒ✝
  h₀✝ : xₒ✝ + yₒ✝ = zᵢ✝ + wᵢ✝
  h₁✝ : xₒ✝ = zᵢ✝
  h₂✝ : yₒ✝ = wᵢ✝
  hₐ : EqN (cat h₂ a b) (cat h₀✝ (x✝.mix y✝) (z✝.mix w✝))
  ⊢ Eqv S ⋯ (cat ⋯ d b) ((cat h₁✝ x✝ z✝).mix (cat h₂✝ y✝ w✝))
  -/
  repeat sorry

def comm_cat₁_atom
  {h₀ h₁ h₂ : _} (x : EqvB S h₀ b d) (y : EqvA S h₁ c e)
  (hₐ : EqN (cat h₂ a b) c)
  : Eqv S (by cases hₐ; simp [h₀] at h₁; simp [*]) (cat # a d) e := by sorry

def comm_b
  {i₀ o₀ : Nat} {a₀ : Net S i₀ o₀}
  {i₁ o₁ : Nat} {a₁ : Net S i₁ o₁}
  {h₀ h₁ : _} (x : EqvB S h₀ a₀ b) (y : EqvB S h₁ a₁ c)
  (hₐ : EqN a₀ a₁)
  : Eqv S (by cases hₐ; simp [h₀] at h₁; simp [*]) b c := by
  induction x generalizing i₁ o₁ cᵢ cₒ with
  | atom x =>
    cases y with
    | atom y => exact comm_atom_atom x y hₐ
    | mix₀ y => exact .symm (comm_mix₀_atom y x (Eq.symm hₐ))
    | mix₁ y => exact .symm (comm_mix₁_atom y x (Eq.symm hₐ))
    | cat₀ y => exact .symm (comm_cat₀_atom y x (Eq.symm hₐ))
    | cat₁ y => exact .symm (comm_cat₁_atom y x (Eq.symm hₐ))
  | mix₀ x ih =>
    cases y with
    | atom y => exact comm_mix₀_atom x y hₐ
    | mix₀ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mix₀ (ih y rfl)
    | mix₁ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply (.mix₁ y) .refl) (.apply (.mix₀ x) .refl)
    | _ => cases hₐ.congr kind
  | mix₁ x ih =>
    cases y with
    | atom y => exact comm_mix₁_atom x y hₐ
    | mix₀ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply (.mix₀ y) .refl) (.apply (.mix₁ x) .refl)
    | mix₁ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mix₁ (ih y rfl)
    | _ => cases hₐ.congr kind
  | cat₀ x ih =>
    cases y with
    | atom y => exact comm_cat₀_atom x y hₐ
    | cat₀ y =>
      cases hₐ.congr uncat₀
      cases hₐ.congr uncat₁
      exact .cat₀ (ih y rfl)
    | cat₁ y =>
      cases hₐ.congr uncat₀
      cases hₐ.congr uncat₁
      apply Eqv.mk (.apply (.cat₁ y) .refl) (.apply (.cat₀ x) .refl)
      simp [*]
    | _ => cases hₐ.congr kind
  | cat₁ x ih =>
    cases y with
    | atom y => exact comm_cat₁_atom x y hₐ
    | cat₀ y =>
      cases hₐ.congr uncat₀
      cases hₐ.congr uncat₁
      apply Eqv.mk (.apply (.cat₀ y) .refl) (.apply (.cat₁ x) .refl)
      simp [*]
    | cat₁ y =>
      cases hₐ.congr uncat₀
      cases hₐ.congr uncat₁
      exact .cat₁ (ih y rfl)
    | _ => cases hₐ.congr kind
