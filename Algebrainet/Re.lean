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

def comm
  {i₀ o₀ : Nat} {a₀ : Net S i₀ o₀}
  {i₁ o₁ : Nat} {a₁ : Net S i₁ o₁}
  {h₀ h₁ : _} (x : EqvA S h₀ a₀ b) (y : EqvA S h₁ a₁ c)
  (hₐ : EqN a₀ a₁)
  : EqvN S (by cases hₐ; simp [h₀] at h₁; simp [*]) b c  := by
  induction x generalizing i₁ o₁ cᵢ cₒ with
  | mix_nil =>
    stop . cases y with
    | mix_nil =>
      cases hₐ
      exact .mk .refl .refl
    | nil_mix =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk .refl .refl
    | mix_assoc =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk .refl (.apply (.mix₁ .mix_nil) .refl)
    | mix₀ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply y .refl) (.apply .mix_nil .refl)
    | mix₁ y => cases y <;> cases hₐ.congr mix₁_kind
    | _ => cases hₐ.congr kind
  | nil_mix =>
    stop . cases y with
    | nil_mix =>
      cases hₐ.congr unmix₁
      exact .mk .refl .refl
    | mix_nil =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk .refl .refl
    | mix₁ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply y .refl) (.apply .nil_mix .refl)
    | mix_assoc => cases hₐ.congr mix₀_kind
    | mix₀ y => cases y <;> cases hₐ.congr mix₀_kind
    | _ => cases hₐ.congr kind
  | mix_assoc =>
    stop . cases y with
    | mix_nil =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply (.mix₁ .mix_nil) .refl) .refl
    | nil_mix => cases hₐ.congr mix₀_kind
    | mix_assoc =>
      cases hₐ.congr unmix₀₀
      cases hₐ.congr unmix₀₁
      cases hₐ.congr unmix₁
      exact .mk .refl .refl
    | mix₁ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply (.mix₁ (.mix₁ y)) .refl) (.apply .mix_assoc .refl)
    | mix₀ y =>
      cases hₐ.congr unmix₁
      cases y with
      | mix_nil =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply (.mix₁ .nil_mix) .refl) .refl
      | nil_mix =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        cases hₐ.congr unmix₁
        exact .mk (.apply .nil_mix .refl) .refl
      | mix_assoc =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply .mix_assoc .refl) (.apply .mix_assoc (.apply (.mix₁ .mix_assoc) .refl))
      | mix₀ y =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply (.mix₀ y) .refl) (.apply .mix_assoc .refl)
      | mix₁ y =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply (.mix₁ (.mix₀ y)) .refl) (.apply .mix_assoc .refl)
      | _ => cases hₐ.congr mix₀_kind
    | _ => cases hₐ.congr kind
  | mix₀ x ih =>
    stop . cases y with
    | mix_nil =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply .mix_nil .refl) (.apply x .refl)
    | nil_mix => cases x <;> cases hₐ.congr mix₀_kind
    | mix₀ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mix₀ (ih y rfl)
    | mix₁ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply (.mix₁ y) .refl) (.apply (.mix₀ x) .refl)
    | mix_assoc =>
      cases hₐ.congr unmix₁
      cases x with
      | mix_nil =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk .refl (.apply (.mix₁ .nil_mix) .refl)
      | nil_mix =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        cases hₐ.congr unmix₁
        exact .mk .refl (.apply .nil_mix .refl)
      | mix_assoc =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply .mix_assoc (.apply (.mix₁ .mix_assoc) .refl)) (.apply .mix_assoc .refl)
      | mix₀ y =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply .mix_assoc .refl) (.apply (.mix₀ y) .refl)
      | mix₁ y =>
        cases hₐ.congr unmix₀₀
        cases hₐ.congr unmix₀₁
        exact .mk (.apply .mix_assoc .refl) (.apply (.mix₁ (.mix₀ y)) .refl)
      | _ => cases hₐ.congr mix₀_kind
    | _ => cases hₐ.congr kind
  | mix₁ x ih =>
    stop . cases y with
    | nil_mix =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply .nil_mix .refl) (.apply x .refl)
    | mix_nil => cases x <;> cases hₐ.congr mix₁_kind
    | mix₀ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply (.mix₀ y) .refl) (.apply (.mix₁ x) .refl)
    | mix₁ y =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mix₁ (ih y rfl)
    | mix_assoc =>
      cases hₐ.congr unmix₀
      cases hₐ.congr unmix₁
      exact .mk (.apply .mix_assoc .refl) (.apply (.mix₁ (.mix₁ x)) .refl)
    | _ => cases hₐ.congr kind
  | swap_swap | cup_swap | swap_cap =>
    cases y
    all_goals
      try first
      | . cases hₐ.congr kind
      | . cases hₐ.congr cat₀_kind
      | . cases hₐ.congr cat₁_kind
      | . cases hₐ.congr uncat₀
      | . cases hₐ.congr uncat₁
      | . exact .mk .refl .refl
    all_goals rename EqvA _ _ _ _ => y
    cases y <;> cases hₐ.congr cat₀_kind
    cases y <;> cases hₐ.congr cat₁_kind
  | _ => sorry

def _no_nil_eq {h : _} (hₐ : EqN a nil) : ¬ EqvA S h a b := by intro x; cases x <;> cases hₐ.congr kind
def no_nil_eq {h : _} : ¬ EqvA S h nil a := _no_nil_eq rfl

-- set_option maxHeartbeats 2000000

-- def comm2
--   {i₀ o₀ : Nat} {a₀ : Net S i₀ o₀}
--   {i₁ o₁ : Nat} {a₁ : Net S i₁ o₁}
--   {h₀ h₁ : _} (x : EqvA S h₀ a₀ b) (y : EqvA S h₁ a₁ c)
--   (hₐ : EqN a₀ a₁)
--   : EqvN S (by cases hₐ; simp [h₀] at h₁; simp [*]) b c  := by
--   induction x generalizing i₁ o₁ cᵢ cₒ
--   case' mix₀ | mix₁ | cat₀ | cat₁ =>
--     rename_i x ih
--   all_goals
--     try cases y
--     all_goals
--       try first
--       | . cases hₐ.congr kind
--       | . cases hₐ.congr cat₀_kind
--       | . cases hₐ.congr cat₁_kind
--       | . cases hₐ.congr mix₀_kind
--       | . cases hₐ.congr mix₁_kind
--       | . try
--             cases hₐ.congr unmix₀
--             cases hₐ.congr unmix₁
--           try
--             cases hₐ.congr uncat₀
--             cases hₐ.congr uncat₁
--           exact .mk .refl .refl
--   save

--   case mix₀.nil_mix | nil_mix.mix₀ | mix₁.mix_nil | mix₀.nil_mix =>
--     . cases hₐ.congr unmix₀
--       cases hₐ.congr unmix₁
--       exfalso
--       apply no_nil_eq
--       assumption


--   stop


  -- repeat sorry


-- -> -> -> <-   <-   ->   -> <-
-- -> -> -> <-   ->   <-   -> <-

/-

  a₀ a₁

  Eqv a₀ a₁
  Rd a₀ b
  Rd a₁ c



  Eqv a₀ a
  Eqv a₁ a
  Rd a b'
  Rd a c'
  Eqv b b'
  Eqv c c'

-/
