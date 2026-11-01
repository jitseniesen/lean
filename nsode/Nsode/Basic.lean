import Mathlib

/-! Basic abbreviations for the Numerical Solution of ODEs package -/

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev ODE (n : ℕ) := ℝ → Rn n → Rn n

/- The function φ satisfies the ODE y' = f(t,y) -/
def IsSolutionOnSet {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt φ (f t (φ t)) s t

def IsSolutionOnInterval {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (a b : ℝ) : Prop :=
  IsSolutionOnSet f φ (Set.Icc a b)
