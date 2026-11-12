import Nsode.Basic

/-! Proofs for general methods -/

def Φ_domain {n : ℕ} (φ : ℝ → Rn n) (a b γ h₀ : ℝ) :
    Set (ℝ × Rn n × ℝ) :=
  {q | q.1 ∈ Set.Icc a b ∧ ‖q.2.1 - φ q.1‖ ≤ γ ∧ q.2.2 ∈ Set.Icc 0 h₀}

-- A local error of order p+1 and a Lipschitz increment give a global order-p bound
-- Theorem 7.2.2.3 from Bulirsch & Stoer
theorem global_error_bound {n : ℕ} (f : ODE n)
    (φ : ℝ → Rn n) (Φ : Increment n)
    (a b t₀ : ℝ) (y₀ : Rn n) (h₀ γ M N : ℝ) (p : ℕ)
    (ht₀ : t₀ ∈ Set.Icc a b) (hsol : IsSolutionOnInterval f φ a b)
    (hinit : φ t₀ = y₀) (hh₀ : 0 < h₀) (hγ : 0 < γ)
    (hM : 0 < M) (hN : 0 < N) (hp : 0 < p)
    (hcont : ContinuousOn (fun q : ℝ × Rn n × ℝ => Φ f q.1 q.2.1 q.2.2)
      (Φ_domain φ a b γ h₀))
    (hlip : ∀ t y₁ y₂ h, (t, y₁, h) ∈ Φ_domain φ a b γ h₀ →
      (t, y₂, h) ∈ Φ_domain φ a b γ h₀ →
      ‖Φ f t y₁ h - Φ f t y₂ h‖ ≤ M * ‖y₁ - y₂‖)
    (hloc : ∀ t ∈ Set.Icc a b, ∀ h ∈ Set.Icc 0 h₀,
      ‖local_error Φ f φ h t‖ ≤ N * h ^ (p + 1)) :
    ∃ hmax, 0 < hmax ∧ hmax ≤ h₀ ∧
      ∀ t ∈ Set.Icc t₀ b, ∀ k : ℕ, k ≥ 1 → (t - t₀) / k ≤ hmax →
        ‖global_error Φ f φ t₀ t ((t - t₀) / k)‖ ≤
          ((t - t₀) / k) ^ p * N * (Real.exp (M * (t - t₀)) - 1) / M := by
  sorry
