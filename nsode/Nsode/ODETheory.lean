import Mathlib.Analysis.Calculus.ContDiff.Comp
import Nsode.Basic

/-! ODE theory -/

/- Convert toSpanSingletonCLE to toSpanSingleton -/
lemma toSpanSingletonCLE_apply {n : ℕ} (x : Rn n) :
    (ContinuousLinearMap.toSpanSingletonCLE : Rn n ≃L[ℝ] (ℝ →L[ℝ] Rn n)) x
    = ContinuousLinearMap.toSpanSingleton ℝ x := by
  trans (ContinuousLinearMap.toSpanSingletonLE ℝ ℝ (Rn n)) x
  · rfl
  · simp

/- If f is C¹ and φ solves the ODE y' = f(y), then φ is C² -/
theorem ode_contDiffOn_two {n : ℕ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {f : Rn n → Rn n} {φ : ℝ → Rn n} (hf : ContDiff ℝ 1 f)
    (hsol : ∀ t ∈ s, HasDerivWithinAt φ (f (φ t)) s t) :
    ContDiffOn ℝ (2 : ℕ∞) φ s := by
  /- A = Dφ is the Fréchet derivative of φ, given by Dφ(t)(h) = hf(φ(t)) -/
  let A : ℝ → (ℝ →L[ℝ] Rn n) :=
    fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (f (φ t))
  let CLMtoCLE : Rn n ≃L[ℝ] (ℝ →L[ℝ] Rn n) := ContinuousLinearMap.toSpanSingletonCLE
  have hAeq : (⇑CLMtoCLE ∘ f ∘ φ) = A := by
    funext t
    simp [A, CLMtoCLE, toSpanSingletonCLE_apply]
  have A_is_Fderiv : ∀ x ∈ s, HasFDerivWithinAt φ (A x) s x := by
    intro t ht
    simpa [A] using (hsol t ht).hasFDerivWithinAt
  /-
  -- Prove that the solution φ is C¹ by proving that A is its Fréchet derivative
  -- and that A is C⁰ because A = f(φ(t)) where both f and φ are C⁰
  -/
  have hφ₁ : ContDiffOn ℝ 1 φ s := by
    change ContDiffOn ℝ (0 + 1) φ s
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs]
    constructor
    · intro h; cases h
    · use A
      constructor
      · -- need to show that A is C⁰
        apply contDiffOn_zero.mpr
        have hφcont : ContinuousOn φ s := by intro t ht; exact (hsol t ht).continuousWithinAt
        have hfOn : ContinuousOn f Set.univ := hf.continuous.continuousOn
        have hcomp : ContinuousOn (f ∘ φ) s := hfOn.comp hφcont (by intro x hx; simp)
        have hCLEOn : ContinuousOn ⇑CLMtoCLE Set.univ :=
          (ContinuousLinearEquiv.continuous ContinuousLinearMap.toSpanSingletonCLE).continuousOn
        have hAcont : ContinuousOn (⇑CLMtoCLE ∘ f ∘ φ) s := hCLEOn.comp hcomp (by intro x hx; simp)
        rw [← hAeq]
        exact hAcont
      · exact A_is_Fderiv
  /-
  -- Prove that the solution φ is C¹ by proving that A is its Fréchet derivative
  -- and that A is C¹ because A = f(φ(t)) where both f and φ are C¹ 
  -- (the latter from the previous step)
  -/
  change ContDiffOn ℝ (1 + 1) φ s
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs]
  constructor
  · intro h; cases h
  · use A; constructor
    · -- need to show that A is C¹
      have hrhs : ContDiffOn ℝ 1 (f ∘ φ) s := by
        have hfOn : ContDiffOn ℝ 1 f Set.univ := hf.contDiffOn
        have hmaps : Set.MapsTo φ s Set.univ := by intro x hx; simp
        have hcomp : ContDiffOn ℝ 1 (f ∘ φ) s := hfOn.comp hφ₁ hmaps
        change ContDiffOn ℝ 1 (f ∘ φ) s
        exact hcomp
      have hCLE : ContDiff ℝ 1 ⇑CLMtoCLE := ContinuousLinearEquiv.contDiff CLMtoCLE
      have hCLEOn : ContDiffOn ℝ 1 ⇑CLMtoCLE Set.univ := hCLE.contDiffOn
      have hAcd : ContDiffOn ℝ 1 (⇑CLMtoCLE ∘ f ∘ φ) s := by
        simpa using hCLEOn.comp hrhs (by intro x hx; simp)
      rw [← hAeq]
      exact hAcd
    · exact A_is_Fderiv
