import Mathlib.Analysis.Calculus.ContDiff.Comp
import Nsode.Basic

/-! ODE theory -/

/- Existence of solution on an interval -/
theorem exists_IsSolutionOnInterval {n : ℕ} {f : ODE n} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {y₀ : Rn n} {a r L K : NNReal} (hPL : IsPicardLindelof f t₀ y₀ a r L K) :
    ∃ φ : ℝ → Rn n, φ t₀ = y₀ ∧ IsSolutionOnInterval f φ tmin tmax := by
  have hy₀ : y₀ ∈ Metric.closedBall y₀ ↑r := by simp [Metric.mem_closedBall]
  obtain ⟨φ, hinit, hderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (x := y₀) hy₀
  use φ, hinit
  intro t ht
  exact hderiv t ht

/- Convert toSpanSingletonCLE to toSpanSingleton -/
lemma toSpanSingletonCLE_apply {n : ℕ} (x : Rn n) :
    (ContinuousLinearMap.toSpanSingletonCLE : Rn n ≃L[ℝ] (ℝ →L[ℝ] Rn n)) x
    = ContinuousLinearMap.toSpanSingleton ℝ x := by
  trans (ContinuousLinearMap.toSpanSingletonLE ℝ ℝ (Rn n)) x
  · rfl
  · simp

/- If f is C¹ and φ solves the ODE y' = f(t,y), then φ is C² -/
theorem ode_contDiffOn_two {n : ℕ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {f : ODE n} {φ : ℝ → Rn n} (hf : ContDiff ℝ 1 f.uncurry) (hsol : IsSolutionOnSet f φ s) :
    ContDiffOn ℝ 2 φ s := by
  /- A = Dφ is the Fréchet derivative of φ, given by Dφ(t)(h) = hf(t,φ(t)) -/
  let g : ℝ → ℝ × Rn n := fun t ↦ (t, φ t)
  let rhs : ℝ → Rn n := fun t ↦ f t (φ t)
  let A : ℝ → (ℝ →L[ℝ] Rn n) :=
    fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (rhs t)
  let CLMtoCLE : Rn n ≃L[ℝ] (ℝ →L[ℝ] Rn n) := ContinuousLinearMap.toSpanSingletonCLE
  have hAeq : ⇑CLMtoCLE ∘ rhs = A := by
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
        have hfOn : ContinuousOn f.uncurry Set.univ := 
          hf.continuous.continuousOn
        have hgcont : ContinuousOn g s := by simpa [g] using continuousOn_id.prodMk hφcont
        have hcomp : ContinuousOn rhs s := hfOn.comp hgcont (by intro x hx; simp)
        have hCLEOn : ContinuousOn ⇑CLMtoCLE Set.univ :=
          (ContinuousLinearEquiv.continuous ContinuousLinearMap.toSpanSingletonCLE).continuousOn
        have hAcont : ContinuousOn (⇑CLMtoCLE ∘ rhs) s := 
          hCLEOn.comp hcomp (by intro x hx; simp)
        rw [← hAeq]
        exact hAcont
      · exact A_is_Fderiv
  /-
  -- Prove that the solution φ is C² by proving that A is its Fréchet derivative
  -- and that A is C¹ because A = f(φ(t)) where both f and φ are C¹ 
  -- (the latter from the previous step)
  -/
  change ContDiffOn ℝ (1 + 1) φ s
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs]
  constructor
  · intro h; cases h
  · use A; constructor
    · -- need to show that A is C¹
      have hrhs : ContDiffOn ℝ 1 rhs s := by
        have hfOn : ContDiffOn ℝ 1 f.uncurry Set.univ := hf.contDiffOn
        have hmaps : Set.MapsTo g s Set.univ := by intro x hx; simp
        have hgcdo : ContDiffOn ℝ 1 g s := by simpa [g] using contDiffOn_id.prodMk hφ₁
        have hcomp : ContDiffOn ℝ 1 (f.uncurry ∘ g) s := hfOn.comp hgcdo hmaps
        change ContDiffOn ℝ 1 (f.uncurry ∘ g) s
        exact hcomp
      have hCLE : ContDiff ℝ 1 ⇑CLMtoCLE := ContinuousLinearEquiv.contDiff CLMtoCLE
      have hCLEOn : ContDiffOn ℝ 1 ⇑CLMtoCLE Set.univ := hCLE.contDiffOn
      have hAcd : ContDiffOn ℝ 1 (⇑CLMtoCLE ∘ rhs) s := by
        simpa using hCLEOn.comp hrhs (by intro x hx; simp)
      rw [← hAeq]
      exact hAcd
    · exact A_is_Fderiv

/- If a function f is C² then its second derivative is bounded on a closed interval -/
theorem exists_bound_iteratedDerivWithin_two {f : ℝ → Rn n} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b)) :
    ∃ M ≥ 0, ∀ t ∈ Set.Icc a b, ‖iteratedDerivWithin 2 f (Set.Icc a b) t‖ ≤ M := by
  let I := Set.Icc a b
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  have hcont : ContinuousOn (fun x ↦ ‖iteratedDerivWithin 2 f I x‖) I := by
    have hcontF : ContinuousOn (iteratedFDerivWithin ℝ 2 f I) I :=
      hf.continuousOn_iteratedFDerivWithin (by norm_num) hI
    simp only [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    exact hcontF.norm
  have I_nonempty : I.Nonempty := by use a; simp [I, hab.le]
  obtain ⟨t₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn I_nonempty hcont
  use ‖iteratedDerivWithin 2 f I t₀‖, norm_nonneg _
  intro t ht
  exact (isMaxOn_iff.mp hmax) t ht
