import Nsode.Basic
import Nsode.ODETheory

/-! Convergence proof for Euler method -/

/- One step of the Euler method for y' = f(t,y) starting from t and h with stepsize h -/
def euler_step {n : ℕ} (f : ODE n) (h t : ℝ) (y : Rn n) : Rn n :=
  y + h • f t y

/- The infinite sequence produced by the Euler method -/ 
def euler_method {n : ℕ} (f : ODE n) (t₀ h : ℝ) (y₀ : Rn n) : ℕ → Rn n
  | 0 => y₀
  | k + 1 => euler_step f h (t₀ + h * k) (euler_method f t₀ h y₀ k)

/- Local error of Euler's method at a time t given the solution -/
def local_error {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (h : ℝ) : ℝ → Rn n :=
  fun t => φ (t + h) - euler_step f h t (φ t)

/- Rewrite local error using solution without referring to ODE -/
theorem local_error_eq_sub_derivWithin {n : ℕ} {f : ODE n} {φ : ℝ → Rn n} {t h : ℝ}
    (hh : 0 < h) (hsol : IsSolutionOnInterval f φ t (t + h)) : 
    local_error f φ h t = φ (t + h) - φ t - h • derivWithin φ (Set.Icc t (t + h)) t := by
  let I := Set.Icc t (t + h)
  unfold local_error euler_step
  have hineq : t < t + h := by simp [hh]
  have ht : t ∈ I := by simp [I, hh.le]
  have hunique : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hineq
  have hφ : derivWithin φ I t = f t (φ t) := (hsol t ht).derivWithin (hunique t ht)
  rw [← hφ]
  abel

/- Explicit form of first order Taylor polynomial in an interval -/
lemma taylor_within_eval_one {n : ℕ} (φ : ℝ → Rn n) (a b x : ℝ) :
    taylorWithinEval φ 1 (Set.Icc a b) a x = φ a + (x - a) • derivWithin φ (Set.Icc a b) a := by
  rw [taylorWithinEval_succ]
  simp [taylor_within_zero_eval]

/- Bound for local error on interval [a,b] assuming solution is given and nice -/
/- The constant M can be sharpened to M / 2 -/
theorem local_error_bound' {n : ℕ} {f : ODE n} {φ : ℝ → Rn n} {M t h : ℝ}
    (hsol : IsSolutionOnInterval f φ t (t + h))
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc t (t + h))) (hh : 0 < h)
    (hM : ∀ s ∈ Set.Icc t (t + h), ‖iteratedDerivWithin 2 φ (Set.Icc t (t + h)) s‖ ≤ M) :
    ‖local_error f φ h t‖ ≤ M * h^2 := by
  rw [local_error_eq_sub_derivWithin hh hsol]
  have hab : t ≤ t + h := by linarith
  have hx : t + h ∈ Set.Icc t (t + h) := by constructor <;> linarith
  have hrem := taylor_mean_remainder_bound hab hφ hx hM
  rw [taylor_within_eval_one] at hrem
  rw [show t + h - t = h by abel] at hrem
  norm_num at hrem
  convert hrem using 2
  abel

/- Local error of Euler is O(h^2) if the rhs of the ODE is C^2 -/
theorem local_error_bound_uniform {n : ℕ} {f : ODE n} {φ : ℝ → Rn n} {t hmax : ℝ}
    (hf : ContDiff ℝ 1 f.uncurry) (hpos : 0 < hmax) (hsol : IsSolutionOnInterval f φ t (t + hmax)) :
    ∃ M ≥ 0, ∀ h, 0 < h → h ≤ hmax → ‖local_error f φ h t‖ ≤ M * h^2 := by
  let I := Set.Icc t (t + hmax)
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  have hφC2 := ode_contDiffOn_two hI hf hsol
  have hineq : t < t + hmax := by linarith
  obtain ⟨M, hMpos, hMbnd⟩ := exists_bound_iteratedDerivWithin_two hineq hφC2
  use M, hMpos
  intro h hhpos hhbnd
  let I' := Set.Icc t (t + h)
  have hsol' : IsSolutionOnInterval f φ t (t + h) := by
    intro s hs'
    have hI' : I' ⊆ I := by apply Set.Icc_subset_Icc_right (by linarith)
    have hs : s ∈ I := hI' hs'
    exact (hsol s hs).mono hI'
  have hφ' : ContDiffOn ℝ 2 φ (Set.Icc t (t + h)) := sorry
  have hM' : ∀ s ∈ Set.Icc t (t + h), ‖iteratedDerivWithin 2 φ (Set.Icc t (t + h)) s‖ ≤ M := sorry
  apply local_error_bound' hsol' hφ' hhpos hM'
