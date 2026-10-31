import Nsode.Basic

/-! Convergence proof for Euler method -/

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev ODE (n : ℕ) := ℝ → Rn n → Rn n

/- One step of the Euler method for y' = f(t,y) starting from t and h with stepsize h -/
def euler_step {n : ℕ} (f : ODE n) (h t : ℝ) (y : Rn n) : Rn n :=
  y + h • f t y

/- The infinite sequence produced by the Euler method -/ 
def euler_method {n : ℕ} (f : ODE n) (t₀ h : ℝ) (y₀ : Rn n) : ℕ → Rn n
  | 0 => y₀
  | k + 1 => euler_step f h (t₀ + h * k) (euler_method f t₀ h y₀ k)

/- The function φ satisfies the ODE y' = f(t,y) -/
def IsSolutionOnInterval {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (a b : ℝ) : Prop :=
  ∀ t ∈ Set.Icc a b, derivWithin φ (Set.Icc a b) t = f t (φ t)

/- Local error of Euler's method at a time t given the solution -/
def local_error {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (h : ℝ) : ℝ → Rn n :=
  fun t => φ (t + h) - euler_step f h t (φ t)

/- Rewrite local error using solution without referring to ODE -/
theorem local_error_eq_sub_derivWithin {n : ℕ} {f : ODE n} {φ : ℝ → Rn n} {t h : ℝ}
    (hh : 0 ≤ h) (hsol : IsSolutionOnInterval f φ t (t + h)) :
    local_error f φ h t = φ (t + h) - φ t - h • derivWithin φ (Set.Icc t (t + h)) t := by
  unfold local_error euler_step
  have hφ : derivWithin φ (Set.Icc t (t + h)) t = f t (φ t) := by
    apply hsol
    constructor <;> linarith
  rw [← hφ]
  abel

/- Explicit form of first order Taylor polynomial in an interval -/
lemma taylor_within_eval_one {n : ℕ} (φ : ℝ → Rn n) (a b x : ℝ) :
    taylorWithinEval φ 1 (Set.Icc a b) a x = φ a + (x - a) • derivWithin φ (Set.Icc a b) a := by
  rw [taylorWithinEval_succ]
  simp [taylor_within_zero_eval]

/- Bound for local error on interval [a,b] assuming solution is given and nice -/
/- The constant M can be sharpened to M / 2 -/
theorem local_error_bound {n : ℕ} {f : ODE n} {φ : ℝ → Rn n} {M t h : ℝ}
    (hsol : IsSolutionOnInterval f φ t (t + h))
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc t (t + h))) (hh : 0 < h)
    (hM : ∀ s ∈ Set.Icc t (t + h), ‖iteratedDerivWithin 2 φ (Set.Icc t (t + h)) s‖ ≤ M) :
    ‖local_error f φ h t‖ ≤ M * h^2 := by
  rw [local_error_eq_sub_derivWithin hh.le hsol]
  have hab : t ≤ t + h := by linarith
  have hx : t + h ∈ Set.Icc t (t + h) := by constructor <;> linarith
  have hrem := taylor_mean_remainder_bound hab hφ hx hM
  rw [taylor_within_eval_one] at hrem
  rw [show t + h - t = h by abel] at hrem
  norm_num at hrem
  convert hrem using 2
  abel

/- ODE theory for constructing the solution -/
theorem exists_IsSolutionOnInterval {n : ℕ} {f : ODE n} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {y₀ : Rn n} {a r L K : NNReal}
    (hmono : tmin < tmax) (hPL : IsPicardLindelof f t₀ y₀ a r L K) :
    ∃ φ : ℝ → Rn n, φ t₀ = y₀ ∧ IsSolutionOnInterval f φ tmin tmax := by
  have hy₀ : y₀ ∈ Metric.closedBall y₀ ↑r := by simp [Metric.mem_closedBall]
  obtain ⟨φ, hinit, hderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (x := y₀) hy₀
  use φ, hinit
  intro t ht
  have hUD : UniqueDiffWithinAt ℝ (Set.Icc tmin tmax) t :=
    (uniqueDiffOn_Icc hmono) t ht
  exact (hderiv t ht).derivWithin hUD
