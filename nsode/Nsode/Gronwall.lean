import Nsode.Basic

/-! Discrete Grönwall inequality, Lemma 7.2.2.2 from Burlisch & Stoer -/

/- If |ξ (i + 1)| < (1 + δ) |ξ i| + B for all i, where δ > 0 and B ≥ 0,
   then |ξ n| ≤ exp(nδ) |ξ 0| + B (exp(nδ) - 1) / δ for all n. -/
theorem gronwall_bound {d : ℕ} {ξ : ℕ → Rn d} {N : ℕ} {δ B : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B)
    (hstep : ∀ i < N, ‖ξ (i + 1)‖ ≤ (1 + δ) * ‖ξ i‖ + B) :
    ∀ n ≤ N, ‖ξ n‖ ≤ Real.exp ((n : ℝ) * δ) * ‖ξ 0‖ + B * (Real.exp ((n : ℝ) * δ) - 1) / δ := by
  have aux : ∀ n ≤ N, ‖ξ n‖ ≤ (1 + δ) ^ n * ‖ξ 0‖ + B * ∑ k ∈ Finset.range n, (1 + δ)^k := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        ‖ξ (n + 1)‖ ≤ (1 + δ) * ‖ξ n‖ + B := hstep n hn
        _ ≤ (1 + δ) * ((1 + δ) ^ n * ‖ξ 0‖ + B * ∑ k ∈ Finset.range n, (1 + δ)^k) + B := by
          apply add_le_add_left
          have hnonneg : 0 ≤ (1 + δ) := by linarith [hδ]
          apply mul_le_mul_of_nonneg_left (ih (by linarith)) hnonneg
        _ = (1 + δ) ^ (n + 1) * ‖ξ 0‖ + (1 + δ) * B * (∑ k ∈ Finset.range n, (1 + δ)^k) + B := by
          ring
        _ = (1 + δ) ^ (n + 1) * ‖ξ 0‖ + B * (∑ k ∈ Finset.range n, (1 + δ) ^ (k + 1)) + B := by
          simp only [pow_succ]
          rw [← Finset.sum_mul]
          ring
        _ = (1 + δ) ^ (n + 1) * ‖ξ 0‖ + B * (∑ k ∈ Finset.range n, (1 + δ) ^ (k + 1) + 1) := by ring
        _ = (1 + δ) ^ (n + 1) * ‖ξ 0‖ + B * (∑ k ∈ Finset.range (n + 1), (1 + δ) ^ k) := by
          congr 2
          rw [Finset.sum_range_succ' (fun k => (1 + δ) ^ k) n]
          simp [add_comm]
  intro n hn
  have hexp : (1 + δ) ^ n ≤ Real.exp (n * δ) := by
    calc (1 + δ) ^ n = (δ + 1) ^ n := by ring
      _ ≤ (Real.exp δ) ^ n := by
        apply pow_le_pow_left₀ (by linarith [hδ]) (Real.add_one_le_exp δ)
      _ = Real.exp ((n : ℝ) * δ) := by
        rw [Real.exp_nat_mul]
  calc
    ‖ξ n‖ ≤ (1 + δ) ^ n * ‖ξ 0‖ + B * ∑ k ∈ Finset.range n, (1 + δ)^k := aux n hn
    _ = (1 + δ) ^ n * ‖ξ 0‖ + B * ((1 + δ) ^ n - 1) / δ := by
      rw [geom_sum_eq]
      · ring
      · apply ne_of_gt
        linarith [hδ]
    _ ≤ Real.exp ((n : ℝ) * δ) * ‖ξ 0‖ + B * (Real.exp ((n : ℝ) * δ) - 1) / δ := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      · apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hB
        · linarith [hδ]
