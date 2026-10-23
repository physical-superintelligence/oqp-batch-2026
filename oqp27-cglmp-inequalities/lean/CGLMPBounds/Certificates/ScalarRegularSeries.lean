module

public import CGLMPBounds.Certificates.ScalarCosecant

@[expose] public section


/-!
# Uniform bounds for the regularized cosecant series

These bounds prepare integration against the actual binomial beta density.
-/

namespace CGLMPBounds.Certificates
noncomputable section

def scalarRegularTerm (i : ℕ) (y : ℝ) : ℝ :=
  scalarCosecantCoefficient (i + 1) * y ^ (2 * i + 1)

def scalarRegularMajorant (i : ℕ) : ℝ := (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (i + 1)

def scalarRegularSeries (y : ℝ) : ℝ := ∑' i : ℕ, scalarRegularTerm i y

theorem scalarRegularTerm_continuous (i : ℕ) : Continuous (scalarRegularTerm i) := by
  unfold scalarRegularTerm
  fun_prop

theorem scalarRegularTerm_bound (i : ℕ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : ‖scalarRegularTerm i y‖ ≤ scalarRegularMajorant i := by
  have hc := scalarCosecantCoefficient_pos_lt (i + 1) (by omega)
  have hy0 : 0 ≤ y := hy.1
  have hp : y ^ (2 * i + 1) ≤ 1 := pow_le_one₀ hy.1 hy.2
  rw [scalarRegularTerm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.1.le (by positivity))]
  exact (mul_le_of_le_one_right hc.1.le hp).trans hc.2.le

theorem scalarRegularMajorant_summable : Summable scalarRegularMajorant := by
  have hg : Summable (fun i : ℕ => (1 / 4 : ℝ) ^ i) :=
    summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h : Summable (fun i : ℕ => (1 / 4 : ℝ) ^ (i + 1)) :=
    (summable_nat_add_iff 1).2 hg
  change Summable (fun i : ℕ => (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (i + 1))
  exact h.mul_left (4 / 3 : ℝ)

theorem scalarRegularTerm_summable {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun i => scalarRegularTerm i y) :=
  Summable.of_norm_bounded scalarRegularMajorant_summable (fun i => scalarRegularTerm_bound i hy)

theorem scalarRegularSeries_eq {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    scalarRegularSeries y = 1 / Real.sin (Real.pi * y / 2) - 2 / (Real.pi * y) :=
  (scalar_cosecant_hasSum_zero_le ⟨hy.1, by linarith [hy.2]⟩).tsum_eq

end
end CGLMPBounds.Certificates
