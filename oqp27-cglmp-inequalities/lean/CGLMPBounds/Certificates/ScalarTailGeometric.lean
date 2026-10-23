module

public import CGLMPBounds.Defs.ScalarTail
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


/-!
# Exact evaluation of the geometric budget in (J.3)

We reuse the pinned Mathlib HasSum formulas for r^n, n*r^n, and n²*r^n.
This file evaluates only the displayed majorant. The identification and bounds
of the manuscript's actual coefficients r_n are not assumed or concluded.
-/

namespace CGLMPBounds.Certificates

/-- The exact geometric tail appearing after the tenth retained scalar term. -/
theorem scalar_geometric_tail_hasSum :
    HasSum (fun m : ℕ => scalarGeometricMajorant (m + 11))
      ((4 / 3 : ℝ) * (1 / 4 : ℝ) ^ 11 *
        (485 * (1 - (1 / 4 : ℝ))⁻¹ +
          88 * ((1 / 4 : ℝ) / (1 - (1 / 4 : ℝ)) ^ 2) +
          4 * ((1 / 4 : ℝ) * (1 + (1 / 4 : ℝ)) / (1 - (1 / 4 : ℝ)) ^ 3))) := by
  have hr : ‖(1 / 4 : ℝ)‖ < 1 := by norm_num
  have h0 := hasSum_geometric_of_norm_lt_one hr
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hr
  have h := (((h0.mul_left (485 : ℝ)).add (h1.mul_left (88 : ℝ))).add
    (h2.mul_left (4 : ℝ))).mul_left ((4 / 3 : ℝ) * (1 / 4 : ℝ) ^ 11)
  convert h using 1
  funext m
  simp only [scalarGeometricMajorant, Nat.cast_add, Nat.cast_ofNat, pow_add]
  ring

theorem scalar_geometric_tail_summable :
    Summable (fun m : ℕ => scalarGeometricMajorant (m + 11)) :=
  scalar_geometric_tail_hasSum.summable

/-- The exact rational number printed in (J.3), including coefficient rounding. -/
theorem scalarTruncationErrorBudget_eq :
    scalarTruncationErrorBudget = (45400712033 : ℝ) / 207360000000000 := by
  unfold scalarTruncationErrorBudget
  rw [scalar_geometric_tail_hasSum.tsum_eq]
  norm_num

/-- The strict margin epsilon_sc < epsilon_0 = 9/40000 in (J.3). -/
theorem scalarTruncationErrorBudget_lt : scalarTruncationErrorBudget < (9 : ℝ) / 40000 := by
  rw [scalarTruncationErrorBudget_eq]
  norm_num

end CGLMPBounds.Certificates
