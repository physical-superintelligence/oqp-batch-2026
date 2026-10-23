module

public import CGLMPBounds.Circulation.ScalarFormDecomposition
public import CGLMPBounds.Circulation.ScalarCoercivity

@[expose] public section


/-! The actual L_(e+s) coercive bound used in D.1. -/

namespace CGLMPBounds.Circulation
noncomputable section
open scoped Matrix

theorem scalarEdgeForm_error_partition_coercivity_three {d r : ℕ} [NeZero r] (hd : 3 ≤ d)
    (V : Fin d → Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1) :
    scalarForbiddenTotal V / (3 * ((d : ℝ) + 1)) ≤
      scalarEdgeForm (fun h => scalarIntegralError d h + scalarPartitionCoefficient d h) V := by
  letI : NeZero d := ⟨by omega⟩
  rw [scalarEdgeForm_error_partition_decomposition]
  simpa only [scalarForbiddenTotal, div_eq_mul_inv, one_div, mul_comm, one_mul] using
    scalar_expanded_coercivity hd V hunit hfour

theorem scalarEdgeForm_error_partition_coercivity_two {r : ℕ} [NeZero r]
    (V : Fin 2 → Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1) :
    scalarForbiddenTotal V / 9 ≤
      scalarEdgeForm (fun h => scalarIntegralError 2 h + scalarPartitionCoefficient 2 h) V := by
  have hp := fourth_root_forbidden_nonneg (V 0) (V 1)
    (hunit 0) (hunit 1) (hfour 0) (hfour 1)
  have he := Certificates.scalar_two_outcome_margin
  have hs := Certificates.scalarPartitionCoefficient_lower 2 1 (by omega) (by omega)
  norm_num at he hs
  have ha : (1 / 18 : ℝ) ≤ scalarIntegralError 2 1 + scalarPartitionCoefficient 2 1 := by
    linarith
  have hm := mul_le_mul_of_nonneg_right ha hp
  rw [scalarEdgeForm_error_partition_decomposition]
  norm_num [scalarForbiddenTotal, Fin.sum_univ_two]
  linarith

/-- The actual coefficient-form bound used immediately before (D.7)–(D.8). -/
theorem scalarEdgeForm_error_partition_coercivity {d r : ℕ} [NeZero r] (hd : 2 ≤ d)
    (V : Fin d → Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1) :
    scalarForbiddenTotal V / (3 * ((d : ℝ) + 1)) ≤
      scalarEdgeForm (fun h => scalarIntegralError d h + scalarPartitionCoefficient d h) V := by
  by_cases hd2 : d = 2
  · subst d
    convert scalarEdgeForm_error_partition_coercivity_two V hunit hfour using 1 <;> norm_num
  · exact scalarEdgeForm_error_partition_coercivity_three (by omega) V hunit hfour

end
end CGLMPBounds.Circulation
