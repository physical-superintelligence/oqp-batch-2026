module

public import CGLMPBounds.Hardy.MatrixHermitianParts
public import CGLMPBounds.Hardy.HardyMatrixPotentialContinuity

@[expose] public section


/-! A genuine Hilbert operator-norm bound for the actual root potential.
This coarser auxiliary is sufficient for C.6 radial uniform integrability.
The manuscript's sharper trace-absolute-value estimate is proved separately. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem matrixHardyPotential_norm_bound {r : ℕ} (hr : 0 < r) (X : Circulation.Mat r)
    (hstrip : ∀ z ∈ spectrum ℂ X, |z.re| ≤ 1) :
    0 ≤ matrixHardyPotential X ∧
    matrixHardyPotential X ≤ hardyStripCenterConstant + ‖hermitianImagPart X‖ := by
  have hscalar (i : Fin r) :
      0 ≤ (hardyStripPotential (charpolyRootVector X i)).re ∧
      (hardyStripPotential (charpolyRootVector X i)).re ≤
        hardyStripCenterConstant + ‖hermitianImagPart X‖ := by
    have hz := Matrix.mem_spectrum_of_isRoot_charpoly
      (Polynomial.isRoot_of_mem_roots (charpolyRootVector_mem X i))
    have hs := hardyStripRealPotential_bounds (y := (charpolyRootVector X i).im)
      (hstrip _ hz)
    have he : ((charpolyRootVector X i).re : ℂ) +
        Complex.I*(charpolyRootVector X i).im = charpolyRootVector X i := by
      apply Complex.ext <;> simp
    simp only [hardyStripRealPotential, he] at hs
    exact ⟨hs.1, hs.2.trans (add_le_add_right (matrix_spectrum_parts_rectangle X hz).2 _)⟩
  rw [matrixHardyPotential_eq_root_sum, charpoly_root_sum_eq_vector_sum]
  simp only [Fintype.card_fin]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hscalar i).1)) hr'.le
  · apply (div_le_iff₀ hr').mpr
    calc
      _ ≤ ∑ _i : Fin r, (hardyStripCenterConstant + ‖hermitianImagPart X‖) :=
        Finset.sum_le_sum (fun i _ => (hscalar i).2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end
end CGLMPBounds.Hardy
