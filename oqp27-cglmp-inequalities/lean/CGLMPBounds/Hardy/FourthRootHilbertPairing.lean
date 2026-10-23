module

public import CGLMPBounds.Hardy.FourthRootCircleBasics
public import CGLMPBounds.Hardy.MatrixHilbertBilinear
public import CGLMPBounds.Circulation.Projection

@[expose] public section


/-! The equality in literal C.16 from matrix Parseval and bilinear Hilbert
skew-symmetry. The source's W lift, negative energy, and A/B are all actual
functions; no energy identity is supplied as a premise. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
open scoped ComplexConjugate
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance fourthRootHilbertPairingENormedAddMonoid {r : ℕ} :
    ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

 theorem matrix_circle_trace_linearCombination {r : ℕ}
    (A B C D : UnitCircle → Circulation.Mat r)
    (hA : MemLp A 2 circleMeasure) (hB : MemLp B 2 circleMeasure)
    (hC : MemLp C 2 circleMeasure) (hD : MemLp D 2 circleMeasure) (a b c d : ℂ) :
    (∫ t, Circulation.tr ((a • A t+b • B t)*(c • C t+d • D t)) ∂circleMeasure) =
      (a*c)*(∫ t, Circulation.tr (A t*C t) ∂circleMeasure) +
      (a*d)*(∫ t, Circulation.tr (A t*D t) ∂circleMeasure) +
      ((b*c)*(∫ t, Circulation.tr (B t*C t) ∂circleMeasure) +
      (b*d)*(∫ t, Circulation.tr (B t*D t) ∂circleMeasure)) := by
  have hAC := matrix_circle_trace_mul_integrable A C hA hC
  have hAD := matrix_circle_trace_mul_integrable A D hA hD
  have hBC := matrix_circle_trace_mul_integrable B C hB hC
  have hBD := matrix_circle_trace_mul_integrable B D hB hD
  have hpoint (t : UnitCircle) :
      Circulation.tr ((a • A t+b • B t)*(c • C t+d • D t)) =
        ((a*c)*Circulation.tr (A t*C t) + (a*d)*Circulation.tr (A t*D t)) +
          ((b*c)*Circulation.tr (B t*C t) + (b*d)*Circulation.tr (B t*D t)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Circulation.tr_add, Circulation.tr_smul]
    ring
  simp_rw [hpoint]
  rw [integral_add (((hAC.const_mul (a*c)).fun_add (hAD.const_mul (a*d))))
      (((hBC.const_mul (b*c)).fun_add (hBD.const_mul (b*d)))),
    integral_add (hAC.const_mul (a*c)) (hAD.const_mul (a*d)),
    integral_add (hBC.const_mul (b*c)) (hBD.const_mul (b*d))]
  simp only [integral_const_mul]

theorem fourthRootCircle_reconstruction {r : ℕ} (U : ℝ → Circulation.Mat r)
    (t : UnitCircle) :
    fourthRootCircleLift U t = ((1+Complex.I)/2) • fourthRootCircleA U t +
      ((1-Complex.I)/2) • fourthRootCircleB U t := by
  rw [← hermitianParts_reconstruct (fourthRootCircleLift U t)]
  simp only [fourthRootCircleA, fourthRootCircleB]
  module

theorem fourthRootCircle_conj_reconstruction {r : ℕ} (U : ℝ → Circulation.Mat r)
    (t : UnitCircle) :
    (fourthRootCircleLift U t)ᴴ = conj ((1+Complex.I)/2) • fourthRootCircleA U t +
      conj ((1-Complex.I)/2) • fourthRootCircleB U t := by
  conv_lhs => rw [fourthRootCircle_reconstruction]
  have hA := (hermitianRealPart_isHermitian (fourthRootCircleLift U t)).add
    (hermitianImagPart_isHermitian (fourthRootCircleLift U t))
  have hB := (hermitianRealPart_isHermitian (fourthRootCircleLift U t)).sub
    (hermitianImagPart_isHermitian (fourthRootCircleLift U t))
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def]
  rw [show (fourthRootCircleA U t)ᴴ = fourthRootCircleA U t from hA.eq,
    show (fourthRootCircleB U t)ᴴ = fourthRootCircleB U t from hB.eq]

theorem fourthRootCircle_complex_pairing {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) :
    (∫ t, Circulation.tr ((fourthRootCircleLift U t)ᴴ *
      matrixHilbert (fourthRootCircleLift U) t) ∂circleMeasure) =
      -Complex.I * (∫ t, Circulation.tr (fourthRootCircleA U t *
        matrixHilbert (fourthRootCircleB U) t) ∂circleMeasure) := by
  obtain ⟨hA,hB⟩ := fourthRootCircle_parts_memLp U hU hunit
  have hlin := matrixHilbert_linearCombination _ _ hA hB
    ((1+Complex.I)/2) ((1-Complex.I)/2)
  have hrec : (fun t => ((1+Complex.I)/2) • fourthRootCircleA U t +
      ((1-Complex.I)/2) • fourthRootCircleB U t) = fourthRootCircleLift U := by
    funext t
    exact (fourthRootCircle_reconstruction U t).symm
  rw [hrec] at hlin
  calc
    _ = ∫ t, Circulation.tr
        ((conj ((1+Complex.I)/2) • fourthRootCircleA U t +
          conj ((1-Complex.I)/2) • fourthRootCircleB U t) *
        (((1+Complex.I)/2) • matrixHilbert (fourthRootCircleA U) t +
          ((1-Complex.I)/2) • matrixHilbert (fourthRootCircleB U) t)) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [hlin] with t ht
      rw [ht, fourthRootCircle_conj_reconstruction]
    _ = _ := by
      rw [matrix_circle_trace_linearCombination _ _ _ _ hA hB
        (matrixHilbert_memLp _) (matrixHilbert_memLp _),
        matrixHilbert_bilinear_self _ hA, matrixHilbert_bilinear_self _ hB,
        matrixHilbert_bilinear_cross _ _ hA hB]
      norm_num [Complex.I_sq, map_ofNat]
      <;> ring

theorem fourthRootCircle_energy_one {r : ℕ} (hr : 0 < r) (U : ℝ → Circulation.Mat r)
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) :
    matrixCircleEnergy (fourthRootCircleLift U) = 1 := by
  unfold matrixCircleEnergy
  calc
    _ = ∫ _ : UnitCircle, (1 : ℝ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [fourthRootCircleLift_unitary U hunit] with t ht
      simp only [Circulation.hsSq, Circulation.reTr_eq, ht, Matrix.trace_one,
        Fintype.card_fin, Complex.natCast_re]
      exact div_self (by exact_mod_cast hr.ne')
    _ = 1 := by simp

theorem fourthRootCircle_hilbert_pairing {r : ℕ} (hr : 0 < r) (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
        (1 : Circulation.Mat r)) :
    Integrable (fun t => Circulation.reTr
      (fourthRootCircleA U t * matrixHilbert (fourthRootCircleB U) t)) circleMeasure ∧
    1 - 2 * Partition.matrixNegativeFourierEnergy U =
      ∫ t, Circulation.reTr
        (fourthRootCircleA U t * matrixHilbert (fourthRootCircleB U) t) ∂circleMeasure := by
  obtain ⟨hA,hB⟩ := fourthRootCircle_parts_memLp U hU hunit
  have hi := matrix_circle_trace_mul_integrable (fourthRootCircleA U)
    (matrixHilbert (fourthRootCircleB U)) hA (matrixHilbert_memLp (fourthRootCircleB U))
  refine ⟨hi.re, ?_⟩
  have hW := fourthRootCircleLift_memLp U hU hunit
  have hU2 := unitary_function_memLp U hU hunit
  have h := matrix_hilbert_signed_energy (fourthRootCircleLift U) hW
  have hz := fourthRootCircleLift_mean_zero U (hU2.integrable (by norm_num))
  have hzcoeff : matrixCircleFourierCoefficient (fourthRootCircleLift U) 0 = 0 := by
    simpa only [matrixCircleFourierCoefficient, fourierCoeff, neg_zero, fourier_zero,
      one_smul] using hz
  rw [fourthRootCircle_energy_one hr U hunit, hzcoeff,
    show Circulation.hsSq (0 : Circulation.Mat r) = 0 by
      simp [Circulation.hsSq, Circulation.reTr, Circulation.tr], sub_zero,
    fourthRootCircleLift_negativeEnergy U (fun i j => (hU2.eval i).eval j),
    fourthRootCircle_complex_pairing U hU hunit] at h
  have he : -( -Complex.I * (∫ t, Circulation.tr (fourthRootCircleA U t *
      matrixHilbert (fourthRootCircleB U) t) ∂circleMeasure)).im =
      (∫ t, Circulation.tr (fourthRootCircleA U t *
        matrixHilbert (fourthRootCircleB U) t) ∂circleMeasure).re := by
    simp [Complex.mul_im]
  rw [he] at h
  have hreal := integral_re hi
  simp only [RCLike.re_to_complex] at hreal
  simpa only [Circulation.reTr] using h.symm.trans hreal.symm

end
end CGLMPBounds.Hardy
