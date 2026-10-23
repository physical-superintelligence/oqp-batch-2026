module

public import CGLMPBounds.Hardy.PositivePinchingSimilarity
public import CGLMPBounds.Hardy.PositivePinchingDensity
public import CGLMPBounds.Hardy.SpectrumImaginaryBound

@[expose] public section


/-! The exact C.12 majorant in the Hilbert operator norm. A concrete balancing
similarity reduces the pencil to a Hermitian part and a perturbation of norm
sqrt(1-x²)‖D‖. All characteristic roots retain algebraic multiplicity. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positivePinching_balanced_diagonal_hermitian {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (hY : Y.IsHermitian) (x y : ℝ) :
    ((B - (x : ℂ) • (1 : Matrix ι ι ℂ)) *
      (positivePinchingPart B Y - (y : ℂ) • 1)).IsHermitian := by
  have hfirst := positivePinching_shift_hermitian hB x
  have hsecond := (positivePinching_part_hermitian hB hY).sub
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (y : ℂ) by simp [isSelfAdjoint_iff]))
  change (_ * _)ᴴ = _
  rw [conjTranspose_mul, hsecond.eq, hfirst.eq]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul]
  rw [← positivePinching_part_commute hB2]
  module

lemma positivePinching_norm_B_mul {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (A : Matrix ι ι ℂ) :
    ‖B * A‖ = ‖A‖ := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  have hunit : B ∈ unitary (Matrix ι ι ℂ) := by
    constructor
    · change Bᴴ * B = 1
      rw [hB.eq, hBB]
    · change B * Bᴴ = 1
      rw [hB.eq, hBB]
  exact CStarRing.norm_mem_unitary_mul A hunit

theorem positivePinching_pencil_spectrum_abs_im_le {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (hY : Y.IsHermitian)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (y : ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ ((B - (x : ℂ) • (1 : Matrix ι ι ℂ)) *
      (Y - (y : ℂ) • 1))) :
    |z.im| ≤ Real.sqrt (1 - x ^ 2) * ‖positivePinchingOffdiag B Y‖ := by
  obtain ⟨U, hU⟩ := positivePinching_exists_balancing_unit (Y := Y) hB2 hx y
  have hs : z ∈ spectrum ℂ
      ((B - (x : ℂ) • (1 : Matrix ι ι ℂ)) *
        (positivePinchingPart B Y - (y : ℂ) • 1) +
          (Real.sqrt (1 - x ^ 2) : ℂ) • (B * positivePinchingOffdiag B Y)) := by
    rw [← hU, spectrum.units_conjugate']
    exact hz
  have h := matrix_spectrum_abs_im_le_norm_perturbation
    (positivePinching_balanced_diagonal_hermitian hB hB2 hY x y) hs
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), positivePinching_norm_B_mul hB hB2] using h

theorem positivePinching_density_le_majorant [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (y : ℝ) :
    positivePinchingDensity B Y (x, y) ≤
      ‖positivePinchingOffdiag B Y‖ / (2 * Real.pi * Real.sqrt (1 - x ^ 2)) := by
  let A := (B - (x : ℂ) • (1 : Matrix ι ι ℂ)) * (Y - (y : ℂ) • 1)
  have hsum : (A.charpoly.roots.map (fun z : ℂ => |z.im|)).sum ≤
      (Fintype.card ι : ℝ) *
        (Real.sqrt (1 - x ^ 2) * ‖positivePinchingOffdiag B Y‖) := by
    rw [charpoly_root_sum_eq_vector_sum]
    calc
      _ ≤ ∑ _i : ι, Real.sqrt (1 - x ^ 2) * ‖positivePinchingOffdiag B Y‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact positivePinching_pencil_spectrum_abs_im_le hB hB2 hY hx y
          (Matrix.mem_spectrum_of_isRoot_charpoly
            (Polynomial.isRoot_of_mem_roots (charpolyRootVector_mem A i)))
      _ = _ := by simp
  have hp := positivePinching_strip_denominator_pos hx
  have hs := Real.sqrt_pos.mpr hp
  have hr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  change (if x ∈ Set.Ioo (-1 : ℝ) 1 then
    positivePinchingOmega B Y x y / (1 - x ^ 2) else 0) ≤ _
  rw [if_pos hx]
  unfold positivePinchingOmega
  change (A.charpoly.roots.map (fun z : ℂ => |z.im|)).sum /
    (2 * Real.pi * Fintype.card ι) / (1 - x ^ 2) ≤ _
  calc
    _ ≤ ((Fintype.card ι : ℝ) *
        (Real.sqrt (1 - x ^ 2) * ‖positivePinchingOffdiag B Y‖)) /
        (2 * Real.pi * Fintype.card ι) / (1 - x ^ 2) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hsum (by positivity)) hp.le
    _ = _ := by
      have hsq := Real.sq_sqrt hp.le
      have hsdiv : Real.sqrt (1 - x ^ 2) / (1 - x ^ 2) =
          1 / Real.sqrt (1 - x ^ 2) := by
        apply (div_eq_div_iff (ne_of_gt hp) (ne_of_gt hs)).mpr
        simpa only [one_mul, pow_two] using hsq
      calc
        _ = (‖positivePinchingOffdiag B Y‖ / (2 * Real.pi)) *
            (Real.sqrt (1 - x ^ 2) / (1 - x ^ 2)) := by
          field_simp [ne_of_gt hr, Real.pi_ne_zero, ne_of_gt hp] <;> ring
        _ = _ := by rw [hsdiv]; ring

end
end CGLMPBounds.Hardy
