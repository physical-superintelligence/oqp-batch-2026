module

public import CGLMPBounds.Defs.PositivePinching

@[expose] public section


/-! Elementary algebra in C.4. The inverse of the shifted involution is proved
from an actual two-sided matrix product, and the literal characteristic-root
density is identified with C.3 without changing either definition. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positivePinching_part_add_offdiag (B Y : Matrix ι ι ℂ) :
    positivePinchingPart B Y + positivePinchingOffdiag B Y = Y := by
  unfold positivePinchingOffdiag
  abel

theorem positivePinching_conjugate_conjugate {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) : B * (B * Y * B) * B = Y := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  calc
    B * (B * Y * B) * B = (B * B) * Y * (B * B) := by noncomm_ring
    _ = Y := by rw [hBB, one_mul, mul_one]

theorem positivePinching_part_conjugate {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) : B * positivePinchingPart B Y * B =
      positivePinchingPart B Y := by
  unfold positivePinchingPart
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  rw [positivePinching_conjugate_conjugate hB2]
  rw [add_comm]

theorem positivePinching_offdiag_conjugate {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) : B * positivePinchingOffdiag B Y * B =
      -positivePinchingOffdiag B Y := by
  simp only [positivePinchingOffdiag, mul_sub, sub_mul,
    positivePinching_part_conjugate hB2]
  unfold positivePinchingPart
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

theorem positivePinching_part_commute {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) : B * positivePinchingPart B Y =
      positivePinchingPart B Y * B := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  have h := congrArg (fun A : Matrix ι ι ℂ => A * B)
    (positivePinching_part_conjugate (Y := Y) hB2)
  simpa only [mul_assoc, hBB, mul_one] using h

theorem positivePinching_offdiag_anticommute {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) : B * positivePinchingOffdiag B Y =
      -(positivePinchingOffdiag B Y * B) := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  have h := congrArg (fun A : Matrix ι ι ℂ => A * B)
    (positivePinching_offdiag_conjugate (Y := Y) hB2)
  simpa only [mul_assoc, hBB, mul_one, neg_mul] using h

theorem positivePinching_part_hermitian {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hY : Y.IsHermitian) :
    (positivePinchingPart B Y).IsHermitian := by
  have hc : (B * Y * B).IsHermitian := by
    change (B * Y * B)ᴴ = B * Y * B
    rw [conjTranspose_mul, conjTranspose_mul, hB.eq, hY.eq, mul_assoc]
  exact (hY.add hc).smul (by simp [isSelfAdjoint_iff])

theorem positivePinching_offdiag_hermitian {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hY : Y.IsHermitian) :
    (positivePinchingOffdiag B Y).IsHermitian :=
  hY.sub (positivePinching_part_hermitian hB hY)

theorem positivePinching_shift_mul {B : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) (x : ℂ) :
    (B + x • (1 : Matrix ι ι ℂ)) * (B - x • 1) =
      (1 - x ^ 2) • (1 : Matrix ι ι ℂ) := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, hBB]
  module

theorem positivePinching_strip_denominator_pos {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < 1 - x ^ 2 := by
  have hp := mul_pos (sub_pos.mpr hx.2) (show 0 < 1 + x by linarith [hx.1])
  nlinarith

theorem positivePinching_shift_left_inverse {B : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ((1 - (x : ℂ) ^ 2)⁻¹ • (B + (x : ℂ) • (1 : Matrix ι ι ℂ))) *
      (B - (x : ℂ) • 1) = 1 := by
  have hn : 1 - (x : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (positivePinching_strip_denominator_pos hx))
  rw [smul_mul_assoc, positivePinching_shift_mul hB2, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

theorem positivePinching_shift_isUnit_det {B : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    IsUnit (B - (x : ℂ) • (1 : Matrix ι ι ℂ)).det :=
  Matrix.isUnit_det_of_left_inverse (positivePinching_shift_left_inverse hB2 hx)

theorem positivePinching_shift_inverse {B : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (B - (x : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ =
      (1 - (x : ℂ) ^ 2)⁻¹ • (B + (x : ℂ) • 1) :=
  Matrix.inv_eq_left_inv (positivePinching_shift_left_inverse hB2 hx)

theorem positivePinching_shift_hermitian {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (x : ℝ) :
    (B - (x : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian :=
  hB.sub (Matrix.isHermitian_one.smul (by simp [isSelfAdjoint_iff]))

theorem positivePinching_omega_eq_traceDensity {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (y : ℝ) :
    positivePinchingOmega B Y x y =
      traceDensity (B - (x : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ Y y := by
  unfold positivePinchingOmega traceDensity traceDensityPencil
  rw [Matrix.nonsing_inv_nonsing_inv _ (positivePinching_shift_isUnit_det hB2 hx)]

end
end CGLMPBounds.Hardy
