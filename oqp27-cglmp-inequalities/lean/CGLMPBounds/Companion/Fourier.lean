module

public import CGLMPBounds.Companion.Shift
public import CGLMPBounds.Fourier.Basis
public import CGLMPBounds.CGLMP.FourierValue
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section


/-!
# The source Fourier matrix and its shift eigenvalues

The character description avoids representative arithmetic for the cyclic shift.
The explicit entry identity identifies this matrix with the positive-exponent
Fourier matrix in Lemma C.1. Existing Fourier-basis orthogonality supplies both
unitarity identities, including the `ZMod d` / `Fin d` coordinate identification.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]

lemma stdAddChar_nat (k : ℕ) :
    ZMod.stdAddChar (k : ZMod d) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / d) := by
  simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := d) (k : ℤ)

lemma stdAddChar_mul_fin (a : ZMod d) (j : Fin d) :
    ZMod.stdAddChar (a * (j.val : ZMod d)) =
      Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (j.val : ℂ) / d) := by
  have hcast : a * (j.val : ZMod d) = ((a.val * j.val : ℕ) : ZMod d) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast, stdAddChar_nat, Nat.cast_mul]
  congr 1
  ring

/-- The positive-exponent matrix `F_aj=d^(-1/2) exp(2πiaj/d)` from supplement p. 6. -/
def outcomeFourier : Matrix (ZMod d) (Fin d) ℂ :=
  fun a j => (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (a * (j.val : ZMod d))

lemma outcomeFourier_apply (a : ZMod d) (j : Fin d) :
    outcomeFourier a j = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (j.val : ℂ) / d) := by
  rw [outcomeFourier, stdAddChar_mul_fin]

lemma outcomeFourier_eq_star_fourierVector (a : ZMod d) (j : Fin d) :
    outcomeFourier a j = star (fourierVector d 0 a j) := by
  rw [outcomeFourier_apply, fourierVector_eq, star_mul',
    ← starRingEnd_apply ((((Real.sqrt d)⁻¹ : ℝ) : ℂ)), Complex.conj_ofReal,
    star_exp_ofReal_mul_I]
  congr 2
  unfold fourierPhase
  push_cast
  ring

lemma outcomeFourier_mul_star :
    (outcomeFourier (d := d) * (outcomeFourier (d := d))ᴴ :
      Matrix (ZMod d) (ZMod d) ℂ) = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply, ← inner_fourierVector_same d 0 a b]
  simp only [outcomeFourier_eq_star_fourierVector, Matrix.conjTranspose_apply,
    star_star, dotProduct, Pi.star_apply]

lemma outcomeFourier_star_mul :
    ((outcomeFourier (d := d))ᴴ * outcomeFourier (d := d) :
      Matrix (Fin d) (Fin d) ℂ) = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (ZMod d) (Fin d) ℂ (by simp [ZMod.card])).mp
    (outcomeFourier_mul_star (d := d))

/-- The shift eigenvalue `exp(2πij/d)` in frequency `j`. -/
def outcomeRoot (j : Fin d) : ℂ := ZMod.stdAddChar (j.val : ZMod d)

lemma outcomeRoot_apply (j : Fin d) :
    outcomeRoot j = Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) :=
  stdAddChar_nat j.val

lemma outcomeRoot_injective : Function.Injective (outcomeRoot (d := d)) := by
  intro j k h
  have hz : (j.val : ZMod d) = (k.val : ZMod d) := ZMod.injective_stdAddChar h
  apply Fin.ext
  simpa only [ZMod.val_natCast_of_lt j.isLt, ZMod.val_natCast_of_lt k.isLt] using
    congrArg ZMod.val hz

/-- Scalar outcome shift with the same convention as `shiftBlocks`. -/
def outcomeShift : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight (1 : ZMod d)).permMatrix ℂ

set_option maxHeartbeats 800000 in
theorem outcomeShift_fourier :
    (outcomeShift (d := d) * outcomeFourier (d := d) : Matrix (ZMod d) (Fin d) ℂ) =
      (outcomeFourier (d := d) * Matrix.diagonal (outcomeRoot (d := d)) :
        Matrix (ZMod d) (Fin d) ℂ) := by
  have hperm :
      (outcomeShift (d := d) * outcomeFourier (d := d) : Matrix (ZMod d) (Fin d) ℂ) =
        (outcomeFourier (d := d)).submatrix (Equiv.addRight (1 : ZMod d)) id :=
    PEquiv.toMatrix_toPEquiv_mul (Equiv.addRight (1 : ZMod d))
      (outcomeFourier (d := d))
  refine hperm.trans (Matrix.ext fun a j => ?_)
  have hindex : (a + 1) * (j.val : ZMod d) =
      a * (j.val : ZMod d) + (j.val : ZMod d) := by
    rw [add_mul, one_mul]
  have hchar : ZMod.stdAddChar ((a + 1) * (j.val : ZMod d)) =
      ZMod.stdAddChar (a * (j.val : ZMod d)) * ZMod.stdAddChar (j.val : ZMod d) :=
    (congrArg (fun x : ZMod d => ZMod.stdAddChar x) hindex).trans
      (AddChar.map_add_eq_mul ZMod.stdAddChar _ _)
  have hentry : outcomeFourier (a + 1) j = outcomeFourier a j * outcomeRoot j :=
    (congrArg (fun z : ℂ => (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * z) hchar).trans
      (mul_assoc _ _ _).symm
  exact hentry.trans
    (Matrix.mul_diagonal (outcomeRoot (d := d)) (outcomeFourier (d := d)) a j).symm

/-- Exact Fourier diagonalization of `J|a⟩=|a−1⟩`. -/
theorem outcomeFourier_diagonalizes_shift :
    ((((outcomeFourier (d := d))ᴴ * outcomeShift (d := d) :
        Matrix (Fin d) (ZMod d) ℂ) * outcomeFourier (d := d)) :
      Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal (outcomeRoot (d := d)) := by
  rw [Matrix.mul_assoc, outcomeShift_fourier, ← Matrix.mul_assoc,
    outcomeFourier_star_mul, Matrix.one_mul]

/-- The source phase `λ_j=exp(πij/(2d))`, expressed through the existing `etaD`. -/
def sourcePhase (j : Fin d) : ℂ := etaD d ^ j.val

lemma sourcePhase_apply (j : Fin d) :
    sourcePhase j = Complex.exp (((Real.pi * j.val / (2 * d) : ℝ) : ℂ) * Complex.I) := by
  rw [sourcePhase, etaD, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma sourcePhase_ne_zero (j : Fin d) : sourcePhase j ≠ 0 :=
  pow_ne_zero _ (etaD_ne_zero d)

lemma sourcePhase_star_mul (j : Fin d) : star (sourcePhase j) * sourcePhase j = 1 := by
  rw [sourcePhase_apply]
  change (starRingEnd ℂ) (Complex.exp _) * Complex.exp _ = 1
  rw [conj_exp_ofReal_mul_I, inv_mul_cancel₀ (Complex.exp_ne_zero _)]

lemma sourcePhase_fourth (j : Fin d) : sourcePhase j ^ 4 = outcomeRoot j := by
  calc
    sourcePhase j ^ 4 = (etaD d ^ 4) ^ j.val := by
      rw [sourcePhase, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = Complex.exp (2 * Real.pi * Complex.I / d) ^ j.val := by rw [etaD_pow_four]
    _ = Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    _ = outcomeRoot j := (outcomeRoot_apply j).symm

end
end CGLMPBounds.Companion
