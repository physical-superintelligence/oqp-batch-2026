module

public import ThreeCopyQutritWerner.SharpQutritDiagonalBounds
public import ThreeCopyQutritWerner.Identities

@[expose] public section


/-!
# Rank-two overlap with the exact qutrit middle-eigenvalue deficit

The full nine-vector physical eigenbasis and its proved pair-weight bounds
give the improved overlap estimate. Projection saturation then forces an
original diagonal exterior coefficient to vanish.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Every orthogonal compression with at most two columns obeys the bound
from the two actual central extremes. -/
theorem sharpQutritDiagonal_compression_le
    {k : Type*} [Fintype k] [DecidableEq k]
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (U : Matrix (Fin 3 × Fin 3) k ℂ) (hU : Uᴴ * U = 1)
    (hk : Fintype.card k ≤ 2) :
    frobSq (Uᴴ * sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))) ≤
      sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 := by
  have he : Uᴴ * sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) =
      (Uᴴ * sharpQutritDiagonalFrame d *
        Matrix.diagonal (fun j => (sharpQutritDiagonalWeight d j : ℂ))) *
          (sharpQutritDiagonalFrame d)ᴴ := by
    rw [sharpQutritDiagonalFrame_factorization]
    simp only [Matrix.mul_assoc]
  rw [he, ← rankTwo_frobSq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    nuclearTrace_frobSq_isometry_mul _ _ (sharpQutritDiagonalFrame_gram d),
    rankTwo_frobSq_conjTranspose]
  exact rankTwo_weighted_frame_le U (sharpQutritDiagonalFrame d) hU
    (sharpQutritDiagonalFrame_gram d) hk (sharpQutritDiagonalWeight d) _
    (by positivity) (sharpQutritDiagonalWeight_sq_le d hd)
    (sharpQutritDiagonalWeight_pair_le d hd)

/-- The improved overlap constant retains the exact square of the actual
middle eigenvalue, for every original rank-at-most-two matrix Y. -/
theorem sharpQutritDiagonal_rank_two_overlap_le
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2) :
    Complex.normSq
      ((sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))ᴴ * Y).trace ≤
        (2 * (∑ i, d i ^ 2) - sharpQutritCentralOrdered d 1 ^ 2) * frobSq Y := by
  obtain ⟨r, U, B, hr, hU, hUB⟩ := exists_orthonormal_mul Y
  have hk : Fintype.card (Fin r) ≤ 2 := by simpa [hr] using hY
  have hcomp := sharpQutritDiagonal_compression_le d hd U hU hk
  rw [sharpQutritCentralOrdered_extreme_deficit] at hcomp
  have hcs := nuclearTrace_pair_normSq_le
    (Uᴴ * sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))) B
  have ht : ((sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))ᴴ * Y).trace =
      ((Uᴴ * sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))ᴴ * B).trace := by
    rw [hUB]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← ht] at hcs
  have hB : frobSq B = frobSq Y := by rw [hUB, frobSq_isometry_mul U hU]
  exact hcs.trans (by
    rw [← hB]
    exact mul_le_mul_of_nonneg_right hcomp (frobSq_nonneg B))

/-- Nonzero sharp projection saturation excludes a nonzero coefficient in
every exterior direction. The projection and norm equations refer to the
actual original physical Y; no spectral saturation premise is supplied. -/
theorem sharpQutritDiagonal_saturation_forces_coefficient_zero
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y) :
    d 0 = 0 ∨ d 1 = 0 ∨ d 2 = 0 := by
  let Z := sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))
  have hfix : sharpDoubleAnti Z = Z := sharpQutritAntiEncode_fixed _
  have ht : (Zᴴ * Y).trace = (frobSq Z : ℂ) := by
    rw [← hsInner_eq_trace]
    calc
      hsInner Z Y = hsInner (sharpDoubleAnti Z) Y := by rw [hfix]
      _ = hsInner Z (sharpDoubleAnti Y) := sharpDoubleAnti_selfadjoint Z Y
      _ = hsInner Z Z := by rw [hQ]
      _ = (frobSq Z : ℂ) := (ofReal_frobSq Z).symm
  have hZ : frobSq Z = 4 * ∑ i, d i ^ 2 := by
    change frobSq (sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))) = _
    rw [sharpQutritAntiEncode_frobSq]
    simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]
  have hov := sharpQutritDiagonal_rank_two_overlap_le d hd Y hY
  change Complex.normSq (Zᴴ * Y).trace ≤ _ at hov
  rw [ht, Complex.normSq_ofReal] at hov
  rw [hQ] at hs
  change frobSq Z = frobSq Y / 2 at hs
  have hbound : frobSq Z / 2 ≤
      2 * (∑ i, d i ^ 2) - sharpQutritCentralOrdered d 1 ^ 2 := by
    apply le_of_mul_le_mul_right (a := frobSq Y) ?_ hpos
    have hcancel : frobSq Z / 2 * frobSq Y = frobSq Z * frobSq Z := by
      rw [show frobSq Y = 2 * frobSq Z by linarith]
      ring
    rw [hcancel]
    exact hov
  have hmid : sharpQutritCentralOrdered d 1 = 0 := by
    have hsq := sq_nonneg (sharpQutritCentralOrdered d 1)
    have hz : sharpQutritCentralOrdered d 1 ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hz
  apply sharpQutritCentralOrdered_extreme_eq_forces_coefficient_zero d
  exact (sharpQutritCentralOrdered_extreme_eq_iff d).mpr hmid

end ThreeCopyQutritWerner
