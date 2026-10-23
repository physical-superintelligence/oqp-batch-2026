module

public import ThreeCopyQutritWerner.RankTwoSpectralEquality

@[expose] public section


/-!
# Actual range support at saturated rank-two spectral overlap

An actual orthonormal rank factorization supplies the compression. Equality
in the original Hilbert--Schmidt overlap forces that compression to saturate,
so every strict submaximal spectral row of the original Y vanishes.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Equality at a uniform largest squared spectral weight annihilates every
strictly lower spectral row of the original rank-at-most-two matrix. No
range inclusion or chosen rank factorization is an input. -/
theorem rankTwo_spectral_overlap_eq_submax_rows_zero
    {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
    (V : Matrix m r ℂ) (hV : Vᴴ * V = 1) (w : r → ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hw : ∀ j, w j ^ 2 ≤ S)
    (Y : Matrix m m ℂ) (hY : Y.rank ≤ 2) (hpos : 0 < frobSq Y)
    (heq : Complex.normSq
      ((V * Matrix.diagonal (fun j => (w j : ℂ)) * Vᴴ)ᴴ * Y).trace =
        2 * S * frobSq Y)
    (j : r) (hj : w j ^ 2 < S) (i : m) : (Vᴴ * Y) j i = 0 := by
  let X := V * Matrix.diagonal (fun j => (w j : ℂ)) * Vᴴ
  obtain ⟨k, U, B, hk, hU, hUB⟩ := exists_orthonormal_mul Y
  have hk2 : Fintype.card (Fin k) ≤ 2 := by simpa [hk] using hY
  have hcomp : frobSq (Uᴴ * V * Matrix.diagonal (fun j => (w j : ℂ))) ≤ 2 * S := by
    apply rankTwo_weighted_frame_le U V hU hV hk2 w (2 * S) (by positivity)
    · intro a
      linarith [hw a]
    · intro a b _
      linarith [hw a, hw b]
  have hnorm : frobSq (Uᴴ * X) =
      frobSq (Uᴴ * V * Matrix.diagonal (fun j => (w j : ℂ))) := by
    have hx : Uᴴ * X = (Uᴴ * V * Matrix.diagonal (fun j => (w j : ℂ))) * Vᴴ := by
      simp only [X, Matrix.mul_assoc]
    rw [hx, ← rankTwo_frobSq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, nuclearTrace_frobSq_isometry_mul V _ hV,
      rankTwo_frobSq_conjTranspose]
  have hcs := nuclearTrace_pair_normSq_le (Uᴴ * X) B
  have ht : (Xᴴ * Y).trace = ((Uᴴ * X)ᴴ * B).trace := by
    rw [hUB]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hB : frobSq B = frobSq Y := by rw [hUB, frobSq_isometry_mul U hU]
  rw [← ht, hB, hnorm] at hcs
  change Complex.normSq (Xᴴ * Y).trace = 2 * S * frobSq Y at heq
  rw [heq] at hcs
  have he : frobSq (Uᴴ * V * Matrix.diagonal (fun j => (w j : ℂ))) = 2 * S :=
    le_antisymm hcomp (le_of_mul_le_mul_right hcs hpos)
  have hz : ∀ a : Fin k, (Uᴴ * V) a j = 0 :=
    rankTwo_weighted_frame_eq_submax_zero U V hU hV hk2 w S hS hw he j hj
  rw [hUB, ← Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  have hzero : (Vᴴ * U) j a = 0 := by
    rw [show Vᴴ * U = (Uᴴ * V)ᴴ by simp]
    simp only [Matrix.conjTranspose_apply, hz a, star_zero]
  rw [hzero, zero_mul]

end ThreeCopyQutritWerner
