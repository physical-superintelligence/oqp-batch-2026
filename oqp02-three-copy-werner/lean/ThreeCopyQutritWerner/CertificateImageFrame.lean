module

public import ThreeCopyQutritWerner.CertificateKernelFrame
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
Exact completeness of selected image columns from an ordinary left inverse
and the trace of an actual projector. This avoids expanding the full square
projector or promoting a modular rank count to a rational completeness claim.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- A characteristic-zero matrix idempotent with zero trace vanishes. -/
theorem certificateIdempotentMatrix_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) (hE : E * E = E) (htrace : E.trace = 0) : E = 0 := by
  let φ := (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ))
  have he : IsIdempotentElem (φ E) := by
    change φ E * φ E = φ E
    have h := congrArg φ hE
    simpa only [map_mul] using h
  have ht : LinearMap.trace ℂ (n → ℂ) (φ E) = 0 := by
    change LinearMap.trace ℂ (n → ℂ) E.toLin' = 0
    rw [Matrix.trace_toLin'_eq, htrace]
  apply φ.injective
  rw [map_zero]
  exact LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero he ht

/-- An independent family inside a projector image is complete when its size
equals the exact trace. The conclusion is a literal matrix reconstruction. -/
theorem certificateImageFrame_complete {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (P : Matrix n n ℂ) (J : Matrix n m ℂ) (L : Matrix m n ℂ)
    (hP : P * P = P) (hJ : P * J = J) (hL : L * J = 1)
    (htrace : P.trace = (Fintype.card m : ℂ)) :
    P = J * L * P := by
  let Q := J * L * P
  have hPQ : P * Q = Q := by
    dsimp [Q]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have hQP : Q * P = Q := by
    dsimp [Q]
    rw [Matrix.mul_assoc, hP]
  have hQQ : Q * Q = Q := by
    dsimp [Q]
    calc
      (J * L * P) * (J * L * P) = J * L * (P * J) * L * P := by
        simp only [Matrix.mul_assoc]
      _ = J * (L * J) * L * P := by rw [hJ, Matrix.mul_assoc J L J]
      _ = J * L * P := by rw [hL, Matrix.mul_one]
  have hQtrace : Q.trace = (Fintype.card m : ℂ) := by
    dsimp [Q]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hJ, hL,
      Matrix.trace_one]
  have hd : (P - Q) * (P - Q) = P - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP, hPQ, hQP, hQQ]
    abel
  have hz := certificateIdempotentMatrix_eq_zero (P - Q) hd
    (by rw [Matrix.trace_sub, htrace, hQtrace, sub_self])
  exact sub_eq_zero.mp hz

/-- Selected nonzero multiples of projector columns are automatically in its image. -/
theorem certificateImageFrame_of_columns {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (P : Matrix n n ℂ) (column : m → n) (scale : m → ℂ)
    (hP : P * P = P) :
    P * (P.submatrix id column * Matrix.diagonal scale) =
      P.submatrix id column * Matrix.diagonal scale := by
  have hc : P * P.submatrix id column = P.submatrix id column := by
    change (P * P).submatrix id column = P.submatrix id column
    rw [hP]
  rw [← Matrix.mul_assoc, hc]

end ThreeCopyQutritWerner
