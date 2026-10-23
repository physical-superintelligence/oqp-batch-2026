module

public import ThreeCopyQutritWerner.CertificateImageFrame
public import ThreeCopyQutritWerner.CertificateCentralIdempotence

@[expose] public section


/-!
# Passing actual physical projections to original source coordinates

The source frame is merely left-invertible, not orthonormal. Idempotence,
commutation and selfadjointness in the original Gram metric follow from exact
physical action. These lemmas supply the projector premises needed by the
selected-column image reconstruction; they assume no archive rank claim.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- An ordinary left inverse permits cancellation of a rectangular source frame. -/
theorem certificateSourceFrame_cancel_left {n m k : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (U : Matrix n m ℂ) (L : Matrix m n ℂ) (hLU : L * U = 1)
    (A B : Matrix m k ℂ) (h : U * A = U * B) : A = B := by
  have he := congrArg (fun M : Matrix n k ℂ => L * M) h
  simpa only [← Matrix.mul_assoc, hLU, Matrix.one_mul] using he

/-- The actual coefficient action of a physical projector is idempotent. -/
theorem certificateSourceFrame_projector {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (U : Matrix n m ℂ) (L : Matrix m n ℂ) (hLU : L * U = 1)
    (P : Matrix n n ℂ) (A : Matrix m m ℂ)
    (hP : P * P = P) (hA : P * U = U * A) : A * A = A := by
  apply certificateSourceFrame_cancel_left U L hLU
  calc
    U * (A * A) = (P * P) * U := by
      rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, ← hA, ← Matrix.mul_assoc]
    _ = P * U := by rw [hP]
    _ = U * A := hA

/-- Physical commutation passes to the original coefficient operators. -/
theorem certificateSourceFrame_commute {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (U : Matrix n m ℂ) (L : Matrix m n ℂ) (hLU : L * U = 1)
    (P Q : Matrix n n ℂ) (A B : Matrix m m ℂ)
    (hPQ : P * Q = Q * P) (hA : P * U = U * A) (hB : Q * U = U * B) :
    A * B = B * A := by
  apply certificateSourceFrame_cancel_left U L hLU
  calc
    U * (A * B) = (P * Q) * U := by
      rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, ← hB, ← Matrix.mul_assoc]
    _ = (Q * P) * U := by rw [hPQ]
    _ = U * (B * A) := by
      rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]

/-- Physical Hermiticity is exactly selfadjointness in the original source Gram. -/
theorem certificateSourceFrame_gram_selfadjoint {n m : Type*}
    [Fintype n] [Fintype m]
    (U : Matrix n m ℂ) (P : Matrix n n ℂ) (A : Matrix m m ℂ)
    (hP : P.IsHermitian) (hA : P * U = U * A) :
    (Uᴴ * U) * A = Aᴴ * (Uᴴ * U) := by
  calc
    (Uᴴ * U) * A = Uᴴ * (P * U) := by rw [Matrix.mul_assoc, ← hA]
    _ = (P * U)ᴴ * U := by
      rw [Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
    _ = (U * A)ᴴ * U := by rw [hA]
    _ = Aᴴ * (Uᴴ * U) := by rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A commuting carrier and site projector give the actual image projector. -/
theorem certificateImageProjector_mul_idempotent {n : Type*} [Fintype n]
    (P Q : Matrix n n ℂ) (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = Q * P) : (P * Q) * (P * Q) = P * Q :=
  (IsIdempotentElem.mul_of_commute hPQ hP hQ).eq

/-- The product retains selfadjointness in the unchanged original metric. -/
theorem certificateImageProjector_mul_gram_selfadjoint {n : Type*} [Fintype n]
    (G P Q : Matrix n n ℂ) (hP : G * P = Pᴴ * G) (hQ : G * Q = Qᴴ * G)
    (hPQ : P * Q = Q * P) : G * (P * Q) = (P * Q)ᴴ * G := by
  calc
    G * (P * Q) = (G * P) * Q := (Matrix.mul_assoc _ _ _).symm
    _ = Pᴴ * (Qᴴ * G) := by rw [hP, Matrix.mul_assoc, hQ]
    _ = (Q * P)ᴴ * G := by rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * Q)ᴴ * G := by rw [hPQ]

/-- Projector idempotence reduces the full image Gram to one projected kernel.
This avoids summing over the entire image ambient space for every Gram entry. -/
theorem certificateImageProjector_gram {n m : Type*}
    [Fintype n] [Fintype m]
    (G P : Matrix n n ℂ) (E : Matrix n m ℂ)
    (hP : P * P = P) (hGP : G * P = Pᴴ * G) :
    (P * E)ᴴ * G * (P * E) = Eᴴ * G * P * E := by
  rw [Matrix.conjTranspose_mul]
  calc
    (Eᴴ * Pᴴ) * G * (P * E) = Eᴴ * (Pᴴ * G) * P * E := by
      simp only [Matrix.mul_assoc]
    _ = Eᴴ * (G * P) * P * E := by rw [← hGP]
    _ = Eᴴ * G * (P * P) * E := by simp only [Matrix.mul_assoc]
    _ = Eᴴ * G * P * E := by rw [hP]

/-- An exact scaled inverse of selected rows yields an ordinary full left inverse. -/
theorem certificateImageFrame_leftInverse_of_pivot_inverse {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J : Matrix n m ℂ) (row : m → n) (W : Matrix m m ℂ)
    (d : ℂ) (hd : d ≠ 0) (hW : W * J.submatrix row id = d • (1 : Matrix m m ℂ)) :
    ((d⁻¹ • W) * (1 : Matrix n n ℂ).submatrix row id) * J = 1 := by
  have hs : (1 : Matrix n n ℂ).submatrix row id * J = J.submatrix row id := by
    change ((1 : Matrix n n ℂ) * J).submatrix row id = J.submatrix row id
    rw [Matrix.one_mul]
  rw [Matrix.mul_assoc, Matrix.smul_mul, hs, hW, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

end ThreeCopyQutritWerner
