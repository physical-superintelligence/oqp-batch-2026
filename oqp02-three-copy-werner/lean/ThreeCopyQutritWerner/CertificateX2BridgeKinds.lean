module

public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# Positivity of an h type triple from its block residuals

On a canonical h type triple the residual Q-form is `πᵀ q π` (`π` the carrier action on the
ambient, `q` the transferred Q-form, symmetric). Each stabilizer kind `k` contributes
`(π P_k)ᵀ q (π P_k)`, and the range of `π P_k` is spanned by the image `J_k` together with, for
the standard kind, its partner `W_k = (cyc - cyc²) J_k`. The certificate's partner normalization gives
`J_kᵀ q W_k = 0` and `W_kᵀ q W_k = 3 J_kᵀ q J_k` for an S3-invariant `q`. Then
`(J A + W B)ᵀ q (J A + W B) = Aᵀ R A + 3 Bᵀ R B` with `R = Jᵀ q J` the block residual, which is
positive semidefinite when `R` is.

This module proves that algebraic step (`x2_posSemidef_of_span`) and its sum over kinds
(`x2_posSemidef_of_kinds`). The span and orthogonality facts themselves are finite data
obligations of the bridge.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem x2Complex_mul {l m n : Type*} [Fintype m] (A : Matrix l m ℚ) (B : Matrix m n ℚ) :
    (A * B).map (fun q : ℚ => (q : ℂ)) = A.map (fun q : ℚ => (q : ℂ)) * B.map (fun q : ℚ => (q : ℂ)) :=
  Matrix.map_mul (f := Rat.castHom ℂ)

theorem x2Complex_transpose_eq_conjTranspose {m n : Type*} (A : Matrix m n ℚ) :
    (Aᵀ).map (fun q : ℚ => (q : ℂ)) = (A.map (fun q : ℚ => (q : ℂ)))ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem x2Complex_add {n : Type*} (A B : Matrix n n ℚ) :
    x2Complex (A + B) = x2Complex A + x2Complex B := by
  ext i j
  simp [x2Complex]

theorem x2Complex_smul {n : Type*} (c : ℚ) (A : Matrix n n ℚ) :
    x2Complex (c • A) = (c : ℂ) • x2Complex A := by
  ext i j
  simp [x2Complex]

theorem x2Complex_sum {n ι : Type*} [Fintype ι] (X : ι → Matrix n n ℚ) :
    x2Complex (∑ k, X k) = ∑ k, x2Complex (X k) := by
  ext i j
  simp [x2Complex, Matrix.sum_apply]

theorem x2_ratCast_nonneg {c : ℚ} (hc : 0 ≤ c) : (0 : ℂ) ≤ (c : ℂ) := by
  rw [← Complex.ofReal_ratCast]
  exact Complex.zero_le_real.mpr (Rat.cast_nonneg.mpr hc)

/-- `Bᵀ R B` is positive semidefinite (as a complex matrix) when `R` is. -/
theorem x2_posSemidef_congr {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (R : Matrix m m ℚ) (B : Matrix m n ℚ) (hR : (x2Complex R).PosSemidef) :
    (x2Complex (Bᵀ * R * B)).PosSemidef := by
  unfold x2Complex at hR ⊢
  rw [x2Complex_mul, x2Complex_mul, x2Complex_transpose_eq_conjTranspose]
  exact hR.conjTranspose_mul_mul_same _

/-- Positivity through a spanning pair `[J | W]` with the standard-copy relations. -/
theorem x2_posSemidef_of_span {n r k : Type*} [Fintype n] [Fintype r] [Fintype k]
    [DecidableEq k] (q : Matrix n n ℚ) (hq : qᵀ = q) (J W : Matrix n r ℚ)
    (A B : Matrix r k ℚ) (c : ℚ) (hc : 0 ≤ c)
    (hJW : Jᵀ * q * W = 0) (hWW : Wᵀ * q * W = c • (Jᵀ * q * J))
    (hR : (x2Complex (Jᵀ * q * J)).PosSemidef) :
    (x2Complex ((J * A + W * B)ᵀ * q * (J * A + W * B))).PosSemidef := by
  have hWJ : Wᵀ * q * J = 0 := by
    have h := congrArg Matrix.transpose hJW
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hq,
      Matrix.transpose_zero] at h
    rw [← h, Matrix.mul_assoc]
  have hexp : (J * A + W * B)ᵀ * q * (J * A + W * B) =
      Aᵀ * (Jᵀ * q * J) * A + c • (Bᵀ * (Jᵀ * q * J) * B) := by
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]
    have e1 : (Aᵀ * Jᵀ + Bᵀ * Wᵀ) * q * (J * A + W * B) =
        Aᵀ * (Jᵀ * q * J) * A + Aᵀ * (Jᵀ * q * W) * B + Bᵀ * (Wᵀ * q * J) * A +
          Bᵀ * (Wᵀ * q * W) * B := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [e1, hJW, hWJ, hWW]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_smul, Matrix.smul_mul]
  rw [hexp, x2Complex_add, x2Complex_smul]
  exact (x2_posSemidef_congr (Jᵀ * q * J) A hR).add
    ((x2_posSemidef_congr (Jᵀ * q * J) B hR).smul (x2_ratCast_nonneg hc))

/-- Sum over kinds: if the residual is the sum of the kind pieces and each piece is spanned by
its image and partner, the residual is positive semidefinite. -/
theorem x2_posSemidef_of_kinds {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}
    (q : Matrix n n ℚ) (hq : qᵀ = q) (M : Matrix n n ℚ)
    (r : Fin K → ℕ) (J W : (k : Fin K) → Matrix n (Fin (r k)) ℚ)
    (A B : (k : Fin K) → Matrix (Fin (r k)) n ℚ) (c : Fin K → ℚ) (hc : ∀ k, 0 ≤ c k)
    (hsum : M = ∑ k, (J k * A k + W k * B k)ᵀ * q * (J k * A k + W k * B k))
    (hJW : ∀ k, (J k)ᵀ * q * W k = 0) (hWW : ∀ k, (W k)ᵀ * q * W k = c k • ((J k)ᵀ * q * J k))
    (hR : ∀ k, (x2Complex ((J k)ᵀ * q * J k)).PosSemidef) :
    (x2Complex M).PosSemidef := by
  rw [hsum, x2Complex_sum]
  apply Matrix.posSemidef_sum
  intro k _
  exact x2_posSemidef_of_span q hq (J k) (W k) (A k) (B k) (c k) (hc k) (hJW k) (hWW k) (hR k)

end ThreeCopyQutritWerner

end
