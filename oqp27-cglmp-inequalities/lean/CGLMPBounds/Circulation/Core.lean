module

public import CGLMPBounds.Defs.Circulation
public import CGLMPBounds.LocalContent.Tracial

@[expose] public section


/-! # Elementary real trace and Hilbert–Schmidt identities for Appendix H -/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds.Circulation
noncomputable section
variable {r : ℕ}

lemma reTr_eq (X : Mat r) : reTr X = (Matrix.trace X).re / r := by
  simp only [reTr, tr, ← Complex.ofReal_natCast, Complex.div_ofReal_re]

@[simp] lemma reTr_zero : reTr (0 : Mat r) = 0 := by simp [reTr_eq]
@[simp] lemma reTr_add (X Y : Mat r) : reTr (X + Y) = reTr X + reTr Y := by
  simp [reTr_eq, Matrix.trace_add, add_div]
@[simp] lemma reTr_sub (X Y : Mat r) : reTr (X - Y) = reTr X - reTr Y := by
  simp [reTr_eq, Matrix.trace_sub, sub_div]
@[simp] lemma reTr_neg (X : Mat r) : reTr (-X) = -reTr X := by
  simp [reTr_eq, Matrix.trace_neg, neg_div]
@[simp] lemma reTr_smul (a : ℝ) (X : Mat r) : reTr ((a : ℂ) • X) = a * reTr X := by
  simp [reTr_eq, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, mul_div_assoc]
@[simp] lemma reTr_sum {ι : Type*} (s : Finset ι) (X : ι → Mat r) :
    reTr (∑ i ∈ s, X i) = ∑ i ∈ s, reTr (X i) := by
  simp [reTr_eq, Matrix.trace_sum, Complex.re_sum, Finset.sum_div]

lemma reTr_mul_comm (X Y : Mat r) : reTr (X * Y) = reTr (Y * X) := by
  simp only [reTr_eq, Matrix.trace_mul_comm X Y]
lemma reTr_cycle (X Y Z : Mat r) : reTr (X * Y * Z) = reTr (Y * Z * X) := by
  simp only [reTr_eq]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm X (Y * Z)]
@[simp] lemma reTr_star (X : Mat r) : reTr Xᴴ = reTr X := by
  simp [reTr_eq, Matrix.trace_conjTranspose]

lemma reTr_inner_comm (X Y : Mat r) : reTr (Xᴴ * Y) = reTr (Yᴴ * X) := by
  calc reTr (Xᴴ * Y) = reTr (Xᴴ * Y)ᴴ := (reTr_star _).symm
    _ = reTr (Yᴴ * X) := by simp

lemma hsSq_nonneg (X : Mat r) : 0 ≤ hsSq X := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  rw [hsSq, reTr_eq]
  exact div_nonneg (Complex.nonneg_iff.mp h).1 (Nat.cast_nonneg r)

@[simp] lemma hsSq_star (X : Mat r) : hsSq Xᴴ = hsSq X := by
  simp only [hsSq, Matrix.conjTranspose_conjTranspose, reTr_mul_comm X Xᴴ]

lemma hsSq_sub_smul (X Y : Mat r) (a : ℝ) :
    hsSq (Y - (a : ℂ) • X) = hsSq Y + a ^ 2 * hsSq X - 2 * a * reTr (Xᴴ * Y) := by
  simp only [hsSq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
    reTr_sub, reTr_smul]
  rw [reTr_inner_comm Y X]
  ring

lemma hsSq_add_smul (X Y : Mat r) (a : ℝ) :
    hsSq (Y + (a : ℂ) • X) = hsSq Y + a ^ 2 * hsSq X + 2 * a * reTr (Xᴴ * Y) := by
  simpa using hsSq_sub_smul X Y (-a)

lemma hsSq_proj_mul {P Q : Mat r} (hP : P.IsHermitian) (hP2 : P * P = P)
    (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) : hsSq (P * Q) = reTr (P * Q) := by
  simp only [hsSq, reTr_eq, ← trace_proj_mul_eq hP hP2 hQ hQ2]

lemma reTr_shared_left {P Q R : Mat r} (hP : P.IsHermitian) (hP2 : P * P = P)
    (hQ : Q.IsHermitian) : reTr ((P * Q)ᴴ * (P * R)) = reTr (Q * P * R) := by
  rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq]
  congr 1
  calc Q * P * (P * R) = Q * (P * P) * R := by simp only [Matrix.mul_assoc]
    _ = Q * P * R := by rw [hP2]

lemma reTr_reverse {P Q R : Mat r} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hR : R.IsHermitian) : reTr (P * Q * R) = reTr (R * Q * P) := by
  calc reTr (P * Q * R) = reTr (P * Q * R)ᴴ := (reTr_star _).symm
    _ = reTr (R * Q * P) := by simp [hP.eq, hQ.eq, hR.eq, Matrix.mul_assoc]

lemma reTr_swap_first {P Q R : Mat r} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hR : R.IsHermitian) : reTr (P * Q * R) = reTr (Q * P * R) := by
  rw [reTr_reverse hP hQ hR, reTr_cycle]

end
end CGLMPBounds.Circulation
