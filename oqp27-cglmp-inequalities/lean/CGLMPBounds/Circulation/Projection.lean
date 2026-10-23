module

public import CGLMPBounds.Circulation.Core

@[expose] public section


/-! # Fourth roots and their spectral-projection overlap coordinates -/

open Matrix
namespace CGLMPBounds.Circulation
noncomputable section
variable {r : ℕ}

@[simp] lemma tr_add (X Y : Mat r) : tr (X + Y) = tr X + tr Y := by
  simp [tr, Matrix.trace_add, add_div]
@[simp] lemma tr_sum {ι : Type*} (s : Finset ι) (X : ι → Mat r) :
    tr (∑ i ∈ s, X i) = ∑ i ∈ s, tr (X i) := by
  simp [tr, Matrix.trace_sum, Finset.sum_div]
@[simp] lemma tr_smul (a : ℂ) (X : Mat r) : tr (a • X) = a * tr X := by
  simp [tr, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]

lemma tr_hermitian_mul {P Q : Mat r} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    tr (P * Q) = (reTr (P * Q) : ℂ) := by
  have ht : star (Matrix.trace (P * Q)) = Matrix.trace (P * Q) := by
    calc
      star (Matrix.trace (P * Q)) = Matrix.trace ((P * Q)ᴴ) :=
        (Matrix.trace_conjTranspose _).symm
      _ = Matrix.trace (Q * P) := by rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq]
      _ = Matrix.trace (P * Q) := Matrix.trace_mul_comm Q P
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  simp only [tr, map_div₀, map_natCast]
  change star (Matrix.trace (P * Q)) / (r : ℂ) = Matrix.trace (P * Q) / (r : ℂ)
  rw [ht]

lemma corr_root_expansion (E F : Fin 4 → Mat r) (hE : IsPVM E) (hF : IsPVM F) :
    corr (root E) (root F) =
      ∑ a, ∑ b, (star (Complex.I ^ a.val) * Complex.I ^ b.val) *
        (reTr (E a * F b) : ℂ) := by
  have he : ∀ a, (E a)ᴴ = E a := fun a => (hE.isHermitian a).eq
  simp only [corr, root, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    he, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    tr_sum, tr_smul, tr_hermitian_mul (hE.isHermitian _) (hF.isHermitian _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma corr_root_im (E F : Fin 4 → Mat r) (hE : IsPVM E) (hF : IsPVM F) :
    (corr (root E) (root F)).im =
      (∑ l, reTr (E l * F (l + 1))) - ∑ l, reTr (E l * F (l + 3)) := by
  rw [corr_root_expansion E F hE hF]
  norm_num [Fin.sum_univ_four, Complex.mul_im, Complex.mul_re, Complex.star_def,
    Complex.I_sq, pow_succ]
  <;> ring

lemma corr_root_re (E F : Fin 4 → Mat r) (hE : IsPVM E) (hF : IsPVM F) :
    (corr (root E) (root F)).re =
      (∑ l, reTr (E l * F l)) - ∑ l, reTr (E l * F (l + 2)) := by
  rw [corr_root_expansion E F hE hF]
  norm_num [Fin.sum_univ_four, Complex.mul_im, Complex.mul_re, Complex.star_def,
    Complex.I_sq, pow_succ]
  <;> ring

lemma overlap_total [NeZero r] (E F : Fin 4 → Mat r) (hE : IsPVM E) (hF : IsPVM F) :
    (∑ l, reTr (E l * F l)) + (∑ l, reTr (E l * F (l + 1))) +
      (∑ l, reTr (E l * F (l + 2))) + (∑ l, reTr (E l * F (l + 3))) = 1 := by
  calc _ = ∑ a, ∑ b, reTr (E a * F b) := by
          norm_num [Fin.sum_univ_four]
          <;> ring
    _ = reTr ((∑ a, E a) * ∑ b, F b) := by
          simp only [Finset.sum_mul, Finset.mul_sum, reTr_sum]
          rw [Finset.sum_comm]
    _ = 1 := by
          rw [hE.sum_eq_one, hF.sum_eq_one, Matrix.one_mul, reTr_eq]
          simp [NeZero.ne r]

/-- Formula (C.2), expressed using the two forbidden successor overlaps. -/
lemma forbidden_root [NeZero r] (E F : Fin 4 → Mat r) (hE : IsPVM E) (hF : IsPVM F) :
    forbidden (root E) (root F) =
      (∑ l, hsSq (E l * F (l + 1))) + ∑ l, hsSq (E l * F (l + 2)) := by
  simp_rw [hsSq_proj_mul (hE.isHermitian _) (hE.mul_self _) (hF.isHermitian _) (hF.mul_self _)]
  rw [forbidden, corr_root_im E F hE hF, corr_root_re E F hE hF]
  have h := overlap_total E F hE hF
  linarith

/-- The forbidden overlap in (C.2) is nonnegative for arbitrary spectral PVMs. -/
lemma forbidden_root_nonneg [NeZero r] (E F : Fin 4 → Mat r)
    (hE : IsPVM E) (hF : IsPVM F) : 0 ≤ forbidden (root E) (root F) := by
  rw [forbidden_root E F hE hF]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => hsSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => hsSq_nonneg _)

lemma circulation_root (A B C : Fin 4 → Mat r) (hA : IsPVM A) (hB : IsPVM B)
    (hC : IsPVM C) :
    circulation (root A) (root B) (root C) =
      ((∑ l, reTr (A l * B (l + 1))) - ∑ l, reTr (A l * B (l + 3))) +
      ((∑ l, reTr (B l * C (l + 1))) - ∑ l, reTr (B l * C (l + 3))) -
      ((∑ l, reTr (A l * C (l + 1))) - ∑ l, reTr (A l * C (l + 3))) := by
  simp only [circulation, corr_root_im A B hA hB, corr_root_im B C hB hC,
    corr_root_im A C hA hC]

end
end CGLMPBounds.Circulation
