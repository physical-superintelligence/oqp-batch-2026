module

public import CGLMPBounds.Circulation.SOS

@[expose] public section


/-! # Explicit spectral projections of an arbitrary fourth-root unitary -/

open Matrix
namespace CGLMPBounds.Circulation
noncomputable section
variable {r : ℕ}

lemma fourth_root_star {V : Mat r} (hunit : Vᴴ * V = 1) (hfour : V ^ 4 = 1) :
    Vᴴ = V ^ 3 := by
  calc Vᴴ = Vᴴ * V ^ 4 := by rw [hfour, Matrix.mul_one]
    _ = (Vᴴ * V) * V ^ 3 := by rw [show V ^ 4 = V * V ^ 3 by exact pow_succ' V 3, Matrix.mul_assoc]
    _ = V ^ 3 := by rw [hunit, Matrix.one_mul]

lemma average4_hermitian {V : Mat r} (hunit : Vᴴ * V = 1) (hfour : V ^ 4 = 1) :
    (average4 V).IsHermitian := by
  have hs := fourth_root_star hunit hfour
  have h6 : V ^ 6 = V ^ 2 := by
    calc V ^ 6 = V ^ 4 * V ^ 2 := by rw [← pow_add]
      _ = V ^ 2 := by rw [hfour, Matrix.one_mul]
  have h9 : V ^ 9 = V := by
    calc V ^ 9 = (V ^ 4) ^ 2 * V := by simp only [← pow_mul, ← pow_succ]
      _ = V := by rw [hfour]; simp
  change (average4 V)ᴴ = average4 V
  simp only [average4, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_pow, hs, ← pow_mul]
  norm_num [h6, h9]
  <;> module

lemma average4_idempotent {V : Mat r} (hfour : V ^ 4 = 1) :
    average4 V * average4 V = average4 V := by
  have hnum : (1 + V + V ^ 2 + V ^ 3) * (1 + V + V ^ 2 + V ^ 3) =
      (4 : ℂ) • (1 + V + V ^ 2 + V ^ 3) := by
    calc _ = (4 : Mat r) * (1 + V + V ^ 2 + V ^ 3) +
        (V ^ 4 - 1) * (V ^ 2 + 2 * V + 3) := by noncomm_ring
      _ = (4 : ℂ) • (1 + V + V ^ 2 + V ^ 3) := by
        rw [hfour, sub_self, Matrix.zero_mul, add_zero]
        simp only [Algebra.smul_def, map_ofNat]
  simp only [average4, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hnum]
  norm_num

lemma spectral_sum (V : Mat r) : ∑ l, spectral V l = 1 := by
  norm_num [Fin.sum_univ_four, spectral, average4, smul_pow, pow_succ,
    Complex.I_sq, smul_add, smul_smul]
  <;> module

lemma root_spectral (V : Mat r) : root (spectral V) = V := by
  norm_num [root, Fin.sum_univ_four, spectral, average4, smul_pow, pow_succ,
    Complex.I_sq, smul_add, smul_smul]
  <;> match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

/-- Every fourth-root unitary has the four-outcome spectral PVM used in Appendix H. -/
theorem spectral_isPVM {V : Mat r} (hunit : Vᴴ * V = 1) (hfour : V ^ 4 = 1) :
    IsPVM (spectral V) := by
  have hu : ∀ l : Fin 4, (((-Complex.I) ^ l.val) • V)ᴴ * (((-Complex.I) ^ l.val) • V) = 1 := by
    intro l
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hunit]
    fin_cases l <;> norm_num [pow_succ, Complex.I_sq]
  have hf : ∀ l : Fin 4, (((-Complex.I) ^ l.val) • V) ^ 4 = 1 := by
    intro l
    simp only [smul_pow, hfour]
    fin_cases l <;> norm_num [pow_succ, Complex.I_sq]
  exact ⟨fun l => average4_hermitian (hu l) (hf l),
    fun l => average4_idempotent (hf l), spectral_sum V⟩

/-- Nonnegativity in (C.2) for arbitrary fourth-root unitaries. -/
theorem fourth_root_forbidden_nonneg [NeZero r] (U V : Mat r)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hU4 : U ^ 4 = 1) (hV4 : V ^ 4 = 1) : 0 ≤ forbidden U V := by
  simpa only [root_spectral] using forbidden_root_nonneg (spectral U) (spectral V)
    (spectral_isPVM hU hU4) (spectral_isPVM hV hV4)

/-- Lemma D.4 / (D.12) for arbitrary fourth-root unitaries, with no spectral data assumed. -/
theorem fourth_root_circulation_bound [NeZero r] (U V W : Mat r)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hU4 : U ^ 4 = 1) (hV4 : V ^ 4 = 1) (hW4 : W ^ 4 = 1) :
    |circulation U V W| ≤ 5 * (forbidden U V + forbidden V W + forbidden U W) := by
  simpa only [root_spectral] using circulation_bound (spectral U) (spectral V) (spectral W)
    (spectral_isPVM hU hU4) (spectral_isPVM hV hV4) (spectral_isPVM hW hW4)

end
end CGLMPBounds.Circulation
