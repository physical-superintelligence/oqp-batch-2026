module

public import CGLMPBounds.Partition.CircularCorrelationShift

@[expose] public section


/-! The actual one-turn phase and the coefficient interchange in D.3.
The scalar-wrap baseline is subtracted explicitly, so the complementary
arc has the correct sign and no scalar offset is lost. -/

namespace CGLMPBounds.Partition
open scoped Matrix
noncomputable section

theorem sourceCyclicExtension_one_turn {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) {h : ℕ} (hh : h ≤ d) :
    sourceCyclicExtension hd V (a.val + h) =
      if a.val + h < d then V ⟨(a.val + h) % d, Nat.mod_lt _ hd⟩
      else (-Complex.I) • V ⟨(a.val + h) % d, Nat.mod_lt _ hd⟩ := by
  unfold sourceCyclicExtension
  by_cases hlt : a.val + h < d
  · simp [hlt, Nat.div_eq_of_lt hlt]
  · have hlo : d ≤ a.val + h := Nat.le_of_not_gt hlt
    have hhi : a.val + h < d + d := by omega
    have he : (a.val + h) / d = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hlo
      · simpa [two_mul] using hhi
    simp only [if_neg hlt, he, pow_one]

lemma corr_negative_I_right {r : ℕ} (V W : Circulation.Mat r) :
    Circulation.corr V ((-Complex.I) • W) = (-Complex.I) * Circulation.corr V W := by
  simp [Circulation.corr, Circulation.tr, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, mul_div_assoc] <;> ring

/-- Crossing the cyclic origin sends z to -i·conj(z), as in D.3. -/
theorem corr_wrapped_reverse {r : ℕ} (V W : Circulation.Mat r) :
    Circulation.corr W ((-Complex.I) • V) =
      (-Complex.I) * star (Circulation.corr V W) := by
  rw [corr_negative_I_right]
  congr 1
  unfold Circulation.corr Circulation.tr
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Subtracting the scalar cut value A-B interchanges the two arc
coefficients, retaining the source positive imaginary correlation. -/
theorem wrapped_scalar_pair_kernel (A B : ℝ) (z : ℂ) :
    A * (1 - ((-Complex.I) * star z).re) + B * ((-Complex.I) * star z).im - (A - B) =
      B * (1 - z.re) + A * z.im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

end
end CGLMPBounds.Partition
