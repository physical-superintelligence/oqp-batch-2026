module

public import ThreeCopyQutritWerner.CertificateX2OutputBlock

@[expose] public section


/-!
# Output stage: the residual block `x2Residual D Nm Na b` from its three parts

`x2Residual_eq_lit`: from `x2Target D b = T8 / 8`, `x2Out D 1 Nm b = O1 / d1`, `x2Out D 2 Na b = O2 / d2` and the
integer identity `N k₀ = T8 k₁ - O1 k₂ - O2 k₃` (with `den k₀ = 8 k₁ = d1 k₂ = d2 k₃`, a kernel check of `r²`
entries) it gives `x2Residual D Nm Na b = (1 / den) • N.map Int.cast`: the `heq` premise of the `x2_residualBlocks_posSemidef` (CertificateX2PsdReduced) for `Nlit b = N`, `den b = den`.
-/

open scoped Matrix

namespace ThreeCopyQutritWerner
namespace X2

theorem x2o_frac (a p q r : ℚ) (hq : q ≠ 0) (h : p * r = q) : a / p = a * r / q := by
  have hr : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hq h.symm
  rw [← h]
  exact (mul_div_mul_right a p hr).symm

theorem x2Residual_eq_lit (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2) (b : x2Key 0)
    (T8 O1 O2 : ℕ → ℕ → ℤ) (Nl : Matrix (x2Col 0 b) (x2Col 0 b) ℤ) (d1 d2 den k0 k1 k2 k3 : ℕ)
    (hden : 0 < den) (hk0 : 0 < k0)
    (hk1 : 8 * k1 = den * k0) (hk2 : d1 * k2 = den * k0) (hk3 : d2 * k3 = den * k0)
    (hT : x2Target D b = Matrix.of fun (c c' : x2Col 0 b) => ((T8 c c' : ℤ) : ℚ) / 8)
    (h1 : x2Out D 1 Nm b = Matrix.of fun (c c' : x2Col 0 b) => ((O1 c c' : ℤ) : ℚ) / (d1 : ℚ))
    (h2 : x2Out D 2 Na b = Matrix.of fun (c c' : x2Col 0 b) => ((O2 c c' : ℤ) : ℚ) / (d2 : ℚ))
    (hint : ∀ c c' : x2Col 0 b, Nl c c' * k0 = T8 c c' * k1 - O1 c c' * k2 - O2 c c' * k3) :
    x2Residual D Nm Na b = (1 / (den : ℚ)) • Nl.map (Int.cast : ℤ → ℚ) := by
  have hk0' : (k0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
  have hDk : ((den : ℚ) * k0) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hden.ne') hk0'
  have q1 : (8 : ℚ) * k1 = den * k0 := by exact_mod_cast hk1
  have q2 : (d1 : ℚ) * k2 = den * k0 := by exact_mod_cast hk2
  have q3 : (d2 : ℚ) * k3 = den * k0 := by exact_mod_cast hk3
  unfold x2Residual
  rw [hT, h1, h2]
  ext c c'
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [x2o_frac _ _ _ _ hDk q1, x2o_frac _ _ _ _ hDk q2, x2o_frac _ _ _ _ hDk q3,
    show (1 / (den : ℚ)) * (Nl c c' : ℚ) = (Nl c c' : ℚ) * k0 / (den * k0) by
      rw [mul_div_mul_right _ _ hk0']; ring]
  have hc : ((Nl c c' : ℤ) : ℚ) * k0 = (T8 c c' : ℚ) * k1 - (O1 c c' : ℚ) * k2 - (O2 c c' : ℚ) * k3 := by
    exact_mod_cast hint c c'
  rw [hc]
  ring

end X2
end ThreeCopyQutritWerner
