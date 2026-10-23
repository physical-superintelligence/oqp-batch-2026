module

public import ThreeCopyQutritWerner.CertificateX2OutputIface
public import ThreeCopyQutritWerner.CertificateX2OutputResidual
public import ThreeCopyQutritWerner.CertificateX2OutputConcrete

@[expose] public section


/-!
# Output stage: one sector's output of an h block from the tables

`x2Out_of_tables`: for the concrete data, tables satisfying the global interface (`X2TableS`, `X2TableA`; the `transfer_global`), per-fiber bounds and a kernel check of `x2OutNum` against a literal `O` give
`x2Out x2DataConcrete s Nsrc b = O / q`. `x2Residual_eq_fam`: the residual block from target, two outputs and the
integer identity (numerators indexed by the block's columns). No target family is imported here.
-/

open scoped Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-- `x2Residual` from its three parts, with numerators indexed by the block's columns. -/
theorem x2Residual_eq_fam (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2) (b : x2Key 0)
    (T8 O1 O2 Nl : Matrix (x2Col 0 b) (x2Col 0 b) ℤ) (d1 d2 den k0 k1 k2 k3 : ℕ)
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

/-- The output of one source sector of block `b` from tables satisfying the global interface. -/
theorem x2Out_of_tables (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0) (W d bF q : ℕ)
    (fibS fibA : ℕ → ℕ → ℕ) (hS : X2TableS x2DataConcrete s Nsrc W (q : ℚ) fibS)
    (hA : X2TableA x2DataConcrete s Nsrc W (q : ℚ) fibA)
    (hW : 12 ≤ W) (hbF : bF + 3 ≤ W) (hB : X2BlockBounds W bF b fibS fibA)
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) <
      2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (O : Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (hchk : ∀ c c' : x2Col 0 b, x2OutNum W d b fibS fibA (x2JAll.getD (x2KeyGlobal 0 b) []) c c' = O c c') :
    x2Out x2DataConcrete s Nsrc b = Matrix.of fun (c c' : x2Col 0 b) => ((O c c' : ℤ) : ℚ) / (q : ℚ) := by
  rw [x2Out_eq_of_tables x2DataConcrete s Nsrc b W d bF (q : ℚ) fibS fibA (x2JAll.getD (x2KeyGlobal 0 b) [])
    hW hbF (x2JAll_length_h b) (x2ImageCols_concrete b) (x2BlockIface_of_tables _ _ _ b W _ fibS fibA hS hA) hB hb1 hb2]
  ext c c'
  simp only [Matrix.of_apply]
  rw [hchk c c']

end X2
end ThreeCopyQutritWerner
