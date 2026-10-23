module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Corrected source block `1-006-0`: exact positivity of its corrected face block
`A / den = Z Zᵀ / 2^160 + C` (trial plus exact correction, kernel coordinates; `A` below is its numerator,
1 x 1). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2Correction1x006k0Face

def A : Matrix (Fin 1) (Fin 1) ℤ :=
  !![779765103135963303702917827193239286376125617850984448000]

def C : Matrix (Fin 1) (Fin 1) ℤ :=
  !![48366262098780074231819386997]

def CC : Matrix (Fin 1) (Fin 1) ℤ :=
  !![2339295309407889911108753481596338886136823743664852678009]

theorem CC_eq : C * Cᵀ = CC := by decide +kernel

theorem residual_symm : ((2 : ℤ) ^ 2 • A - CC)ᵀ = (2 : ℤ) ^ 2 • A - CC := by decide +kernel

theorem residual_rows : ∀ i, ∑ j ∈ Finset.univ.erase i, |((2 : ℤ) ^ 2 • A - CC) i j| ≤
    ((2 : ℤ) ^ 2 • A - CC) i i := by decide +kernel

/-- The face block is positive semidefinite (exact). -/
theorem A_psd : (A.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_residual A CC 2 (by norm_num)
    (by rw [← CC_eq]; exact certificateX2_int_gram_posSemidef C) residual_symm residual_rows

/-- The rational face block `(1/den) • A` (`den = 46188793025384413423571871319830538981162952029845382496256000`), in the bridge's `x2Complex` form. -/
theorem A_psd_rat : (((1 / ((46188793025384413423571871319830538981162952029845382496256000 : ℤ) : ℚ)) • A.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef A 46188793025384413423571871319830538981162952029845382496256000 (by norm_num) A_psd

end ThreeCopyQutritWerner.X2Correction1x006k0Face
