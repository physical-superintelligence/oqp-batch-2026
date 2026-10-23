module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Holomorphic block `044-1`: exact positivity of its face block `A = Kᵀ N K`
(2 x 2). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x044k1Face

def A : Matrix (Fin 2) (Fin 2) ℤ :=
  !![402124786012189337693818781091940655553673274490895136691687168, -179690930279995146570190844256554558687994511029397891256860416;
    -179690930279995146570190844256554558687994511029397891256860416, 111488385753517928755861794628466778187725025784187068855900928]

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![39715315776278667833585822291631, 0;
    -18097897676777049034200735406914, 9339529209534680803358171438932]

def CC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1577306307209529244191027157178965669687718997368617796412640161, -718763721119980586280763377026221707293596227707905840761736734;
    -718763721119980586280763377026221707293596227707905840761736734, 414760706174843608439199211325061572651696477170199548564304020]

theorem CC_eq : C * Cᵀ = CC := by decide +kernel

theorem residual_symm : ((2 : ℤ) ^ 2 • A - CC)ᵀ = (2 : ℤ) ^ 2 • A - CC := by decide +kernel

theorem residual_rows : ∀ i, ∑ j ∈ Finset.univ.erase i, |((2 : ℤ) ^ 2 • A - CC) i j| ≤
    ((2 : ℤ) ^ 2 • A - CC) i i := by decide +kernel

/-- The face block is positive semidefinite (exact). -/
theorem A_psd : (A.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_residual A CC 2 (by norm_num)
    (by rw [← CC_eq]; exact certificateX2_int_gram_posSemidef C) residual_symm residual_rows

/-- The rational face block `(1/den) • A` (`den = 57735991281730516779464839149788173726453690037306728120320000`), in the bridge's `x2Complex` form. -/
theorem A_psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • A.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef A 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) A_psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x044k1Face
