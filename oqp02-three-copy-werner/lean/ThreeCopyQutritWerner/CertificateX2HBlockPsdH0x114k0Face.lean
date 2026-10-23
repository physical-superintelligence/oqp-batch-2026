module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Holomorphic block `114-0`: exact positivity of its face block `A = Kᵀ N K`
(2 x 2). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x114k0Face

def A : Matrix (Fin 2) (Fin 2) ℤ :=
  !![63064889680604700802190043903708730384957749018687656149963776, -12442320488162892270416794017396131211255922323493106769289728;
    -12442320488162892270416794017396131211255922323493106769289728, 98349947659534867048067312209612470579146522755502541747600384]

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![13754805307303120908343012194773, 0;
    -3618319622904916247019685460378, 17811307196947561267996856947840]

def CC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![189194669041814102406570131711133448920608986593530990488521529, -49769281952651569081667176069581441020452145913124374710204194;
    -49769281952651569081667176069581441020452145913124374710204194, 330334900957534767390079204934726022937383611841099174288568484]

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

end ThreeCopyQutritWerner.X2HBlockPsdH0x114k0Face
