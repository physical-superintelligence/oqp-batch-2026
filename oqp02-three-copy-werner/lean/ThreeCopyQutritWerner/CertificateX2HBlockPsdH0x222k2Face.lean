module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Holomorphic block `222-2`: exact positivity of its face block `A = Kᵀ N K`
(2 x 2). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x222k2Face

def A : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1772269953265327896561573251557298590085805063134438276606853120, 1291386786299972958862470656734165291132753582378812533784576000;
    1291386786299972958862470656734165291132753582378812533784576000, 1320590785801636652043287480930880258362439802314776092454657064960]

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![72916458085921752276435124155501, 0;
    70841992065947906333990113752028, 2296861398825233741310273425212612]

def CC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![5316809859795983689684719754671832710888710582371252458428561001, 5165547145199891835449882626936626074301447205713762110026106028;
    5165547145199891835449882626936626074301447205713762110026106028, 5280590873253281280276588350471965419525994136466978934881277975328]

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

end ThreeCopyQutritWerner.X2HBlockPsdH0x222k2Face
