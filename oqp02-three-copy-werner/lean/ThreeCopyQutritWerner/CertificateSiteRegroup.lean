module

public import ThreeCopyQutritWerner.CertificateDiagramOperators
public import ThreeCopyQutritWerner.CertificateReduction
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section


/-!
# The physical six registers, grouped into the three local sites

The statement base orders its registers `((row,col),(p₁,p₂)),(p₃,p₄)`.
The archive orders them `(row,p₁,p₂,p₃,p₄,col)` at each of three sites.
These explicit equivalences identify those spaces and the actual transpose
maps. In particular, the two physical transposes take the archive's sector-0
diagram convention to sector 1 and sector 2, respectively.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Put the six physical registers in the archive's exact order. -/
def certificateSixRegisterWordEquiv :
    SixRegisters ≃ (Fin 6 → Fin 3 × Fin 3 × Fin 3) where
  toFun x := ![x.1.1.1, x.1.2.1, x.1.2.2, x.2.1, x.2.2, x.1.1.2]
  invFun w := (((w 0, w 5), (w 1, w 2)), (w 3, w 4))
  left_inv _ := rfl
  right_inv w := by
    funext i
    fin_cases i <;> rfl

/-- Exchange the six-register and three-site groupings, without reordering sites. -/
def certificateWordSiteEquiv :
    (Fin 6 → Fin 3 × Fin 3 × Fin 3) ≃
      CertificateLocalWord × CertificateLocalWord × CertificateLocalWord where
  toFun w := (fun i => (w i).1, fun i => (w i).2.1, fun i => (w i).2.2)
  invFun w i := (w.1 i, w.2.1 i, w.2.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal physical-space equivalence used for three local decompositions. -/
def certificateSiteRegroupEquiv : SixRegisters ≃
    CertificateLocalWord × CertificateLocalWord × CertificateLocalWord :=
  certificateSixRegisterWordEquiv.trans certificateWordSiteEquiv

/-- Reindex a physical matrix, retaining every physical row and column. -/
def certificateRegroupMatrix {R : Type*} (M : Matrix SixRegisters SixRegisters R) :
    Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) R :=
  M.submatrix certificateSiteRegroupEquiv.symm certificateSiteRegroupEquiv.symm

/-- Regrouping respects actual operator composition. -/
theorem certificateRegroupMatrix_mul {R : Type*} [Semiring R]
    (M N : Matrix SixRegisters SixRegisters R) :
    certificateRegroupMatrix (M * N) =
      certificateRegroupMatrix M * certificateRegroupMatrix N := by
  exact (Matrix.submatrix_mul_equiv M N certificateSiteRegroupEquiv.symm
    certificateSiteRegroupEquiv.symm certificateSiteRegroupEquiv.symm).symm

/-- Applying the same register transpose at all three physical sites. -/
def certificateSitewiseTranspose {R : Type*} (S : Finset (Fin 6))
    (M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) R) :
    Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) R :=
  fun r c => M
    (certificateWordSwap S r.1 c.1,
      certificateWordSwap S r.2.1 c.2.1, certificateWordSwap S r.2.2 c.2.2)
    (certificateWordSwap S c.1 r.1,
      certificateWordSwap S c.2.1 r.2.1, certificateWordSwap S c.2.2 r.2.2)

/-- The manuscript's Γ₃₄ is exactly transpose of registers 3,4 at each site. -/
theorem certificateRegroupMatrix_partialTranspose
    (M : Matrix SixRegisters SixRegisters ℂ) :
    certificateRegroupMatrix (partialTranspose M) =
      certificateSitewiseTranspose {3, 4} (certificateRegroupMatrix M) := by
  ext r c
  rfl

/-- The manuscript's Γ₁₂₃₄ transposes exactly the four minor registers at each site. -/
theorem certificateRegroupMatrix_minorTranspose
    (M : Matrix SixRegisters SixRegisters ℂ) :
    certificateRegroupMatrix (minorTranspose M) =
      certificateSitewiseTranspose {1, 2, 3, 4} (certificateRegroupMatrix M) := by
  ext r c
  rfl

/-- The sitewise transpose acts on each factor of the physical tensor product. -/
theorem certificateSitewiseTranspose_kronecker {R : Type*} [Mul R]
    (S : Finset (Fin 6))
    (A B C : Matrix CertificateLocalWord CertificateLocalWord R) :
    certificateSitewiseTranspose S (A ⊗ₖ (B ⊗ₖ C)) =
      certificateWordTranspose S A ⊗ₖ
        (certificateWordTranspose S B ⊗ₖ certificateWordTranspose S C) := rfl

/-- Transposing the last minor pair changes the exact sector-0 convention to sector 1. -/
theorem certificateWordTranspose_sector1 {R : Type*}
    (M : Matrix CertificateLocalWord CertificateLocalWord R) :
    certificateWordTranspose {3, 4} (certificateWordTranspose {5} M) =
      certificateWordTranspose {3, 4, 5} M := by
  ext r c
  apply congrArg₂ M <;> funext i <;> fin_cases i <;>
    simp [certificateWordTranspose, certificateWordSwap]

/-- Transposing both minor pairs changes the exact sector-0 convention to sector 2. -/
theorem certificateWordTranspose_sector2 {R : Type*}
    (M : Matrix CertificateLocalWord CertificateLocalWord R) :
    certificateWordTranspose {1, 2, 3, 4} (certificateWordTranspose {5} M) =
      certificateWordTranspose {1, 2, 3, 4, 5} M := by
  ext r c
  apply congrArg₂ M <;> funext i <;> fin_cases i <;>
    simp [certificateWordTranspose, certificateWordSwap]

/-- The physical sector-1 diagram is the actual partial transpose of sector 0. -/
theorem certificateLocalDiagram_sector1 (σ : Equiv.Perm (Fin 6)) :
    certificateWordTranspose {3, 4} (certificateLocalDiagram (n := Fin 3) (R := ℂ) {5} σ) =
      certificateLocalDiagram {3, 4, 5} σ :=
  certificateWordTranspose_sector1 _

/-- The physical sector-2 diagram is the actual four-register transpose of sector 0. -/
theorem certificateLocalDiagram_sector2 (σ : Equiv.Perm (Fin 6)) :
    certificateWordTranspose {1, 2, 3, 4}
        (certificateLocalDiagram (n := Fin 3) (R := ℂ) {5} σ) =
      certificateLocalDiagram {1, 2, 3, 4, 5} σ :=
  certificateWordTranspose_sector2 _

end ThreeCopyQutritWerner
