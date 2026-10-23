module

public import ThreeCopyQutritWerner.CertificateGlobalDiagramActions

@[expose] public section


/-!
# Literal global partial transposes between the three diagram sectors

These identities use the manuscript's actual partial-transpose operations on
SixRegisters. Coefficients are unchanged, since partial transpose is complex
linear and does not take the complex conjugate.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Regrouping is injective on physical matrices, since its index map is an equivalence. -/
theorem certificateRegroupMatrix_injective {R : Type*} :
    Function.Injective (certificateRegroupMatrix (R := R)) := by
  intro M N h
  ext i j
  have he := congrFun (congrFun h (certificateSiteRegroupEquiv i))
    (certificateSiteRegroupEquiv j)
  simpa only [certificateRegroupMatrix, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using he

/-- Local partial transpose distributes over the unchanged complex coefficients. -/
theorem certificateWordTranspose_diagramCombination
    (S R : Finset (Fin 6)) (w : Equiv.Perm (Fin 6) → ℂ) :
    certificateWordTranspose S (certificateLocalDiagramCombination R w) =
      ∑ σ, w σ • certificateWordTranspose S (certificateLocalDiagram R σ) := by
  ext r c
  simp only [certificateWordTranspose, certificateLocalDiagramCombination,
    Matrix.sum_apply, Matrix.smul_apply]

theorem certificateLocalDiagramCombination_sector1
    (w : Equiv.Perm (Fin 6) → ℂ) :
    certificateWordTranspose {3, 4} (certificateLocalDiagramCombination {5} w) =
      certificateLocalDiagramCombination {3, 4, 5} w := by
  rw [certificateWordTranspose_diagramCombination]
  simp only [certificateLocalDiagram_sector1, certificateLocalDiagramCombination]

theorem certificateLocalDiagramCombination_sector2
    (w : Equiv.Perm (Fin 6) → ℂ) :
    certificateWordTranspose {1, 2, 3, 4} (certificateLocalDiagramCombination {5} w) =
      certificateLocalDiagramCombination {1, 2, 3, 4, 5} w := by
  rw [certificateWordTranspose_diagramCombination]
  simp only [certificateLocalDiagram_sector2, certificateLocalDiagramCombination]

/-- All three local transposes distribute over finite physical operator combinations. -/
theorem certificateSitewiseTranspose_weighted_sum
    {ι : Type*} [Fintype ι] (S : Finset (Fin 6)) (w : ι → ℂ)
    (M : ι → Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ) :
    certificateSitewiseTranspose S (∑ i, w i • M i) =
      ∑ i, w i • certificateSitewiseTranspose S (M i) := by
  ext r c
  simp only [certificateSitewiseTranspose, Matrix.sum_apply, Matrix.smul_apply]

/-- The physical Γ₃₄ map is exactly the global sector-0 to sector-1 diagram map. -/
theorem certificateGlobalDiagramCombination_partialTranspose
    {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    partialTranspose (certificateGlobalDiagramCombination {5} w w₁ w₂ w₃) =
      certificateGlobalDiagramCombination {3, 4, 5} w w₁ w₂ w₃ := by
  apply certificateRegroupMatrix_injective
  rw [certificateRegroupMatrix_partialTranspose, certificateGlobalDiagramCombination_regroup,
    certificateSitewiseTranspose_weighted_sum, certificateGlobalDiagramCombination_regroup]
  simp only [certificateSitewiseTranspose_kronecker, certificateLocalDiagramCombination_sector1]

/-- The physical Γ₁₂₃₄ map is exactly the global sector-0 to sector-2 diagram map. -/
theorem certificateGlobalDiagramCombination_minorTranspose
    {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    minorTranspose (certificateGlobalDiagramCombination {5} w w₁ w₂ w₃) =
      certificateGlobalDiagramCombination {1, 2, 3, 4, 5} w w₁ w₂ w₃ := by
  apply certificateRegroupMatrix_injective
  rw [certificateRegroupMatrix_minorTranspose, certificateGlobalDiagramCombination_regroup,
    certificateSitewiseTranspose_weighted_sum, certificateGlobalDiagramCombination_regroup]
  simp only [certificateSitewiseTranspose_kronecker, certificateLocalDiagramCombination_sector2]

end ThreeCopyQutritWerner
