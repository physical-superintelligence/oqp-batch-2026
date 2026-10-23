module

public import ThreeCopyQutritWerner.CertificateTensorRealization

@[expose] public section


/-!
# Exact physical actions on the tensor frame bases

Regrouping the complete physical tensor basis gives the row-major tensor action
on each original joint source block. The coefficient matrices may be arbitrary;
this algebraic transport assumes neither Hermiticity nor positivity.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The tensor of two repeated actions is the repeated joint action after regrouping. -/
theorem certificateTensorFrame_block_action
    {F₁ F₂ T₁ T₂ : Type*} [DecidableEq F₁] [DecidableEq F₂]
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (type₁ : F₁ → T₁) (type₂ : F₂ → T₂)
    (A : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (B : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ) :
    (Matrix.blockDiagonal' (fun f => A (type₁ f)) ⊗ₖ
      Matrix.blockDiagonal' (fun f => B (type₂ f))).submatrix
      (certificateTensorFrameIndex size₁ size₂ type₁ type₂)
      (certificateTensorFrameIndex size₁ size₂ type₁ type₂) =
      Matrix.blockDiagonal' (fun f : F₁ × F₂ =>
        certificateTensorSourceGram size₁ size₂ A B (type₁ f.1, type₂ f.2)) := by
  ext ⟨⟨f₁, f₂⟩, i⟩ ⟨⟨g₁, g₂⟩, j⟩
  by_cases h₁ : f₁ = g₁
  · subst g₁
    by_cases h₂ : f₂ = g₂
    · subst g₂
      simp [certificateTensorFrameIndex, certificateTensorSourceGram,
        Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    · have hn : (f₁, f₂) ≠ (f₁, g₂) := fun h => h₂ (congrArg Prod.snd h)
      simp [certificateTensorFrameIndex, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.blockDiagonal'_apply, h₂, hn]
  · have hn : (f₁, f₂) ≠ (g₁, g₂) := fun h => h₁ (congrArg Prod.fst h)
    simp [certificateTensorFrameIndex, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.blockDiagonal'_apply, h₁, hn]

/-- Literal column reindexing transports an exact intertwining equation. -/
theorem certificate_intertwines_submatrix_columns
    {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
    (M : Matrix n n ℂ) (S : Matrix n m ℂ) (A : Matrix m m ℂ)
    (e : k ≃ m) (h : M * S = S * A) :
    M * S.submatrix id e = S.submatrix id e * A.submatrix e e := by
  calc
    M * S.submatrix id e = (M * S).submatrix id e :=
      (Matrix.submatrix_mul M S id id e Function.bijective_id).symm
    _ = (S * A).submatrix id e := by rw [h]
    _ = _ := Matrix.submatrix_mul S A id e e e.bijective

/-- Tensoring established physical systems transports their actual coefficient actions. -/
theorem certificatePhysicalFrameTensor_intertwines
    {n₁ n₂ F₁ F₂ T₁ T₂ : Type*}
    [Fintype n₁] [Fintype n₂] [Fintype F₁] [Fintype F₂]
    [DecidableEq n₁] [DecidableEq n₂] [DecidableEq F₁] [DecidableEq F₂]
    [DecidableEq T₁] [DecidableEq T₂]
    (a : CertificatePhysicalFrameSystem n₁ F₁ T₁)
    (b : CertificatePhysicalFrameSystem n₂ F₂ T₂)
    (M : Matrix n₁ n₁ ℂ) (N : Matrix n₂ n₂ ℂ)
    (A : (t : T₁) → Matrix (Fin (a.size t)) (Fin (a.size t)) ℂ)
    (B : (t : T₂) → Matrix (Fin (b.size t)) (Fin (b.size t)) ℂ)
    (hM : M * a.basis = a.basis * Matrix.blockDiagonal' (fun f => A (a.type f)))
    (hN : N * b.basis = b.basis * Matrix.blockDiagonal' (fun f => B (b.type f))) :
    (M ⊗ₖ N) * (certificatePhysicalFrameTensor a b).basis =
      (certificatePhysicalFrameTensor a b).basis * Matrix.blockDiagonal' (fun f : F₁ × F₂ =>
        certificateTensorSourceGram a.size b.size A B (a.type f.1, b.type f.2)) := by
  have h := certificate_intertwines_submatrix_columns (M ⊗ₖ N) (a.basis ⊗ₖ b.basis)
    (Matrix.blockDiagonal' (fun f => A (a.type f)) ⊗ₖ
      Matrix.blockDiagonal' (fun f => B (b.type f)))
    (certificateTensorFrameIndex a.size b.size a.type b.type)
    (certificate_kronecker_intertwines M N a.basis b.basis _ _ hM hN)
  rw [certificateTensorFrame_block_action] at h
  exact h

/-- The unchanged right-associated three-site coefficient tensor. -/
def certificateTripleSourceAction
    {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A B C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ)
    (t : T × T × T) :
    Matrix (Fin (s.size t.1 * (s.size t.2.1 * s.size t.2.2)))
      (Fin (s.size t.1 * (s.size t.2.1 * s.size t.2.2))) ℂ :=
  certificateTensorSourceGram s.size (fun t : T × T => s.size t.1 * s.size t.2)
    A (certificateTensorSourceGram s.size s.size B C) t

/-- Exact three-site physical action, with arbitrary local coefficient operators. -/
theorem certificatePhysicalFrameTriple_intertwines
    {n F T : Type*} [Fintype n] [Fintype F]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (M N P : Matrix n n ℂ)
    (A B C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ)
    (hM : M * s.basis = s.basis * Matrix.blockDiagonal' (fun f => A (s.type f)))
    (hN : N * s.basis = s.basis * Matrix.blockDiagonal' (fun f => B (s.type f)))
    (hP : P * s.basis = s.basis * Matrix.blockDiagonal' (fun f => C (s.type f))) :
    (M ⊗ₖ (N ⊗ₖ P)) * (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis =
      (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis *
        Matrix.blockDiagonal' (fun f : F × F × F => certificateTripleSourceAction s A B C
          (s.type f.1, s.type f.2.1, s.type f.2.2)) :=
  certificatePhysicalFrameTensor_intertwines s (certificatePhysicalFrameTensor s s)
    M (N ⊗ₖ P) A (certificateTensorSourceGram s.size s.size B C) hM
    (certificatePhysicalFrameTensor_intertwines s s N P B C hN hP)

/-- Actual physical PT-diagram combinations have their exact joint source action in sector 0. -/
theorem certificateThreeSiteDiagramActions0
    (w₁ w₂ w₃ : Equiv.Perm (Fin 6) → ℂ) :
    (certificateLocalDiagramCombination {5} w₁ ⊗ₖ
      (certificateLocalDiagramCombination {5} w₂ ⊗ₖ certificateLocalDiagramCombination {5} w₃)) *
        certificateThreeSiteFrameSystem0.basis = certificateThreeSiteFrameSystem0.basis *
      Matrix.blockDiagonal' (fun f => certificateTripleSourceAction certificatePhysicalFrameSystem0
        (certificateLocalDecomposition0Action w₁) (certificateLocalDecomposition0Action w₂)
        (certificateLocalDecomposition0Action w₃) (certificateThreeSiteFrameSystem0.type f)) :=
  certificatePhysicalFrameTriple_intertwines certificatePhysicalFrameSystem0 _ _ _ _ _ _
    (certificateLocalDecomposition0intertwines w₁) (certificateLocalDecomposition0intertwines w₂)
    (certificateLocalDecomposition0intertwines w₃)

/-- Actual physical PT-diagram combinations have their exact joint source action in sector 1. -/
theorem certificateThreeSiteDiagramActions1
    (w₁ w₂ w₃ : Equiv.Perm (Fin 6) → ℂ) :
    (certificateLocalDiagramCombination {3, 4, 5} w₁ ⊗ₖ
      (certificateLocalDiagramCombination {3, 4, 5} w₂ ⊗ₖ certificateLocalDiagramCombination {3, 4, 5} w₃)) *
        certificateThreeSiteFrameSystem1.basis = certificateThreeSiteFrameSystem1.basis *
      Matrix.blockDiagonal' (fun f => certificateTripleSourceAction certificatePhysicalFrameSystem1
        (certificateLocalDecomposition1Action w₁) (certificateLocalDecomposition1Action w₂)
        (certificateLocalDecomposition1Action w₃) (certificateThreeSiteFrameSystem1.type f)) :=
  certificatePhysicalFrameTriple_intertwines certificatePhysicalFrameSystem1 _ _ _ _ _ _
    (certificateLocalDecomposition1intertwines w₁) (certificateLocalDecomposition1intertwines w₂)
    (certificateLocalDecomposition1intertwines w₃)

/-- Actual physical PT-diagram combinations have their exact joint source action in sector 2. -/
theorem certificateThreeSiteDiagramActions2
    (w₁ w₂ w₃ : Equiv.Perm (Fin 6) → ℂ) :
    (certificateLocalDiagramCombination {1, 2, 3, 4, 5} w₁ ⊗ₖ
      (certificateLocalDiagramCombination {1, 2, 3, 4, 5} w₂ ⊗ₖ certificateLocalDiagramCombination {1, 2, 3, 4, 5} w₃)) *
        certificateThreeSiteFrameSystem2.basis = certificateThreeSiteFrameSystem2.basis *
      Matrix.blockDiagonal' (fun f => certificateTripleSourceAction certificatePhysicalFrameSystem2
        (certificateLocalDecomposition2Action w₁) (certificateLocalDecomposition2Action w₂)
        (certificateLocalDecomposition2Action w₃) (certificateThreeSiteFrameSystem2.type f)) :=
  certificatePhysicalFrameTriple_intertwines certificatePhysicalFrameSystem2 _ _ _ _ _ _
    (certificateLocalDecomposition2intertwines w₁) (certificateLocalDecomposition2intertwines w₂)
    (certificateLocalDecomposition2intertwines w₃)

end ThreeCopyQutritWerner
