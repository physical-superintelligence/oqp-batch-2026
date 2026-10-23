module

public import ThreeCopyQutritWerner.CoherentPencilSupport
public import ThreeCopyQutritWerner.QutritThinFrame
public import ThreeCopyQutritWerner.BinaryPartitionCarrier

@[expose] public section


/-!
# Actual common local factor planes give an original binary carrier

The common planes contain columns of the actual rectangular source and
corange factors. Their dimensions may be zero, one or two. We construct
three binary isometries, reconstruct the full original operator on their
tensor carrier, and apply the existing original-family classification.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Two actual column families in the same thin qutrit subspace have one
constructed binary isometry fixing both, including deficient-rank cases. -/
theorem common_column_plane_exists_binary_frame
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix (Fin 3) m ℂ) (B : Matrix (Fin 3) n ℂ)
    (P : Submodule ℂ (Fin 3 → ℂ)) (hP : Module.finrank ℂ P ≤ 2)
    (hA : ∀ j, A.col j ∈ P) (hB : ∀ j, B.col j ∈ P) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ,
      Jᴴ * J = 1 ∧ J * Jᴴ * A = A ∧ J * Jᴴ * B = B := by
  classical
  let D : Matrix (Fin 3) (m ⊕ n) ℂ := fun i j => Sum.elim (A i) (B i) j
  have hc : ∀ j, D.col j ∈ P := by
    intro j
    cases j with
    | inl j => exact hA j
    | inr j => exact hB j
  have hs : Submodule.span ℂ (Set.range D.col) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hr : D.rank ≤ 2 := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (Submodule.finrank_mono hs).trans hP
  obtain ⟨J, hJ, hD⟩ := qutrit_rank_le_two_exists_binary_frame D hr
  refine ⟨J, hJ, ?_, ?_⟩
  · ext i j
    exact congrFun (congrFun hD i) (Sum.inl j)
  · ext i j
    exact congrFun (congrFun hD i) (Sum.inr j)

/-- Three separate physical flattening stabilizers fix the actual full
rectangular tensor. No factorization of its columns is assumed. -/
theorem coherentFlatten_stabilizers_fix_tensor
    {a b c n : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    (P : Matrix a a ℂ) (Q : Matrix b b ℂ) (R : Matrix c c ℂ)
    (X : Matrix (a × b × c) n ℂ)
    (h₁ : P * coherentFlatten₁ X = coherentFlatten₁ X)
    (h₂ : Q * coherentFlatten₂ X = coherentFlatten₂ X)
    (h₃ : R * coherentFlatten₃ X = coherentFlatten₃ X) :
    (P ⊗ₖ (Q ⊗ₖ R)) * X = X := by
  ext ⟨i, j, k⟩ s
  have h3 (a : a) (b : b) : ∑ l, R k l * X (a, b, l) s = X (a, b, k) s :=
    congrFun (congrFun h₃ k) ((a, b), s)
  have h2 (a : a) : ∑ l, Q j l * X (a, l, k) s = X (a, j, k) s :=
    congrFun (congrFun h₂ j) ((a, k), s)
  have h1 : ∑ l, P i l * X (l, j, k) s = X (i, j, k) s :=
    congrFun (congrFun h₁ i) ((j, k), s)
  calc
    _ = ∑ a, P i a * (∑ b, Q j b * (∑ c, R k c * X (a, b, c) s)) := by
      simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = X (i, j, k) s := by simp only [h3, h2, h1]

/-- All three common local factor planes construct the exact original
binary carrier. The compressed matrix is explicitly obtained from X and Y. -/
theorem coherent_common_planes_exists_binary_carrier
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (P₁ P₂ P₃ : Submodule ℂ (Fin 3 → ℂ))
    (hp₁ : Module.finrank ℂ P₁ ≤ 2) (hp₂ : Module.finrank ℂ P₂ ≤ 2)
    (hp₃ : Module.finrank ℂ P₃ ≤ 2)
    (hx₁ : ∀ j, (coherentFlatten₁ X).col j ∈ P₁)
    (hy₁ : ∀ j, (coherentFlatten₁ Y).col j ∈ P₁)
    (hx₂ : ∀ j, (coherentFlatten₂ X).col j ∈ P₂)
    (hy₂ : ∀ j, (coherentFlatten₂ Y).col j ∈ P₂)
    (hx₃ : ∀ j, (coherentFlatten₃ X).col j ∈ P₃)
    (hy₃ : ∀ j, (coherentFlatten₃ Y).col j ∈ P₃) :
    ∃ (J₁ J₂ J₃ : Matrix (Fin 3) (Fin 2) ℂ)
      (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ),
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧ J₃ᴴ * J₃ = 1 ∧
        X * Yᴴ = embed₃ J₁ J₂ J₃ K := by
  obtain ⟨J₁, h₁, hX₁, hY₁⟩ := common_column_plane_exists_binary_frame _ _ P₁ hp₁ hx₁ hy₁
  obtain ⟨J₂, h₂, hX₂, hY₂⟩ := common_column_plane_exists_binary_frame _ _ P₂ hp₂ hx₂ hy₂
  obtain ⟨J₃, h₃, hX₃, hY₃⟩ := common_column_plane_exists_binary_frame _ _ P₃ hp₃ hx₃ hy₃
  let W := J₁ ⊗ₖ (J₂ ⊗ₖ J₃)
  have hW : W * Wᴴ = (J₁ * J₁ᴴ) ⊗ₖ ((J₂ * J₂ᴴ) ⊗ₖ (J₃ * J₃ᴴ)) := by
    simp only [W, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
  have hX : W * (Wᴴ * X) = X := by
    rw [← Matrix.mul_assoc, hW]
    exact coherentFlatten_stabilizers_fix_tensor _ _ _ X hX₁ hX₂ hX₃
  have hY : W * (Wᴴ * Y) = Y := by
    rw [← Matrix.mul_assoc, hW]
    exact coherentFlatten_stabilizers_fix_tensor _ _ _ Y hY₁ hY₂ hY₃
  refine ⟨J₁, J₂, J₃, (Wᴴ * X) * (Wᴴ * Y)ᴴ, h₁, h₂, h₃, ?_⟩
  rw [embed₃_eq_mul]
  change X * Yᴴ = W * ((Wᴴ * X) * (Wᴴ * Y)ᴴ) * Wᴴ
  calc
    X * Yᴴ = (W * (Wᴴ * X)) * (W * (Wᴴ * Y))ᴴ := by rw [hX, hY]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The physical assumptions on the original qutrit matrix give its original
family classification once the three actual common factor planes are known. -/
theorem isQutritZeroFamilyMember_of_coherent_common_planes
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1)
    (P₁ P₂ P₃ : Submodule ℂ (Fin 3 → ℂ))
    (hp₁ : Module.finrank ℂ P₁ ≤ 2) (hp₂ : Module.finrank ℂ P₂ ≤ 2)
    (hp₃ : Module.finrank ℂ P₃ ≤ 2)
    (hx₁ : ∀ j, (coherentFlatten₁ X).col j ∈ P₁)
    (hy₁ : ∀ j, (coherentFlatten₁ Y).col j ∈ P₁)
    (hx₂ : ∀ j, (coherentFlatten₂ X).col j ∈ P₂)
    (hy₂ : ∀ j, (coherentFlatten₂ Y).col j ∈ P₂)
    (hx₃ : ∀ j, (coherentFlatten₃ X).col j ∈ P₃)
    (hy₃ : ∀ j, (coherentFlatten₃ Y).col j ∈ P₃) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  obtain ⟨J₁, J₂, J₃, K, h₁, h₂, h₃, he⟩ :=
    coherent_common_planes_exists_binary_carrier X Y P₁ P₂ P₃ hp₁ hp₂ hp₃
      hx₁ hy₁ hx₂ hy₂ hx₃ hy₃
  exact binaryPartition_qutrit_family_of_binary_carrier _ hC hz hN J₁ J₂ J₃ h₁ h₂ h₃ K he

end ThreeCopyQutritWerner
