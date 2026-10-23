module

public import ThreeCopyQutritWerner.CertificateFrameRealization
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section


/-!
# Tensoring complete physical frames in their original metrics

The coefficient index uses the literal row-major finite product equivalence.
Tensoring the physical bases tensors their scalar descendant metrics and their
original source metrics. This retains all overlaps and permits arbitrary joint
source blocks, including blocks that do not factor as tensor products.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- The row-major regrouping of frame labels and source coordinates. -/
def certificateTensorFrameIndex
    {F₁ F₂ T₁ T₂ : Type*} (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (type₁ : F₁ → T₁) (type₂ : F₂ → T₂) :
    (Σ f : F₁ × F₂, Fin (size₁ (type₁ f.1) * size₂ (type₂ f.2))) ≃
      ((Σ f, Fin (size₁ (type₁ f))) × (Σ f, Fin (size₂ (type₂ f)))) where
  toFun x := (⟨x.1.1, (finProdFinEquiv.symm x.2).1⟩,
    ⟨x.1.2, (finProdFinEquiv.symm x.2).2⟩)
  invFun x := ⟨(x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2)⟩
  left_inv := by
    rintro ⟨⟨f, g⟩, j⟩
    exact congrArg (fun k => (⟨(f, g), k⟩ :
      Σ f : F₁ × F₂, Fin (size₁ (type₁ f.1) * size₂ (type₂ f.2))))
      (finProdFinEquiv.apply_symm_apply j)
  right_inv := by
    rintro ⟨⟨f, i⟩, ⟨g, j⟩⟩
    simp

/-- The unchanged tensor-product source Gram, with row-major finite indices. -/
def certificateTensorSourceGram {T₁ T₂ : Type*}
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (G₁ : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (G₂ : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ)
    (t : T₁ × T₂) :
    Matrix (Fin (size₁ t.1 * size₂ t.2)) (Fin (size₁ t.1 * size₂ t.2)) ℂ :=
  (G₁ t.1 ⊗ₖ G₂ t.2).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

private theorem certificate_tensor_metric_entry {T₁ T₂ : Type*}
    [DecidableEq T₁] [DecidableEq T₂]
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (G₁ : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (G₂ : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ)
    (t₁ u₁ : T₁) (t₂ u₂ : T₂) (z₁ z₂ : ℂ)
    (i : Fin (size₁ t₁ * size₂ t₂)) (j : Fin (size₁ u₁ * size₂ u₂)) :
    ((if h : t₁ = u₁ then z₁ * G₁ t₁ (finProdFinEquiv.symm i).1
      (h.symm ▸ (finProdFinEquiv.symm j).1) else 0) *
     (if h : t₂ = u₂ then z₂ * G₂ t₂ (finProdFinEquiv.symm i).2
      (h.symm ▸ (finProdFinEquiv.symm j).2) else 0)) =
    if h : (t₁, t₂) = (u₁, u₂) then
      (z₁ * z₂) * certificateTensorSourceGram size₁ size₂ G₁ G₂ (t₁, t₂)
        i (h.symm ▸ j) else 0 := by
  by_cases h₁ : t₁ = u₁
  · subst u₁
    by_cases h₂ : t₂ = u₂
    · subst u₂
      simp [certificateTensorSourceGram, Matrix.kroneckerMap_apply]
      <;> ring
    · have hn : (t₁, t₂) ≠ (t₁, u₂) := fun h => h₂ (congrArg Prod.snd h)
      simp only [dif_pos rfl, dif_neg h₂, dif_neg hn, mul_zero]
  · have hn : (t₁, t₂) ≠ (u₁, u₂) := fun h => h₁ (congrArg Prod.fst h)
    simp only [dif_neg h₁, dif_neg hn, zero_mul]

/-- Exact tensor factorization of the repeated metric after physical regrouping. -/
theorem certificateRepeatedFrameMetric_tensor
    {F₁ F₂ T₁ T₂ : Type*} [DecidableEq T₁] [DecidableEq T₂]
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (type₁ : F₁ → T₁) (type₂ : F₂ → T₂)
    (G₁ : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (G₂ : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ)
    (K₁ : Matrix F₁ F₁ ℂ) (K₂ : Matrix F₂ F₂ ℂ) :
    (certificateRepeatedFrameMetric size₁ type₁ G₁ K₁ ⊗ₖ
      certificateRepeatedFrameMetric size₂ type₂ G₂ K₂).submatrix
      (certificateTensorFrameIndex size₁ size₂ type₁ type₂)
      (certificateTensorFrameIndex size₁ size₂ type₁ type₂) =
    certificateRepeatedFrameMetric (fun t : T₁ × T₂ => size₁ t.1 * size₂ t.2)
      (fun f : F₁ × F₂ => (type₁ f.1, type₂ f.2))
      (certificateTensorSourceGram size₁ size₂ G₁ G₂) (K₁ ⊗ₖ K₂) := by
  ext ⟨⟨f₁, f₂⟩, i⟩ ⟨⟨g₁, g₂⟩, j⟩
  exact certificate_tensor_metric_entry size₁ size₂ G₁ G₂
    (type₁ f₁) (type₁ g₁) (type₂ f₂) (type₂ g₂) (K₁ f₁ g₁) (K₂ f₂ g₂) i j

/-- Reindexing all coefficient columns preserves physical bijectivity. -/
theorem certificateMatrix_bijective_submatrix_columns
    {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
    (S : Matrix n m ℂ) (e : k ≃ m) (hS : Function.Bijective S.mulVec) :
    Function.Bijective (S.submatrix id e).mulVec := by
  constructor
  · intro x y h
    have he : x ∘ e.symm = y ∘ e.symm := hS.1 (by
      simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_id] using h)
    funext j
    simpa using congrFun he (e j)
  · intro y
    obtain ⟨x, hx⟩ := hS.2 y
    refine ⟨x ∘ e, ?_⟩
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_id,
      Function.comp_assoc, Equiv.self_comp_symm] using hx

/-- The product of physical bases is still a complete physical basis after regrouping. -/
theorem certificateTensorFrame_bijective
    {n₁ n₂ F₁ F₂ T₁ T₂ : Type*}
    [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂]
    [Fintype F₁] [Fintype F₂] [DecidableEq F₁] [DecidableEq F₂]
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (type₁ : F₁ → T₁) (type₂ : F₂ → T₂)
    (S₁ : Matrix n₁ (Σ f, Fin (size₁ (type₁ f))) ℂ)
    (S₂ : Matrix n₂ (Σ f, Fin (size₂ (type₂ f))) ℂ)
    (hS₁ : Function.Bijective S₁.mulVec) (hS₂ : Function.Bijective S₂.mulVec) :
    Function.Bijective ((S₁ ⊗ₖ S₂).submatrix id
      (certificateTensorFrameIndex size₁ size₂ type₁ type₂)).mulVec :=
  certificateMatrix_bijective_submatrix_columns _ _
    (certificate_kronecker_bijective S₁ S₂ hS₁ hS₂)

/-- Exact physical Gram transport for the tensor basis. -/
theorem certificateTensorFrame_gram
    {n₁ n₂ F₁ F₂ T₁ T₂ : Type*}
    [Fintype n₁] [Fintype n₂] [DecidableEq T₁] [DecidableEq T₂]
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (type₁ : F₁ → T₁) (type₂ : F₂ → T₂)
    (S₁ : Matrix n₁ (Σ f, Fin (size₁ (type₁ f))) ℂ)
    (S₂ : Matrix n₂ (Σ f, Fin (size₂ (type₂ f))) ℂ)
    (G₁ : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (G₂ : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ)
    (K₁ : Matrix F₁ F₁ ℂ) (K₂ : Matrix F₂ F₂ ℂ)
    (h₁ : S₁ᴴ * S₁ = certificateRepeatedFrameMetric size₁ type₁ G₁ K₁)
    (h₂ : S₂ᴴ * S₂ = certificateRepeatedFrameMetric size₂ type₂ G₂ K₂) :
    let S := (S₁ ⊗ₖ S₂).submatrix id (certificateTensorFrameIndex size₁ size₂ type₁ type₂)
    Sᴴ * S = certificateRepeatedFrameMetric
      (fun t : T₁ × T₂ => size₁ t.1 * size₂ t.2)
      (fun f : F₁ × F₂ => (type₁ f.1, type₂ f.2))
      (certificateTensorSourceGram size₁ size₂ G₁ G₂) (K₁ ⊗ₖ K₂) := by
  dsimp only
  rw [Matrix.conjTranspose_submatrix]
  rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, h₁, h₂]
  exact certificateRepeatedFrameMetric_tensor size₁ size₂ type₁ type₂ G₁ G₂ K₁ K₂

/-- The original joint source metric is positive definite. -/
theorem certificateTensorSourceGram_posDef {T₁ T₂ : Type*}
    (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (G₁ : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (G₂ : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ)
    (h₁ : ∀ t, (G₁ t).PosDef) (h₂ : ∀ t, (G₂ t).PosDef) (t : T₁ × T₂) :
    (certificateTensorSourceGram size₁ size₂ G₁ G₂ t).PosDef :=
  ((h₁ t.1).kronecker (h₂ t.2)).submatrix finProdFinEquiv.symm.injective

end ThreeCopyQutritWerner
