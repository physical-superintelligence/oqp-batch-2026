module

public import ThreeCopyQutritWerner.ProductRayEnergy
public import ThreeCopyQutritWerner.ProductRayTensor
public import ThreeCopyQutritWerner.ProductRaySupport

@[expose] public section


/-!
# Equality for a canonical product ray

This binds the exact Schur identity to its local Gram defects and the physical
local range dimension. The general change of local basis remains separate.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem productRayD_posSemidef : productRayD.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

/-- The residual vanishes at an energy zero, since both completed terms are positive. -/
theorem productRay_residual_eq_zero (b x d : ProductRayShore → ℂ)
    (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    expectation (tensor₃ productRayA productRayA productRayA -
      tensor₃ productRayB productRayB productRayB)
        (productRayPairTensor x (fun i => star (d i))) = 0 := by
  have hD := (posSemidef_tensor₃ productRayD_posSemidef productRayD_posSemidef
    productRayD_posSemidef).dotProduct_mulVec_nonneg
      (b + productRayRectCube productRayDinv *ᵥ
        (productRayRectCube productRayL *ᵥ productRayPairTensor x d))
  have hR := productRay_tensor_residual_posSemidef.dotProduct_mulVec_nonneg
    (productRayPairTensor x (fun i => star (d i)))
  rw [← expectation_eq_dotProduct] at hD hR
  have he := productRay_energy_completed_square b x d
  rw [hzero, Complex.ofReal_zero] at he
  apply le_antisymm _ hR
  calc
    _ ≤ _ + _ := le_add_of_nonneg_left hD
    _ = 0 := he.symm

/-- A positive lower bound for a local defect preserves the kernel equality. -/
theorem productRay_first_defect_kernel (w : ProductRayThreePairs → ℂ)
    (hzero : expectation (tensor₃ productRayA productRayA productRayA -
      tensor₃ productRayB productRayB productRayB) w = 0) :
    tensor₃ (productRayA - productRayB)
      (1 : Matrix ProductRayPair ProductRayPair ℂ) 1 *ᵥ w = 0 := by
  have hQ := (posSemidef_tensor₃ productRayA_sub_B_posSemidef
    (Matrix.PosSemidef.one : (1 : Matrix ProductRayPair ProductRayPair ℂ).PosSemidef)
    (Matrix.PosSemidef.one : (1 : Matrix ProductRayPair ProductRayPair ℂ).PosSemidef)).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hdom := tensorCube_dominates_local_defect₁ productRayA productRayB
    productRayA_posSemidef productRayA_add_three_B_posSemidef
    productRayA_sub_B_posSemidef productRayA_sub_half_posSemidef
  have hk := mulVec_eq_zero_of_posSemidef_dominated _ _ hQ hdom w
    (by simpa only [expectation_eq_dotProduct] using hzero)
  rw [Matrix.smul_mulVec] at hk
  exact (smul_eq_zero.mp hk).resolve_left (by norm_num)

/-- Tensoring the local defect with identities leaves an independent fiber equation. -/
theorem tensor₃_mulVec_identity_fiber₁ {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (w : n × n × n → ℂ) (j k : n) :
    (fun i => (tensor₃ Q (1 : Matrix n n ℂ) 1 *ᵥ w) (i, j, k)) =
      Q *ᵥ (fun i => w (i, j, k)) := by
  ext i
  simp [tensor₃, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

/-- The three literal coordinate defects vanish on every first-site fiber. -/
theorem productRay_first_defects (b x d : ProductRayShore → ℂ)
    (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    ∀ r s : Fin 3 × Fin 3,
      x (1, r) * star (d (0, s)) = 0 ∧
      x (2, r) * star (d (0, s)) = 0 ∧
      x (1, r) * star (d (2, s)) = x (2, r) * star (d (1, s)) := by
  have hk := productRay_first_defect_kernel _ (productRay_residual_eq_zero b x d hzero)
  intro r s
  have hf : (productRayA - productRayB) *ᵥ
      (fun p => productRayPairTensor x (fun i => star (d i))
        (p, (r.1, s.1), (r.2, s.2))) = 0 := by
    rw [← tensor₃_mulVec_identity_fiber₁, hk]
    rfl
  rw [productRayA_sub_B_eq_gram] at hf
  have hrows := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp hf
  simpa only [productRayPairTensor] using (productRayQ_mulVec_eq_zero_iff _).mp hrows

/-- A canonical product-ray zero with a nonzero second covector has thin source at site 1. -/
theorem productRay_canonical_zero_thin₁ (b x d : ProductRayShore → ℂ)
    (hd : d ≠ 0) (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    localRangeDim₁ (productRayMatrix b x d) ≤ 2 := by
  have hex : ∃ s, d s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext h)
  obtain ⟨⟨j, s⟩, hs⟩ := hex
  have hdef := productRay_first_defects b x d hzero
  apply localRangeDim₁_le_two_of_productRay_defects (productRayMatrix b x d)
    (fun i r => x (i, r)) (fun i s => star (d (i, s)))
    (fun r s => if r = (0, 0) then b s else 0) d
    ⟨j, s, by simpa only [ne_eq, star_eq_zero] using hs⟩
    (fun r s => (hdef r s).1) (fun r s => (hdef r s).2.1)
    (fun r s => (hdef r s).2.2)
  intro i r s
  by_cases hi : i = 0 <;> by_cases hr : r = (0, 0) <;>
    simp [productRayMatrix, Prod.mk.injEq, hi, hr]

end ThreeCopyQutritWerner
