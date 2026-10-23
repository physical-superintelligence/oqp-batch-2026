module

public import ThreeCopyQutritWerner.ThinFirstSiteZeros

@[expose] public section


/-!
# Every actual orthogonal pair in the thin plane gives a cut zero

The pair and the unused coordinate are the literal columns of a unitary.
Conjugating the original matrix therefore reduces its contraction to one of
the already proved off-diagonal zeros. This is not a supplied pencil condition.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]

/-- A transformed first-site block is the actual contraction by the two
corresponding columns of the local coordinate matrix. -/
theorem firstSiteBlock_adjoint_embed_eq_contraction
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    firstSiteBlock (embed₃ Vᴴ 1 1 C) i j =
      firstSiteContraction C (fun r => V r i) (fun r => V r j) := by
  ext r s
  calc
    _ = ∑ a, ∑ d, conj (V a i) * C (a, r) (d, s) * V d j := by
      simp [firstSiteBlock, embed₃, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fintype.sum_prod_type, ite_mul, mul_ite, Complex.star_def]
    _ = _ := by rw [firstSiteContraction_apply]; exact Finset.sum_comm

/-- Complete an actual orthonormal pair in the fixed binary coordinate plane
by its unused coordinate. The columns are prescribed, not chosen abstractly. -/
theorem thinFirstSite_pair_column_isometry (x y : Fin 3 → ℂ)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1) (hxy : braket x y = 0)
    (hx₂ : x 2 = 0) (hy₂ : y 2 = 0) :
    let V : Matrix (Fin 3) (Fin 3) ℂ := fun r i => ![x r, y r, if r = 2 then 1 else 0] i
    Vᴴ * V = 1 := by
  have hyx : braket y x = 0 := by rw [← conj_braket, hxy, map_zero]
  dsimp only
  ext i j
  change braket (fun r => ![x r, y r, if r = 2 then 1 else 0] i)
    (fun r => ![x r, y r, if r = 2 then 1 else 0] j) = (1 : Matrix _ _ ℂ) i j
  fin_cases i <;> fin_cases j
  · simpa [braket_self, hx]
  · simpa using hxy
  · simp [braket, hx₂]
  · simpa using hyx
  · simpa [braket_self, hy]
  · simp [braket, hy₂]
  · simp [braket, hx₂]
  · simp [braket, hy₂]
  · simp [braket]

/-- Every normalized orthogonal pair in the actual thin coordinate plane
contracts the original zero to a genuine two-site cut zero. -/
theorem firstSiteContraction_cutForm_zero_of_thin_orthonormal
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0)
    (x y : Fin 3 → ℂ) (hx : vecNormSq x = 1) (hy : vecNormSq y = 1)
    (hxy : braket x y = 0) (hx₂ : x 2 = 0) (hy₂ : y 2 = 0) :
    cutForm (firstSiteContraction C x y) = 0 := by
  let V : Matrix (Fin 3) (Fin 3) ℂ := fun r i => ![x r, y r, if r = 2 then 1 else 0] i
  have hV : Vᴴ * V = 1 := thinFirstSite_pair_column_isometry x y hx hy hxy hx₂ hy₂
  have hVH : (Vᴴ)ᴴ * Vᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hV
  have hIb : (1 : Matrix b b ℂ)ᴴ * 1 = 1 := by simp
  have hIc : (1 : Matrix c c ℂ)ᴴ * 1 = 1 := by simp
  let D := embed₃ Vᴴ (1 : Matrix b b ℂ) (1 : Matrix c c ℂ) C
  have hDr : D.rank ≤ 2 := (productRay_rank_embed₃ hVH hIb hIc C).trans_le hC
  have hDz : endpointEnergy D = 0 :=
    (productRay_endpointEnergy_embed₃ hVH hIb hIc C).trans hz
  have hV2 (a : Fin 3) : (starRingEnd ℂ) (V a 2) = if a = 2 then 1 else 0 := by
    change star (if a = 2 then (1 : ℂ) else 0) = if a = 2 then 1 else 0
    split_ifs <;> simp
  have hDrow (r : b × c) (q : Fin 3 × b × c) : D (2, r) q = 0 := by
    simp [D, embed₃, Fintype.sum_prod_type,
      Matrix.one_apply, ite_mul, mul_ite, hV2, hrow]
  have hzero := (endpointEnergy_missing_first_row_two_six_zeros D hDr hDz hDrow).1
  change cutForm (firstSiteBlock
    (embed₃ Vᴴ (1 : Matrix b b ℂ) (1 : Matrix c c ℂ) C) 0 1) = 0 at hzero
  rw [firstSiteBlock_adjoint_embed_eq_contraction] at hzero
  simpa [V] using hzero

end ThreeCopyQutritWerner
