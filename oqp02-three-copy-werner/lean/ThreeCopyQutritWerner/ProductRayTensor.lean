module

public import ThreeCopyQutritWerner.ProductRayLocal

@[expose] public section


/-!
# Positive tensor comparison without a generalized-eigenvalue assumption

The local bounds P=A+3B≥0 and Q=A−B≥0 admit exact positive expansions of the
three-site residual. A stronger expansion preserves a positive multiple of
each local defect, as needed for the product-ray equality argument.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace ThreeCopyQutritWerner

/-- Positivity of the repository's right-associated three-site tensor product. -/
theorem posSemidef_tensor₃ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} {C : Matrix c c ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (tensor₃ A B C).PosSemidef := by
  have ht : tensor₃ A B C = A ⊗ₖ (B ⊗ₖ C) := by
    ext i j
    simp only [tensor₃, Matrix.kroneckerMap_apply, mul_assoc]
  rw [ht]
  exact hA.kronecker (hB.kronecker hC)

/-- Sum over the three positions of one exceptional local factor. -/
def tensorMixed {n : Type*} (A B : Matrix n n ℂ) : Matrix (n × n × n) (n × n × n) ℂ :=
  tensor₃ A A B + tensor₃ A B A + tensor₃ B A A

theorem tensorMixed_posSemidef {n : Type*} [Fintype n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (tensorMixed A B).PosSemidef :=
  ((posSemidef_tensor₃ hA hA hB).add (posSemidef_tensor₃ hA hB hA)).add
    (posSemidef_tensor₃ hB hA hA)

/-- Exact positive expansion; coefficients reflect all eight local sign choices. -/
theorem tensorCube_sub_expansion {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    tensor₃ A A A - tensor₃ B B B =
      (1 / 16 : ℝ) • tensorMixed (A + (3 : ℂ) • B) (A - B) +
      (1 / 8 : ℝ) • tensorMixed (A - B) (A + (3 : ℂ) • B) +
      (7 / 16 : ℝ) • tensor₃ (A - B) (A - B) (A - B) := by
  ext i j
  simp only [tensorMixed, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  push_cast
  ring

/-- A stronger positive expansion retains each local defect against the two A factors. -/
theorem tensorCube_sub_defect_expansion {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    tensor₃ A A A - tensor₃ B B B - (1 / 4 : ℝ) • tensorMixed A (A - B) =
      (3 / 64 : ℝ) • tensorMixed (A + (3 : ℂ) • B) (A - B) +
      (1 / 32 : ℝ) • tensorMixed (A - B) (A + (3 : ℂ) • B) +
      (1 / 64 : ℝ) • tensor₃ (A - B) (A - B) (A - B) := by
  ext i j
  simp only [tensorMixed, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  push_cast
  ring

/-- The local generalized comparison implies the complete three-site comparison. -/
theorem tensorCube_sub_posSemidef {n : Type*} [Fintype n] (A B : Matrix n n ℂ)
    (hP : (A + (3 : ℂ) • B).PosSemidef) (hQ : (A - B).PosSemidef) :
    (tensor₃ A A A - tensor₃ B B B).PosSemidef := by
  rw [tensorCube_sub_expansion]
  exact (((tensorMixed_posSemidef hP hQ).smul (by norm_num : (0 : ℝ) ≤ 1 / 16)).add
    ((tensorMixed_posSemidef hQ hP).smul (by norm_num : (0 : ℝ) ≤ 1 / 8))).add
    ((posSemidef_tensor₃ hQ hQ hQ).smul (by norm_num : (0 : ℝ) ≤ 7 / 16))

/-- The positive remainder retains quantitative control of every local equality defect. -/
theorem tensorCube_sub_defect_posSemidef {n : Type*} [Fintype n] (A B : Matrix n n ℂ)
    (hP : (A + (3 : ℂ) • B).PosSemidef) (hQ : (A - B).PosSemidef) :
    (tensor₃ A A A - tensor₃ B B B - (1 / 4 : ℝ) • tensorMixed A (A - B)).PosSemidef := by
  rw [tensorCube_sub_defect_expansion]
  exact (((tensorMixed_posSemidef hP hQ).smul (by norm_num : (0 : ℝ) ≤ 3 / 64)).add
    ((tensorMixed_posSemidef hQ hP).smul (by norm_num : (0 : ℝ) ≤ 1 / 32))).add
    ((posSemidef_tensor₃ hQ hQ hQ).smul (by norm_num : (0 : ℝ) ≤ 1 / 64))

/-- Equality in a positive operator comparison forces the dominated operator's kernel.
This preserves an equality condition, rather than just its scalar nonnegativity. -/
theorem mulVec_eq_zero_of_posSemidef_dominated
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hB : B.PosSemidef) (hAB : (A - B).PosSemidef) (w : n → ℂ)
    (hzero : star w ⬝ᵥ (A *ᵥ w) = 0) : B *ᵥ w = 0 := by
  have hle : star w ⬝ᵥ (B *ᵥ w) ≤ star w ⬝ᵥ (A *ᵥ w) := by
    apply sub_nonneg.mp
    simpa only [Matrix.sub_mulVec, dotProduct_sub] using hAB.dotProduct_mulVec_nonneg w
  have hz : star w ⬝ᵥ (B *ᵥ w) = 0 :=
    le_antisymm (hzero ▸ hle) (hB.dotProduct_mulVec_nonneg w)
  exact hB.dotProduct_mulVec_zero_iff.mp hz

/-- The canonical local comparison A is positive, with its explicit half-identity margin. -/
theorem productRayA_posSemidef : productRayA.PosSemidef := by
  have hhalf : ((1 / 2 : ℂ) • (1 : Matrix ProductRayPair ProductRayPair ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  simpa only [sub_add_cancel] using productRayA_sub_half_posSemidef.add hhalf

/-- The residual controls the unweighted local defect at site ₁. -/
theorem tensorCube_dominates_local_defect₁ {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hP : (A + (3 : ℂ) • B).PosSemidef) (hQ : (A - B).PosSemidef)
    (hR : (A - (1 / 2 : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (tensor₃ A A A - tensor₃ B B B -
      (1 / 16 : ℝ) • tensor₃ (A - B) (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)).PosSemidef := by
  let Q := A - B
  let R := A - (1 / 2 : ℂ) • (1 : Matrix n n ℂ)
  let I : Matrix n n ℂ := 1
  have hI : I.PosSemidef := Matrix.PosSemidef.one
  have hlower : (tensor₃ Q A A - (1 / 4 : ℝ) • tensor₃ Q I I).PosSemidef := by
    have he : tensor₃ Q A A - (1 / 4 : ℝ) • tensor₃ Q I I =
        tensor₃ Q R A + (1 / 2 : ℝ) • tensor₃ Q I R := by
      ext i j
      simp only [Q, R, I, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul]
      push_cast
      ring
    rw [he]
    exact (posSemidef_tensor₃ hQ hR hA).add ((posSemidef_tensor₃ hQ hI hR).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hpos := (((tensorCube_sub_defect_posSemidef A B hP hQ).add
    (hlower.smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).add
      ((posSemidef_tensor₃ hA hQ hA).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).add
      ((posSemidef_tensor₃ hA hA hQ).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have he : tensor₃ A A A - tensor₃ B B B - (1 / 16 : ℝ) • tensor₃ Q I I =
      (tensor₃ A A A - tensor₃ B B B - (1 / 4 : ℝ) • tensorMixed A Q) +
        (1 / 4 : ℝ) • (tensor₃ Q A A - (1 / 4 : ℝ) • tensor₃ Q I I) +
        (1 / 4 : ℝ) • tensor₃ A Q A + (1 / 4 : ℝ) • tensor₃ A A Q := by
    ext i j
    simp only [tensorMixed, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    push_cast
    ring
  change (tensor₃ A A A - tensor₃ B B B - (1 / 16 : ℝ) • tensor₃ Q I I).PosSemidef
  rw [he]
  exact hpos

/-- The residual controls the unweighted local defect at site ₂. -/
theorem tensorCube_dominates_local_defect₂ {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hP : (A + (3 : ℂ) • B).PosSemidef) (hQ : (A - B).PosSemidef)
    (hR : (A - (1 / 2 : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (tensor₃ A A A - tensor₃ B B B -
      (1 / 16 : ℝ) • tensor₃ (1 : Matrix n n ℂ) (A - B) (1 : Matrix n n ℂ)).PosSemidef := by
  let Q := A - B
  let R := A - (1 / 2 : ℂ) • (1 : Matrix n n ℂ)
  let I : Matrix n n ℂ := 1
  have hI : I.PosSemidef := Matrix.PosSemidef.one
  have hlower : (tensor₃ A Q A - (1 / 4 : ℝ) • tensor₃ I Q I).PosSemidef := by
    have he : tensor₃ A Q A - (1 / 4 : ℝ) • tensor₃ I Q I =
        tensor₃ R Q A + (1 / 2 : ℝ) • tensor₃ I Q R := by
      ext i j
      simp only [Q, R, I, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul]
      push_cast
      ring
    rw [he]
    exact (posSemidef_tensor₃ hR hQ hA).add ((posSemidef_tensor₃ hI hQ hR).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hpos := (((tensorCube_sub_defect_posSemidef A B hP hQ).add
    (hlower.smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).add
      ((posSemidef_tensor₃ hQ hA hA).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).add
      ((posSemidef_tensor₃ hA hA hQ).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have he : tensor₃ A A A - tensor₃ B B B - (1 / 16 : ℝ) • tensor₃ I Q I =
      (tensor₃ A A A - tensor₃ B B B - (1 / 4 : ℝ) • tensorMixed A Q) +
        (1 / 4 : ℝ) • (tensor₃ A Q A - (1 / 4 : ℝ) • tensor₃ I Q I) +
        (1 / 4 : ℝ) • tensor₃ Q A A + (1 / 4 : ℝ) • tensor₃ A A Q := by
    ext i j
    simp only [tensorMixed, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    push_cast
    ring
  change (tensor₃ A A A - tensor₃ B B B - (1 / 16 : ℝ) • tensor₃ I Q I).PosSemidef
  rw [he]
  exact hpos

/-- The residual controls the unweighted local defect at site ₃. -/
theorem tensorCube_dominates_local_defect₃ {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hP : (A + (3 : ℂ) • B).PosSemidef) (hQ : (A - B).PosSemidef)
    (hR : (A - (1 / 2 : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (tensor₃ A A A - tensor₃ B B B -
      (1 / 16 : ℝ) • tensor₃ (1 : Matrix n n ℂ) (1 : Matrix n n ℂ) (A - B)).PosSemidef := by
  let Q := A - B
  let R := A - (1 / 2 : ℂ) • (1 : Matrix n n ℂ)
  let I : Matrix n n ℂ := 1
  have hI : I.PosSemidef := Matrix.PosSemidef.one
  have hlower : (tensor₃ A A Q - (1 / 4 : ℝ) • tensor₃ I I Q).PosSemidef := by
    have he : tensor₃ A A Q - (1 / 4 : ℝ) • tensor₃ I I Q =
        tensor₃ R A Q + (1 / 2 : ℝ) • tensor₃ I R Q := by
      ext i j
      simp only [Q, R, I, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul]
      push_cast
      ring
    rw [he]
    exact (posSemidef_tensor₃ hR hA hQ).add ((posSemidef_tensor₃ hI hR hQ).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hpos := (((tensorCube_sub_defect_posSemidef A B hP hQ).add
    (hlower.smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).add
      ((posSemidef_tensor₃ hQ hA hA).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).add
      ((posSemidef_tensor₃ hA hQ hA).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have he : tensor₃ A A A - tensor₃ B B B - (1 / 16 : ℝ) • tensor₃ I I Q =
      (tensor₃ A A A - tensor₃ B B B - (1 / 4 : ℝ) • tensorMixed A Q) +
        (1 / 4 : ℝ) • (tensor₃ A A Q - (1 / 4 : ℝ) • tensor₃ I I Q) +
        (1 / 4 : ℝ) • tensor₃ Q A A + (1 / 4 : ℝ) • tensor₃ A Q A := by
    ext i j
    simp only [tensorMixed, tensor₃, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    push_cast
    ring
  change (tensor₃ A A A - tensor₃ B B B - (1 / 16 : ℝ) • tensor₃ I I Q).PosSemidef
  rw [he]
  exact hpos

/-- The concrete canonical product-ray tensor residual is positive. -/
theorem productRay_tensor_residual_posSemidef :
    (tensor₃ productRayA productRayA productRayA -
      tensor₃ productRayB productRayB productRayB).PosSemidef :=
  tensorCube_sub_posSemidef _ _ productRayA_add_three_B_posSemidef productRayA_sub_B_posSemidef

end ThreeCopyQutritWerner
