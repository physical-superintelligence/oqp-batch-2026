module

public import ThreeCopyQutritWerner.SharpPartialTraceEquality

@[expose] public section


/-!
# Simultaneous unitary rotation of saturated orthonormal families

The two families are rotated by the same coefficient unitary. Their actual
unweighted operator is unchanged, so its exact gamma-one equality is retained
for every rotated pair. The weights of the original singular decomposition
are not assumed to be invariant.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Original vectors as the columns of their actual coordinate matrix. -/
def sharpFamilyMatrix {ι n : Type*} (u : ι → n → ℂ) : Matrix n ι ℂ := fun r i => u i r

/-- Simultaneous rotation uses columns of the actual coefficient matrix. -/
def sharpRotateFamily {ι n : Type*} [Fintype ι]
    (W : Matrix ι ι ℂ) (u : ι → n → ℂ) : ι → n → ℂ :=
  fun i r => (sharpFamilyMatrix u * W) r i

/-- Original finite orthonormality is the literal column Gram identity. -/
theorem sharpFamilyMatrix_gram {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι]
    (u : ι → n → ℂ) (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0) :
    (sharpFamilyMatrix u)ᴴ * sharpFamilyMatrix u = 1 := by
  ext i j
  simpa only [sharpFamilyMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, braket, starRingEnd_apply] using hu i j

/-- Every simultaneous coefficient unitary preserves the complete Gram matrix. -/
theorem sharpRotateFamily_braket {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι]
    (W : Matrix ι ι ℂ) (hW : Wᴴ * W = 1)
    (u : ι → n → ℂ) (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (i j : ι) :
    braket (sharpRotateFamily W u i) (sharpRotateFamily W u j) = if i = j then 1 else 0 := by
  have hgram : (sharpFamilyMatrix u * W)ᴴ * (sharpFamilyMatrix u * W) = 1 := by
    calc
      _ = Wᴴ * ((sharpFamilyMatrix u)ᴴ * sharpFamilyMatrix u) * W := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [sharpFamilyMatrix_gram u hu, Matrix.mul_one, hW]
  have h := congrFun (congrFun hgram i) j
  simpa only [sharpRotateFamily, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, braket, starRingEnd_apply] using h

/-- The actual unweighted sum is the product of the two column matrices. -/
theorem sharpFamily_sum_ketBra {ι n : Type*} [Fintype ι]
    (u v : ι → n → ℂ) :
    ∑ i, ketBra (u i) (v i) = sharpFamilyMatrix u * (sharpFamilyMatrix v)ᴴ := by
  ext r s
  simp only [Matrix.sum_apply, ketBra, sharpFamilyMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply]

/-- The common coefficient rotation fixes the original unweighted operator. -/
theorem sharpRotateFamily_sum_ketBra {ι n : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℂ) (hW : Wᴴ * W = 1) (u v : ι → n → ℂ) :
    ∑ i, ketBra (sharpRotateFamily W u i) (sharpRotateFamily W v i) =
      ∑ i, ketBra (u i) (v i) := by
  have hWW : W * Wᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl ι)).mp hW
  rw [sharpFamily_sum_ketBra, sharpFamily_sum_ketBra]
  change (sharpFamilyMatrix u * W) * (sharpFamilyMatrix v * W)ᴴ = _
  calc
    _ = sharpFamilyMatrix u * (W * Wᴴ) * (sharpFamilyMatrix v)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hWW, Matrix.mul_one]

/-- Full complex gamma-one equality survives every common coefficient
unitary, with orthonormality and the unweighted operator derived exactly. -/
theorem sharpRotateFamily_gamma_eq_one
    {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R]
    [DecidableEq ι] [DecidableEq L] [DecidableEq R]
    (W : Matrix ι ι ℂ) (hW : Wᴴ * W = 1)
    (u v : ι → L × R → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j : ι) :
    sharpPartialTraceGamma (sharpRotateFamily W u i) (sharpRotateFamily W v i)
      (sharpRotateFamily W u j) (sharpRotateFamily W v j) = 1 := by
  have hur := sharpRotateFamily_braket W hW u hu
  have hvr := sharpRotateFamily_braket W hW v hv
  have hun (a : ι) : vecNormSq (sharpRotateFamily W u a) = 1 := by
    have h := hur a a
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  have hvn (a : ι) : vecNormSq (sharpRotateFamily W v a) = 1 := by
    have h := hvr a a
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  apply sharpPartialTraceGamma_eq_one_of_weighted_saturation
    (sharpRotateFamily W u) (sharpRotateFamily W v) (fun _ => 1) hun hvn
    (fun a b hab => by rw [hur, if_neg hab]) (fun _ => by norm_num) ?_ i j
  simp only [Complex.ofReal_one, one_smul]
  rw [sharpRotateFamily_sum_ketBra W hW]
  have h := sharpPartialTraceGamma_weighted_real u v (fun _ => 1)
  simp only [Complex.ofReal_one, one_smul, one_mul, hg, Complex.one_re] at h
  have hsum : (∑ _ : ι, (1 : ℝ)) ^ 2 = ∑ _ : ι, ∑ _ : ι, (1 : ℝ) := by
    simp [pow_two]
  rw [← hsum] at h
  linarith

end ThreeCopyQutritWerner
