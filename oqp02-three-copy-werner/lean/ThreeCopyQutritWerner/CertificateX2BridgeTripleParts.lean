module

public import ThreeCopyQutritWerner.CertificateX2BridgeTripleAlg
public import ThreeCopyQutritWerner.CertificateX2BridgeS3

@[expose] public section


/-!
# The four parts of a triple of three equal types

`x2S3Part m k` (`k : Fin 4`): the trivial projector, the sign projector, and the standard
projector split by the swap `S = x2S3Mat m 2` of the first two sites into its even and odd halves
(`std (1 ± S)/2`). They are orthogonal self-adjoint idempotents summing to the identity and commute
with every matrix commuting with the six site permutations.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable (m : ℕ)

theorem x2S3Mat_zero : x2S3Mat m 0 = 1 := by
  unfold x2S3Mat
  rw [show x2SlotMap3 m 0 = fun x => x from funext (x2SlotMap3_zero m), x2FunMat_id]

/-- The swap of the first two sites. -/
abbrev x2S3Swap : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ := x2S3Mat m 2

theorem x2S3Swap_sq : x2S3Swap m * x2S3Swap m = 1 := by
  rw [x2S3Swap, x2S3Mat_mul, show x2Perm3Mul 2 2 = 0 from rfl, x2S3Mat_zero]

theorem x2S3Swap_conjTranspose : (x2S3Swap m)ᴴ = x2S3Swap m := by
  rw [x2S3Swap, x2S3Mat_conjTranspose]
  rfl

theorem x2S3Sign_two : x2S3Sign 2 = -1 := by
  simp [x2S3Sign, x2Perm3Sign]

/-- The standard-isotypic projector. -/
def x2S3Std : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ := 1 - x2S3Avg m - x2S3Alt m

theorem x2S3Std_avg : x2S3Std m * x2S3Avg m = 0 := by
  rw [x2S3Std, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, x2S3Avg_idem, x2S3Alt_mul_avg]
  simp

theorem x2S3Avg_std : x2S3Avg m * x2S3Std m = 0 := by
  rw [x2S3Std, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, x2S3Avg_idem, x2S3Avg_mul_alt]
  simp

theorem x2S3Std_alt : x2S3Std m * x2S3Alt m = 0 := by
  rw [x2S3Std, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, x2S3Alt_idem, x2S3Avg_mul_alt]
  simp

theorem x2S3Alt_std : x2S3Alt m * x2S3Std m = 0 := by
  rw [x2S3Std, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, x2S3Alt_idem, x2S3Alt_mul_avg]
  simp

theorem x2S3Std_idem : x2S3Std m * x2S3Std m = x2S3Std m := by
  have h : x2S3Std m * x2S3Std m = x2S3Std m - x2S3Avg m * x2S3Std m - x2S3Alt m * x2S3Std m := by
    conv_lhs => rw [show x2S3Std m * x2S3Std m = (1 - x2S3Avg m - x2S3Alt m) * x2S3Std m from rfl]
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [h, x2S3Avg_std, x2S3Alt_std]
  simp

theorem x2S3Std_conjTranspose : (x2S3Std m)ᴴ = x2S3Std m := by
  rw [x2S3Std, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    x2S3Avg_conjTranspose, x2S3Alt_conjTranspose]

theorem x2S3Swap_avg : x2S3Swap m * x2S3Avg m = x2S3Avg m := x2S3Mat_mul_avg m 2

theorem x2S3Avg_swap : x2S3Avg m * x2S3Swap m = x2S3Avg m := x2S3Avg_mul_mat m 2

theorem x2S3Swap_alt : x2S3Swap m * x2S3Alt m = -x2S3Alt m := by
  rw [x2S3Swap, x2S3Mat_mul_alt, x2S3Sign_two, neg_one_smul]

theorem x2S3Alt_swap : x2S3Alt m * x2S3Swap m = -x2S3Alt m := by
  rw [x2S3Swap, x2S3Alt_mul_mat, x2S3Sign_two, neg_one_smul]

theorem x2S3Std_swap : x2S3Std m * x2S3Swap m = x2S3Swap m * x2S3Std m := by
  rw [x2S3Std, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, x2S3Avg_swap, x2S3Alt_swap, x2S3Swap_avg, x2S3Swap_alt]

/-- The four parts. -/
def x2S3Part : Fin 4 → Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ
  | 0 => x2S3Avg m
  | 1 => x2S3Alt m
  | 2 => x2S3Std m * x2InvolutionPart (x2S3Swap m) false
  | 3 => x2S3Std m * x2InvolutionPart (x2S3Swap m) true

theorem x2InvolutionPart_left_avg (b : Bool) :
    x2S3Avg m * x2InvolutionPart (x2S3Swap m) b = if b then 0 else x2S3Avg m := by
  unfold x2InvolutionPart
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, x2S3Avg_swap]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
    rw [← two_smul ℂ, smul_smul]
    norm_num
  · simp only [↓reduceIte, neg_smul, one_smul, add_neg_cancel, smul_zero]

theorem x2InvolutionPart_left_alt (b : Bool) :
    x2S3Alt m * x2InvolutionPart (x2S3Swap m) b = if b then x2S3Alt m else 0 := by
  unfold x2InvolutionPart
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, x2S3Alt_swap]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul, add_neg_cancel, smul_zero]
  · simp only [↓reduceIte, neg_smul, one_smul, neg_neg]
    rw [← two_smul ℂ, smul_smul]
    norm_num

theorem x2InvolutionPart_comm_std (b : Bool) :
    x2S3Std m * x2InvolutionPart (x2S3Swap m) b = x2InvolutionPart (x2S3Swap m) b * x2S3Std m :=
  x2InvolutionPart_comm _ _ (x2S3Std_swap m) b

theorem x2S3Part_sum : ∑ k, x2S3Part m k = 1 := by
  rw [Fin.sum_univ_four]
  simp only [x2S3Part]
  rw [add_assoc, ← Matrix.mul_add]
  have hs := x2InvolutionPart_sum (x2S3Swap m)
  rw [Fintype.sum_bool] at hs
  rw [add_comm (x2InvolutionPart (x2S3Swap m) false), hs, Matrix.mul_one, x2S3Std]
  abel

theorem x2S3Part_conjTranspose (k : Fin 4) : (x2S3Part m k)ᴴ = x2S3Part m k := by
  fin_cases k
  · exact x2S3Avg_conjTranspose m
  · exact x2S3Alt_conjTranspose m
  · show (x2S3Std m * x2InvolutionPart (x2S3Swap m) false)ᴴ = _
    rw [Matrix.conjTranspose_mul, x2InvolutionPart_conjTranspose _ (x2S3Swap_conjTranspose m),
      x2S3Std_conjTranspose, ← x2InvolutionPart_comm_std]
    rfl
  · show (x2S3Std m * x2InvolutionPart (x2S3Swap m) true)ᴴ = _
    rw [Matrix.conjTranspose_mul, x2InvolutionPart_conjTranspose _ (x2S3Swap_conjTranspose m),
      x2S3Std_conjTranspose, ← x2InvolutionPart_comm_std]
    rfl

/-- Products of the standard halves. -/
theorem x2S3_stdHalf_mul (b c : Bool) :
    (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) * (x2S3Std m * x2InvolutionPart (x2S3Swap m) c) =
      if b = c then x2S3Std m * x2InvolutionPart (x2S3Swap m) b else 0 := by
  calc (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) * (x2S3Std m * x2InvolutionPart (x2S3Swap m) c)
      = x2S3Std m * (x2InvolutionPart (x2S3Swap m) b * x2S3Std m) * x2InvolutionPart (x2S3Swap m) c := by
        simp only [Matrix.mul_assoc]
    _ = x2S3Std m * (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) * x2InvolutionPart (x2S3Swap m) c := by
        rw [x2InvolutionPart_comm_std]
    _ = (x2S3Std m * x2S3Std m) * (x2InvolutionPart (x2S3Swap m) b * x2InvolutionPart (x2S3Swap m) c) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [x2S3Std_idem, x2InvolutionPart_mul _ (x2S3Swap_sq m)]
        split_ifs <;> simp

theorem x2InvolutionPart_right_avg (b : Bool) :
    x2InvolutionPart (x2S3Swap m) b * x2S3Avg m = if b then 0 else x2S3Avg m := by
  unfold x2InvolutionPart
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, x2S3Swap_avg]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
    rw [← two_smul ℂ, smul_smul]
    norm_num
  · simp only [↓reduceIte, neg_smul, one_smul, add_neg_cancel, smul_zero]

theorem x2InvolutionPart_right_alt (b : Bool) :
    x2InvolutionPart (x2S3Swap m) b * x2S3Alt m = if b then x2S3Alt m else 0 := by
  unfold x2InvolutionPart
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, x2S3Swap_alt]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul, add_neg_cancel, smul_zero]
  · simp only [↓reduceIte, neg_smul, one_smul, neg_neg]
    rw [← two_smul ℂ, smul_smul]
    norm_num

theorem x2S3_avg_stdHalf (b : Bool) :
    x2S3Avg m * (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) = 0 := by
  rw [← Matrix.mul_assoc, x2S3Avg_std, Matrix.zero_mul]

theorem x2S3_alt_stdHalf (b : Bool) :
    x2S3Alt m * (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) = 0 := by
  rw [← Matrix.mul_assoc, x2S3Alt_std, Matrix.zero_mul]

theorem x2S3_stdHalf_avg (b : Bool) :
    (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) * x2S3Avg m = 0 := by
  rw [Matrix.mul_assoc, x2InvolutionPart_right_avg]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact x2S3Std_avg m
  · simp only [↓reduceIte, Matrix.mul_zero]

theorem x2S3_stdHalf_alt (b : Bool) :
    (x2S3Std m * x2InvolutionPart (x2S3Swap m) b) * x2S3Alt m = 0 := by
  rw [Matrix.mul_assoc, x2InvolutionPart_right_alt]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_zero]
  · simp only [↓reduceIte]
    exact x2S3Std_alt m

theorem x2S3Part_mul (k l : Fin 4) :
    x2S3Part m k * x2S3Part m l = if k = l then x2S3Part m k else 0 := by
  match k, l with
  | 0, 0 => exact (x2S3Avg_idem m).trans (if_pos rfl).symm
  | 0, 1 => exact (x2S3Avg_mul_alt m).trans (if_neg (by decide)).symm
  | 0, 2 => exact (x2S3_avg_stdHalf m false).trans (if_neg (by decide)).symm
  | 0, 3 => exact (x2S3_avg_stdHalf m true).trans (if_neg (by decide)).symm
  | 1, 0 => exact (x2S3Alt_mul_avg m).trans (if_neg (by decide)).symm
  | 1, 1 => exact (x2S3Alt_idem m).trans (if_pos rfl).symm
  | 1, 2 => exact (x2S3_alt_stdHalf m false).trans (if_neg (by decide)).symm
  | 1, 3 => exact (x2S3_alt_stdHalf m true).trans (if_neg (by decide)).symm
  | 2, 0 => exact (x2S3_stdHalf_avg m false).trans (if_neg (by decide)).symm
  | 2, 1 => exact (x2S3_stdHalf_alt m false).trans (if_neg (by decide)).symm
  | 2, 2 => exact (x2S3_stdHalf_mul m false false).trans (by simp [x2S3Part])
  | 2, 3 => exact (x2S3_stdHalf_mul m false true).trans (by simp [x2S3Part])
  | 3, 0 => exact (x2S3_stdHalf_avg m true).trans (if_neg (by decide)).symm
  | 3, 1 => exact (x2S3_stdHalf_alt m true).trans (if_neg (by decide)).symm
  | 3, 2 => exact (x2S3_stdHalf_mul m true false).trans (by simp [x2S3Part])
  | 3, 3 => exact (x2S3_stdHalf_mul m true true).trans (by simp [x2S3Part])

/-- Matrices commuting with the six site permutations commute with the four parts. -/
theorem x2S3Part_comm (X : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ)
    (hX : ∀ q, X * x2S3Mat m q = x2S3Mat m q * X) (k : Fin 4) :
    X * x2S3Part m k = x2S3Part m k * X := by
  have havg : X * x2S3Avg m = x2S3Avg m * X := by
    unfold x2S3Avg
    rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    simp only [hX]
  have halt : X * x2S3Alt m = x2S3Alt m * X := by
    unfold x2S3Alt
    rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hX]
  have hstd : X * x2S3Std m = x2S3Std m * X := by
    rw [x2S3Std, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, havg, halt]
  have hh : ∀ b, X * x2InvolutionPart (x2S3Swap m) b = x2InvolutionPart (x2S3Swap m) b * X :=
    fun b => x2InvolutionPart_comm _ _ (hX 2) b
  match k with
  | 0 => exact havg
  | 1 => exact halt
  | 2 => show X * (x2S3Std m * _) = (x2S3Std m * _) * X
         rw [← Matrix.mul_assoc, hstd, Matrix.mul_assoc, hh, ← Matrix.mul_assoc]
  | 3 => show X * (x2S3Std m * _) = (x2S3Std m * _) * X
         rw [← Matrix.mul_assoc, hstd, Matrix.mul_assoc, hh, ← Matrix.mul_assoc]

end ThreeCopyQutritWerner

end
