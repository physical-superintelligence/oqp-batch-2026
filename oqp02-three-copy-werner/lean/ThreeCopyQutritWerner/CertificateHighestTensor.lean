module

public import ThreeCopyQutritWerner.CertificateTensorPermutation
public import ThreeCopyQutritWerner.CertificateImageProjector

@[expose] public section


/-!
# Original highest frames on three physical sites

The physical frame is rectangular and retains the original, nonorthogonal
source columns. Its metric is the literal tensor product of the original Gram
matrices. These identities allow the compact carrier projections to inherit
idempotence and metric selfadjointness from their actual physical operators.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- Rectangular tensor frame in exactly the original row-major source coordinates. -/
def certificateTripleHighestFrame {n : Type*} {a b c : ℕ}
    (U : Matrix n (Fin a) ℂ) (V : Matrix n (Fin b) ℂ) (W : Matrix n (Fin c) ℂ) :
    Matrix (n × n × n) (Fin (a * (b * c))) ℂ :=
  (U ⊗ₖ (V ⊗ₖ W)).submatrix id (certificateTripleSourceIndex a b c)

/-- The physical Hermitian Gram is the unchanged tensor of the three original metrics. -/
theorem certificateTripleHighestFrame_gram {n : Type*} [Fintype n] {a b c : ℕ}
    (U : Matrix n (Fin a) ℂ) (V : Matrix n (Fin b) ℂ) (W : Matrix n (Fin c) ℂ) :
    (certificateTripleHighestFrame U V W)ᴴ * certificateTripleHighestFrame U V W =
      certificateTripleSourceMatrix (Uᴴ * U) (Vᴴ * V) (Wᴴ * W) := by
  unfold certificateTripleHighestFrame
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ (certificateTripleSourceIndex a b c) id
      (certificateTripleSourceIndex a b c) Function.bijective_id]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

/-- Exact local actions tensor to the actual rectangular joint highest frame. -/
theorem certificateTripleHighestFrame_intertwines {n : Type*} [Fintype n] {a b c : ℕ}
    (M N P : Matrix n n ℂ)
    (U : Matrix n (Fin a) ℂ) (V : Matrix n (Fin b) ℂ) (W : Matrix n (Fin c) ℂ)
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ)
    (hU : M * U = U * A) (hV : N * V = V * B) (hW : P * W = W * C) :
    (M ⊗ₖ (N ⊗ₖ P)) * certificateTripleHighestFrame U V W =
      certificateTripleHighestFrame U V W * certificateTripleSourceMatrix A B C :=
  certificate_intertwines_submatrix_columns _ _ _ (certificateTripleSourceIndex a b c)
    (certificate_kronecker_intertwines _ _ _ _ _ _ hU
      (certificate_kronecker_intertwines _ _ _ _ _ _ hV hW))

/-- A finite physical sum retains its literal coefficient action on a rectangular frame. -/
theorem certificateHighestFrame_intertwines_sum {i n m : Type*}
    [Fintype i] [Fintype n] [Fintype m]
    (U : Matrix n m ℂ) (w : i → ℂ) (M : i → Matrix n n ℂ) (A : i → Matrix m m ℂ)
    (h : ∀ k, M k * U = U * A k) :
    (∑ k, w k • M k) * U = U * (∑ k, w k • A k) := by
  rw [Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.smul_mul, Matrix.mul_smul, h k]

/-- A positive original Hermitian Gram gives an ordinary explicit left inverse. -/
theorem certificateHighestFrame_gram_leftInverse {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (U : Matrix n m ℂ) (hG : (Uᴴ * U).PosDef) :
    ((Uᴴ * U)⁻¹ * Uᴴ) * U = 1 := by
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)

/-- All original sector-0 highest Gram entries remain unchanged after scalar extension. -/
theorem certificateHighestSource0_gram (t : Fin 7) :
    ((certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ))ᴴ *
      (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) =
        certificateLocalDecomposition0Gram t := by
  rw [certificateIntGram_cast_complex]
  fin_cases t
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_0_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_1_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_2_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_3_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_4_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_5_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram0_6_correct

/-- The same literal original Gram binding for every mixed local type. -/
theorem certificateHighestSource1_gram (t : Fin 8) :
    ((certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ))ᴴ *
      (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) =
        certificateLocalDecomposition1Gram t := by
  rw [certificateIntGram_cast_complex]
  fin_cases t
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_0_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_1_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_2_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_3_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_4_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_5_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_6_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram1_7_correct

/-- The same literal original Gram binding for every auxiliary local type. -/
theorem certificateHighestSource2_gram (t : Fin 7) :
    ((certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ))ᴴ *
      (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) =
        certificateLocalDecomposition2Gram t := by
  rw [certificateIntGram_cast_complex]
  fin_cases t
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_0_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_1_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_2_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_3_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_4_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_5_correct
  · exact congrArg (fun M => M.map (Int.cast : ℤ → ℂ)) certificateLocalGram2_6_correct

end ThreeCopyQutritWerner
