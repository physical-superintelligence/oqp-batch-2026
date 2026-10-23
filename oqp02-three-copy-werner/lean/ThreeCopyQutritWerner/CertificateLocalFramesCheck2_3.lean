module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 2, local type 3, with its physical embedding. -/
theorem certificateLocalGram2_3_correct :
    (certificateLocalFrame2_3)ᵀ * certificateLocalFrame2_3 = certificateLocalGram2_3 := by
  unfold certificateLocalFrame2_3
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 5,
      certificateSparseFrameGramEntry certificateLocalFrameEntries2_3 i j =
        certificateLocalGram2_3 i j) :=
    @Nat.decidableForallFin 5 _ (fun i =>
      @Nat.decidableForallFin 5 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
