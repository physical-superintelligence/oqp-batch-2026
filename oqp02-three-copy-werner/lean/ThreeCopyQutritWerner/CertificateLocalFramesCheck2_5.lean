module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 2, local type 5, with its physical embedding. -/
theorem certificateLocalGram2_5_correct :
    (certificateLocalFrame2_5)ᵀ * certificateLocalFrame2_5 = certificateLocalGram2_5 := by
  unfold certificateLocalFrame2_5
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 10,
      certificateSparseFrameGramEntry certificateLocalFrameEntries2_5 i j =
        certificateLocalGram2_5 i j) :=
    @Nat.decidableForallFin 10 _ (fun i =>
      @Nat.decidableForallFin 10 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
