module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 2, local type 0, with its physical embedding. -/
theorem certificateLocalGram2_0_correct :
    (certificateLocalFrame2_0)ᵀ * certificateLocalFrame2_0 = certificateLocalGram2_0 := by
  unfold certificateLocalFrame2_0
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 1,
      certificateSparseFrameGramEntry certificateLocalFrameEntries2_0 i j =
        certificateLocalGram2_0 i j) :=
    @Nat.decidableForallFin 1 _ (fun i =>
      @Nat.decidableForallFin 1 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
