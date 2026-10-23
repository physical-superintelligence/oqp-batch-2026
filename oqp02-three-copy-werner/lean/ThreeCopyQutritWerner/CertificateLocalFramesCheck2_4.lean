module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 2, local type 4, with its physical embedding. -/
theorem certificateLocalGram2_4_correct :
    (certificateLocalFrame2_4)ᵀ * certificateLocalFrame2_4 = certificateLocalGram2_4 := by
  unfold certificateLocalFrame2_4
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 15,
      certificateSparseFrameGramEntry certificateLocalFrameEntries2_4 i j =
        certificateLocalGram2_4 i j) :=
    @Nat.decidableForallFin 15 _ (fun i =>
      @Nat.decidableForallFin 15 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
