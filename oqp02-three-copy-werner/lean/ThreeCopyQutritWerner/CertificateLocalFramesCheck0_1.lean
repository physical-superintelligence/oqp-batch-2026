module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 0, local type 1, with its physical embedding. -/
theorem certificateLocalGram0_1_correct :
    (certificateLocalFrame0_1)ᵀ * certificateLocalFrame0_1 = certificateLocalGram0_1 := by
  unfold certificateLocalFrame0_1
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 4,
      certificateSparseFrameGramEntry certificateLocalFrameEntries0_1 i j =
        certificateLocalGram0_1 i j) :=
    @Nat.decidableForallFin 4 _ (fun i =>
      @Nat.decidableForallFin 4 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
