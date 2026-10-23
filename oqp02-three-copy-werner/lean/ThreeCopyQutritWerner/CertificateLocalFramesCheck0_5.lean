module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 0, local type 5, with its physical embedding. -/
theorem certificateLocalGram0_5_correct :
    (certificateLocalFrame0_5)ᵀ * certificateLocalFrame0_5 = certificateLocalGram0_5 := by
  unfold certificateLocalFrame0_5
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 10,
      certificateSparseFrameGramEntry certificateLocalFrameEntries0_5 i j =
        certificateLocalGram0_5 i j) :=
    @Nat.decidableForallFin 10 _ (fun i =>
      @Nat.decidableForallFin 10 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
