module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 0, local type 3, with its physical embedding. -/
theorem certificateLocalGram0_3_correct :
    (certificateLocalFrame0_3)ᵀ * certificateLocalFrame0_3 = certificateLocalGram0_3 := by
  unfold certificateLocalFrame0_3
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 5,
      certificateSparseFrameGramEntry certificateLocalFrameEntries0_3 i j =
        certificateLocalGram0_3 i j) :=
    @Nat.decidableForallFin 5 _ (fun i =>
      @Nat.decidableForallFin 5 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
