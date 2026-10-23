module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 0, local type 2, with its physical embedding. -/
theorem certificateLocalGram0_2_correct :
    (certificateLocalFrame0_2)ᵀ * certificateLocalFrame0_2 = certificateLocalGram0_2 := by
  unfold certificateLocalFrame0_2
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 5,
      certificateSparseFrameGramEntry certificateLocalFrameEntries0_2 i j =
        certificateLocalGram0_2 i j) :=
    @Nat.decidableForallFin 5 _ (fun i =>
      @Nat.decidableForallFin 5 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
