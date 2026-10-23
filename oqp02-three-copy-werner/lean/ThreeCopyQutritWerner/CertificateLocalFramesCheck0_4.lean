module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 0, local type 4, with its physical embedding. -/
theorem certificateLocalGram0_4_correct :
    (certificateLocalFrame0_4)ᵀ * certificateLocalFrame0_4 = certificateLocalGram0_4 := by
  unfold certificateLocalFrame0_4
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 15,
      certificateSparseFrameGramEntry certificateLocalFrameEntries0_4 i j =
        certificateLocalGram0_4 i j) :=
    @Nat.decidableForallFin 15 _ (fun i =>
      @Nat.decidableForallFin 15 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
