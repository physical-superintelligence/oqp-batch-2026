module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 5, with its physical embedding. -/
theorem certificateLocalGram1_5_correct :
    (certificateLocalFrame1_5)ᵀ * certificateLocalFrame1_5 = certificateLocalGram1_5 := by
  unfold certificateLocalFrame1_5
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 7,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_5 i j =
        certificateLocalGram1_5 i j) :=
    @Nat.decidableForallFin 7 _ (fun i =>
      @Nat.decidableForallFin 7 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
