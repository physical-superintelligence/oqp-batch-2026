module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 1, with its physical embedding. -/
theorem certificateLocalGram1_1_correct :
    (certificateLocalFrame1_1)ᵀ * certificateLocalFrame1_1 = certificateLocalGram1_1 := by
  unfold certificateLocalFrame1_1
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 2,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_1 i j =
        certificateLocalGram1_1 i j) :=
    @Nat.decidableForallFin 2 _ (fun i =>
      @Nat.decidableForallFin 2 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
