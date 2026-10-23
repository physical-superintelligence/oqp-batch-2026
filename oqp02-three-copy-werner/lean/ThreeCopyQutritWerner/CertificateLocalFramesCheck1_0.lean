module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 0, with its physical embedding. -/
theorem certificateLocalGram1_0_correct :
    (certificateLocalFrame1_0)ᵀ * certificateLocalFrame1_0 = certificateLocalGram1_0 := by
  unfold certificateLocalFrame1_0
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 1,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_0 i j =
        certificateLocalGram1_0 i j) :=
    @Nat.decidableForallFin 1 _ (fun i =>
      @Nat.decidableForallFin 1 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
