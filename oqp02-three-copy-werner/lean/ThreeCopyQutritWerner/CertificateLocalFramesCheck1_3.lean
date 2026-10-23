module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 3, with its physical embedding. -/
theorem certificateLocalGram1_3_correct :
    (certificateLocalFrame1_3)ᵀ * certificateLocalFrame1_3 = certificateLocalGram1_3 := by
  unfold certificateLocalFrame1_3
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 9,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_3 i j =
        certificateLocalGram1_3 i j) :=
    @Nat.decidableForallFin 9 _ (fun i =>
      @Nat.decidableForallFin 9 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
