module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 2, with its physical embedding. -/
theorem certificateLocalGram1_2_correct :
    (certificateLocalFrame1_2)ᵀ * certificateLocalFrame1_2 = certificateLocalGram1_2 := by
  unfold certificateLocalFrame1_2
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 2,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_2 i j =
        certificateLocalGram1_2 i j) :=
    @Nat.decidableForallFin 2 _ (fun i =>
      @Nat.decidableForallFin 2 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
