module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 4, with its physical embedding. -/
theorem certificateLocalGram1_4_correct :
    (certificateLocalFrame1_4)ᵀ * certificateLocalFrame1_4 = certificateLocalGram1_4 := by
  unfold certificateLocalFrame1_4
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 7,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_4 i j =
        certificateLocalGram1_4 i j) :=
    @Nat.decidableForallFin 7 _ (fun i =>
      @Nat.decidableForallFin 7 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
