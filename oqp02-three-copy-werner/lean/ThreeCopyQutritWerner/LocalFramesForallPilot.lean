module

public import ThreeCopyQutritWerner.CertificateSparseFrames

@[expose] public section


/-! Exact original-Gram proof-cost pilot after the all22 check module exited137.
The two hypotheses-free equalities retain full original 729-row embeddings and
nonorthogonal Gram matrices. No replacement has been made in the existing22 checks.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

theorem certificateLocalGram1_6_forallPilot :
    (certificateLocalFrame1_6)ᵀ * certificateLocalFrame1_6 = certificateLocalGram1_6 := by
  unfold certificateLocalFrame1_6
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 17,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_6 i j =
        certificateLocalGram1_6 i j) :=
    @Nat.decidableForallFin 17 _ (fun i =>
      @Nat.decidableForallFin 17 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

theorem certificateLocalGram1_7_forallPilot :
    (certificateLocalFrame1_7)ᵀ * certificateLocalFrame1_7 = certificateLocalGram1_7 := by
  unfold certificateLocalFrame1_7
  ext i j
  rw [certificateSparseFrame_gram]
  revert i j
  let d : Decidable (∀ i j : Fin 6,
      certificateSparseFrameGramEntry certificateLocalFrameEntries1_7 i j =
        certificateLocalGram1_7 i j) :=
    @Nat.decidableForallFin 6 _ (fun i =>
      @Nat.decidableForallFin 6 _ (fun j => inferInstance))
  exact @of_decide_eq_true _ d rfl

end ThreeCopyQutritWerner
