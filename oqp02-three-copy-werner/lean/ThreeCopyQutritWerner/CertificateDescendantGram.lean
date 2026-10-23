module

public import ThreeCopyQutritWerner.CertificateDescendantFrames

@[expose] public section


/-!
Exact Gram transport for a full descendant basis. The repeated metric keeps
the original source Gram on each pair of frames of the same source type.
No orthogonality or normalization of those original source columns is assumed.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- A scalar frame metric tensored with the unchanged source metric, with
zero pairing between different original source types. -/
def certificateRepeatedFrameMetric {F T R : Type*} [DecidableEq T] [Mul R] [Zero R]
    (size : T → ℕ) (type : F → T)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) R)
    (K : Matrix F F R) : Matrix (Σ f, Fin (size (type f))) (Σ f, Fin (size (type f))) R :=
  fun i j => if h : type i.1 = type j.1 then
    K i.1 j.1 * G (type i.1) i.2 (h.symm ▸ j.2) else 0

theorem certificateRepeatedFrameMetric_zero {F T R : Type*}
    [DecidableEq T] [MulZeroClass R] (size : T → ℕ) (type : F → T)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) R)
    (K : Matrix F F R) (i j : Σ f, Fin (size (type f))) (hK : K i.1 j.1 = 0) :
    certificateRepeatedFrameMetric size type G K i j = 0 := by
  unfold certificateRepeatedFrameMetric
  split_ifs <;> simp [hK]

/-- Reindexing all physical rows by their exact weight blocks computes the
whole physical Gram from the small, already bound block matrices. -/
theorem certificateGram_of_weight_blocks {n B : Type*}
    [Fintype n] [Fintype B] [DecidableEq B]
    (size : B → ℕ) (row : (Σ b, Fin (size b)) → n)
    (hrow : Function.Bijective row)
    (S : Matrix n (Σ b, Fin (size b)) ℤ)
    (A : (b : B) → Matrix (Fin (size b)) (Fin (size b)) ℤ)
    (hblock : S.submatrix row id = Matrix.blockDiagonal' A) :
    Sᵀ * S = Matrix.blockDiagonal' (fun b => (A b)ᵀ * A b) := by
  calc
    Sᵀ * S = (S.submatrix row id)ᵀ * S.submatrix row id := by
      exact Matrix.submatrix_mul Sᵀ S id row id hrow
    _ = _ := by rw [hblock, Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul]

/-- A surjective column reindexing transports an already exact Gram identity. -/
theorem certificateGram_of_columns {n m k : Type*} [Fintype n]
    (S : Matrix n m ℤ) (P : Matrix n k ℤ) (index : k → m)
    (hindex : Function.Surjective index) (hP : P = S.submatrix id index)
    (H : Matrix m m ℤ) (hgram : Pᵀ * P = H.submatrix index index) :
    Sᵀ * S = H := by
  apply Matrix.submatrix_injective hindex hindex
  calc
    (Sᵀ * S).submatrix index index = (S.submatrix id index)ᵀ * S.submatrix id index := by
      exact Matrix.submatrix_mul Sᵀ S index id index Function.bijective_id
    _ = H.submatrix index index := by rw [← hP]; exact hgram

end ThreeCopyQutritWerner
