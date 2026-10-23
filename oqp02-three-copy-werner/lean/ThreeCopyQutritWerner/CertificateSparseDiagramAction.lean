module

public import ThreeCopyQutritWerner.CertificateDiagramOperators
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-!
# Sparse physical pivot actions

The recovered local action needs only the original source support and the
original identity pivot rows. This formula has no sum over 729 input words.
It is the literal physical matrix action, not an externally assumed array.
Numerical action tables can be checked against it in bounded pieces when needed.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A PT-permutation entry is the exact equality of its unswapped row and permuted column. -/
theorem certificateLocalDiagram_entry {k : ℕ} {n R : Type*} [Fintype n]
    [DecidableEq n] [Zero R] [One R] (S : Finset (Fin k))
    (σ : Equiv.Perm (Fin k)) (r c : Fin k → n) :
    certificateLocalDiagram (R := R) S σ r c =
      if certificateWordSwap S r c = certificateWordSwap S c r ∘ σ then 1 else 0 := by
  have he (a b : Fin k → n) : (a = b ∘ σ) ↔ (b = a ∘ σ.symm) := by
    constructor
    · intro h
      funext i
      have hi := congrFun h (σ.symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi.symm
    · intro h
      funext i
      have hi := congrFun h (σ i)
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi.symm
  simp [certificateLocalDiagram, certificateWordTranspose,
    PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, Equiv.eq_symm_apply,
    certificateRegisterPerm, eq_comm]
  simp only [he]
  rfl

/-- Multiplication by an arbitrary physical matrix sums only a source vector's support. -/
theorem certificateMatrix_mulVec_sparseVector {n m R : Type*}
    [Fintype n] [DecidableEq n] [Semiring R]
    (M : Matrix m n R) (L : List (n × R)) (r : m) :
    (M *ᵥ certificateSparseVector L) r = (L.map fun a => M r a.1 * a.2).sum := by
  induction L with
  | nil => simp [certificateSparseVector, Matrix.mulVec, dotProduct]
  | cons a L ih =>
      have hc : certificateSparseVector (a :: L) =
          (fun w => if a.1 = w then a.2 else 0) + certificateSparseVector L := rfl
      rw [hc, Matrix.mulVec_add, Pi.add_apply, ih]
      simp [Matrix.mulVec, dotProduct, mul_ite]

/-- Exact finite support formula for a local physical diagram acting on an original frame. -/
theorem certificateLocalDiagram_mul_sparseFrame {m : ℕ}
    (entries : List (CertificateLocalWord × Fin m × ℤ))
    (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (r : CertificateLocalWord) (c : Fin m) :
    (certificateLocalDiagram (n := Fin 3) (R := ℤ) S σ *
        certificateMatrixFromSparseEntries entries) r c =
      ((certificateSparseFrameColumn entries c).map fun a =>
        if certificateWordSwap S r a.1 = certificateWordSwap S a.1 r ∘ σ
          then a.2 else 0).sum := by
  change (certificateLocalDiagram S σ *ᵥ
    (fun w => certificateMatrixFromSparseEntries entries w c)) r = _
  simp_rw [certificateMatrixFromSparseEntries_eq_column]
  rw [certificateMatrix_mulVec_sparseVector]
  simp only [certificateLocalDiagram_entry, ite_mul, one_mul, zero_mul]

/-- The integer coefficient action recovered at the source's original identity rows. -/
def certificateSparsePivotAction {m : ℕ}
    (entries : List (CertificateLocalWord × Fin m × ℤ))
    (pivot : Fin m → CertificateLocalWord)
    (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) :
    Matrix (Fin m) (Fin m) ℤ :=
  fun r c => ((certificateSparseFrameColumn entries c).map fun a =>
    if certificateWordSwap S (pivot r) a.1 = certificateWordSwap S a.1 (pivot r) ∘ σ
      then a.2 else 0).sum

/-- The symbolic pivot formula is bound to the literal physical action at every entry. -/
theorem certificateSparsePivotAction_eq {m : ℕ}
    (entries : List (CertificateLocalWord × Fin m × ℤ))
    (pivot : Fin m → CertificateLocalWord)
    (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) :
    (certificateLocalDiagram S σ * certificateMatrixFromSparseEntries entries).submatrix
        pivot id = certificateSparsePivotAction entries pivot S σ := by
  ext r c
  exact certificateLocalDiagram_mul_sparseFrame entries S σ (pivot r) c

/-- After exact source action has been proved, its original compression is `G A`. -/
theorem certificateSparsePivotAction_compression {m : ℕ}
    (entries : List (CertificateLocalWord × Fin m × ℤ))
    (pivot : Fin m → CertificateLocalWord)
    (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (hact : certificateLocalDiagram S σ * certificateMatrixFromSparseEntries entries =
      certificateMatrixFromSparseEntries entries * certificateSparsePivotAction entries pivot S σ) :
    (certificateMatrixFromSparseEntries entries)ᵀ * certificateLocalDiagram S σ *
        certificateMatrixFromSparseEntries entries =
      ((certificateMatrixFromSparseEntries entries)ᵀ * certificateMatrixFromSparseEntries entries) *
        certificateSparsePivotAction entries pivot S σ := by
  rw [Matrix.mul_assoc, hact, ← Matrix.mul_assoc]

end ThreeCopyQutritWerner
