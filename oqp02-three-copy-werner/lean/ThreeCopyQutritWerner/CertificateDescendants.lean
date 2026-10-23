module

public import ThreeCopyQutritWerner.CertificateLocalGenerators

@[expose] public section


/-!
# Exact descendant transport

A descendant is a finite word of the two literal simple lowering matrices.
The generic intertwining theorem transports an already proved highest-frame
matrix identity to every descendant. It does not assert that the descendants
span, that a matrix commutes with these generators, or that a proposed local
compression has the asserted action; those are separate exact obligations.
-/

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Apply a word of generators from left to right, in the order of the list. -/
def certificateDescendantFrame {n m R : Type*} [Fintype n] [Semiring R]
    (E : Fin 2 → Matrix n n R) (U : Matrix n m R) (word : List (Fin 2)) :
    Matrix n m R :=
  word.foldl (fun V g => E g * V) U

/-- The actual signed simple lowering generators used for local descendants. -/
def certificateLocalLowering (ket : Finset (Fin 6)) (g : Fin 2) :
    Matrix CertificateLocalWord CertificateLocalWord ℤ :=
  if g = 0 then certificateLocalGenerator ket 1 0
  else certificateLocalGenerator ket 2 1

/-- Commuting with the generators transports an exact action on a source frame
through every lowering word. No irreducible representation theorem is needed. -/
theorem certificateDescendantFrame_intertwines {n m R : Type*}
    [Fintype n] [Fintype m] [Semiring R]
    (E : Fin 2 → Matrix n n R) (M : Matrix n n R) (A : Matrix m m R)
    (hcomm : ∀ g, M * E g = E g * M) (word : List (Fin 2))
    (U : Matrix n m R) (hU : M * U = U * A) :
    M * certificateDescendantFrame E U word = certificateDescendantFrame E U word * A := by
  induction word generalizing U with
  | nil => exact hU
  | cons g word ih =>
      change M * certificateDescendantFrame E (E g * U) word =
        certificateDescendantFrame E (E g * U) word * A
      apply ih
      calc
        M * (E g * U) = (M * E g) * U := (Matrix.mul_assoc _ _ _).symm
        _ = (E g * M) * U := by rw [hcomm]
        _ = E g * (U * A) := by rw [Matrix.mul_assoc, hU]
        _ = (E g * U) * A := (Matrix.mul_assoc _ _ _).symm

/-- The sparse lowering computation is the same descendant construction on columns. -/
def certificateSparseDescendant (ket : Finset (Fin 6))
    (v : List (CertificateLocalWord × ℤ)) (word : List (Fin 2)) :
    List (CertificateLocalWord × ℤ) :=
  word.foldl (fun L g => certificateSparseAction
    (if g = 0 then certificateLocalGeneratorWord ket 1 0
     else certificateLocalGeneratorWord ket 2 1) L) v

/-- A sparse descendant still refers to the literal physical generator products. -/
theorem certificateSparseDescendant_eq
    (ket : Finset (Fin 6)) (v : List (CertificateLocalWord × ℤ))
    (word : List (Fin 2)) :
    certificateSparseVector (certificateSparseDescendant ket v word) =
      word.foldl (fun x g => certificateLocalLowering ket g *ᵥ x)
        (certificateSparseVector v) := by
  induction word generalizing v with
  | nil => rfl
  | cons g word ih =>
      change certificateSparseVector (certificateSparseDescendant ket
          (certificateSparseAction
            (if g = 0 then certificateLocalGeneratorWord ket 1 0
             else certificateLocalGeneratorWord ket 2 1) v) word) =
        word.foldl (fun x g => certificateLocalLowering ket g *ᵥ x)
          (certificateLocalLowering ket g *ᵥ certificateSparseVector v)
      rw [ih]
      congr 1
      by_cases hg : g = 0
      · have h := (certificateSparseAction_eq_mulVec
          (certificateLocalGeneratorWord ket 1 0) v).symm
        have hM : (fun r c => certificateSparseVector
            (certificateLocalGeneratorWord ket 1 0 c) r :
            Matrix CertificateLocalWord CertificateLocalWord ℤ) =
            certificateLocalGenerator ket 1 0 := rfl
        rw [hM] at h
        simpa only [certificateLocalLowering, hg, ite_true] using h
      · have h := (certificateSparseAction_eq_mulVec
          (certificateLocalGeneratorWord ket 2 1) v).symm
        have hM : (fun r c => certificateSparseVector
            (certificateLocalGeneratorWord ket 2 1 c) r :
            Matrix CertificateLocalWord CertificateLocalWord ℤ) =
            certificateLocalGenerator ket 2 1 := rfl
        rw [hM] at h
        simpa only [certificateLocalLowering, hg, ite_false] using h

end ThreeCopyQutritWerner
