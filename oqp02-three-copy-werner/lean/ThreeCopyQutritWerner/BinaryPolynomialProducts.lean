module

public import ThreeCopyQutritWerner.BinaryPolynomialEncoding
public import Mathlib.Data.Matrix.Basic

@[expose] public section


/-!
# Polynomial multiplication of actual binary replica coefficients

The matrix map adds the two binary exponent vectors. Consequently a literal
rank-one replica coefficient matrix maps to a product of its tensor
polynomials. The physical symmetric-projector kernel identification remains
a separate obligation.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Combine the two actual binary replica words in the same variables. -/
def binaryReplicaPolynomial (K : Matrix (σ → Fin 2) (σ → Fin 2) ℂ) :
    MvPolynomial σ ℂ :=
  ∑ a, ∑ b, MvPolynomial.monomial (binaryWordExponent a + binaryWordExponent b) (K a b)

theorem binaryReplicaPolynomial_sub
    (K H : Matrix (σ → Fin 2) (σ → Fin 2) ℂ) :
    binaryReplicaPolynomial (K - H) = binaryReplicaPolynomial K - binaryReplicaPolynomial H := by
  simp only [binaryReplicaPolynomial, Matrix.sub_apply, map_sub, Finset.sum_sub_distrib]

@[simp] theorem binaryReplicaPolynomial_zero :
    binaryReplicaPolynomial (0 : Matrix (σ → Fin 2) (σ → Fin 2) ℂ) = 0 := by
  simp [binaryReplicaPolynomial]

/-- Ordinary transpose, with no conjugation, is the replica convention. -/
theorem binaryReplicaPolynomial_rank_one (x y : (σ → Fin 2) → ℂ) :
    binaryReplicaPolynomial (fun a b => x a * y b) =
      binaryTensorPolynomial x * binaryTensorPolynomial y := by
  simp only [binaryReplicaPolynomial, binaryTensorPolynomial, Finset.sum_mul_sum,
    MvPolynomial.monomial_mul_monomial]

/-- An actual difference of two replica rays has polynomial zero exactly when
the original four tensor polynomials satisfy a product identity. -/
theorem binaryReplicaPolynomial_two_ray_zero_iff
    (x y z t : (σ → Fin 2) → ℂ) :
    binaryReplicaPolynomial (fun a b => x a * y b - z a * t b) = 0 ↔
      binaryTensorPolynomial x * binaryTensorPolynomial y =
        binaryTensorPolynomial z * binaryTensorPolynomial t := by
  have he : binaryReplicaPolynomial (fun a b => x a * y b - z a * t b) =
      binaryTensorPolynomial x * binaryTensorPolynomial y -
        binaryTensorPolynomial z * binaryTensorPolynomial t := by
    calc
      _ = binaryReplicaPolynomial (fun a b => x a * y b) -
          binaryReplicaPolynomial (fun a b => z a * t b) :=
        binaryReplicaPolynomial_sub (fun a b => x a * y b) (fun a b => z a * t b)
      _ = _ := by rw [binaryReplicaPolynomial_rank_one, binaryReplicaPolynomial_rank_one]
  rw [he, sub_eq_zero]

/-- The exact separated factor grid follows from the original tensor
coefficients and their polynomial kernel equation. No supplied factorization
or coprimality assumption is introduced. -/
theorem binaryReplicaPolynomial_zero_separated_factors
    (x y z t : (σ → Fin 2) → ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hzero : binaryReplicaPolynomial (fun a b => x a * y b - z a * t b) = 0) :
    ∃ p q r s : MvPolynomial σ ℂ,
      p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      binaryTensorPolynomial x = p * r ∧ binaryTensorPolynomial y = q * s ∧
      binaryTensorPolynomial z = p * s ∧ binaryTensorPolynomial t = q * r ∧
      (∀ i, (p.degreeOf i = 0 ∧ q.degreeOf i = 0) ∨
        (r.degreeOf i = 0 ∧ s.degreeOf i = 0)) := by
  apply exists_separated_multiaffine_product_factors
    (binaryTensorPolynomial x) (binaryTensorPolynomial y)
    (binaryTensorPolynomial z) (binaryTensorPolynomial t)
    (binaryTensorPolynomial_ne_zero hx) (binaryTensorPolynomial_ne_zero hy)
    (binaryTensorPolynomial_ne_zero hz)
    ((binaryReplicaPolynomial_two_ray_zero_iff x y z t).mp hzero)
  · exact binaryTensorPolynomial_degreeOf x
  · exact binaryTensorPolynomial_degreeOf y
  · exact binaryTensorPolynomial_degreeOf z
  · exact binaryTensorPolynomial_degreeOf t

end ThreeCopyQutritWerner
