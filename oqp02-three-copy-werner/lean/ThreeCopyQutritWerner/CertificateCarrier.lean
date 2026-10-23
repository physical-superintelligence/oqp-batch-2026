module

public import ThreeCopyQutritWerner.CertificateReduction

@[expose] public section


/-!
# Polynomial identities defining the certificate carriers

The manuscript's Section 4.1 and Appendix B use the same two columns `X`
in `C = X B` and `p = bivecMat X`. The following are exact identities for
arbitrary complex factors, including dependent columns and zero factors.
They impose a two-dimensional source in the full space, with no assumption
on the three physical local supports.

This module proves the incidence and Plücker relations, the mixed carrier
identity, and the three feature norm identities. The central character
projectors and the positive Gram certificate remain separate obligations.
-/

noncomputable section

open scoped BigOperators

namespace ThreeCopyQutritWerner

section PolynomialRelations

variable {n : Type*} [Fintype n]

/-- Pair antisymmetry of the source bivector, without an independence assumption. -/
theorem bivecMat_entry_skew (X : Matrix n (Fin 2) ℂ) (i j : n) :
    bivecMat X j i = -bivecMat X i j := by
  simp only [bivecMat_apply]
  ring

/-- The real `1/sqrt(2)` normalization commutes with conjugation of the source. -/
theorem bivecMat_star (X : Matrix n (Fin 2) ℂ) (i j : n) :
    bivecMat (fun a b => star (X a b)) i j = star (bivecMat X i j) := by
  rw [bivecMat_apply (fun a b => star (X a b)), bivecMat_apply X]
  simp only [Complex.star_def, map_mul, map_sub, Complex.conj_ofReal]

/-- The degree-two Plücker relation for the decomposable bivector of `X`. -/
theorem bivecMat_plucker (X : Matrix n (Fin 2) ℂ) (i j k l : n) :
    bivecMat X i j * bivecMat X k l -
      bivecMat X i k * bivecMat X j l +
      bivecMat X i l * bivecMat X j k = 0 := by
  simp only [bivecMat_apply]
  ring

/-- Every column of `X B` has zero exterior product with the bivector of `X`.
This is the common-source incidence relation `c ∧ p = 0`. -/
theorem bivecMat_incidence (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ)
    (i j k l : n) :
    (X * B) i l * bivecMat X j k -
      (X * B) j l * bivecMat X i k +
      (X * B) k l * bivecMat X i j = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, bivecMat_apply]
  ring

/-- The normalized alternation on three whole registers. -/
def certificateAlt₃ (f : n → n → n → ℂ) (i j k : n) : ℂ :=
  (f i j k + f j k i + f k i j - f i k j - f k j i - f j i k) / 6

/-- Incidence removes the three-row summand from a source column and its minor. -/
theorem certificateAlt₃_column_bivec (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (i j k l : n) :
    certificateAlt₃ (fun a b c => (X * B) a l * bivecMat X b c) i j k = 0 := by
  simp only [certificateAlt₃, Matrix.mul_apply, Fin.sum_univ_two, bivecMat_apply]
  ring

/-- Pointwise action of the manuscript's mixed carrier
`(A₁₂ - Alt₀₁₂) A₃₄` in the order `(row,p₁,p₂,p₃,p₄)`.
The matrix column is an external parameter and is not permuted. -/
def certificateMixedCarrier (f : n → n → n → n → n → ℂ)
    (i j k l m : n) : ℂ :=
  let g := fun a b c => (f a b c l m - f a b c m l) / 2
  (g i j k - g i k j) / 2 - certificateAlt₃ g i j k

/-- The literal mixed carrier fixes `C ⊗ p ⊗ p̄`.
All three factors come from the same `X,B`; no positivity premise is used. -/
theorem certificateMixedCarrier_feature (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (i j k l m q : n) :
    certificateMixedCarrier
        (fun a b c d e => (X * B) a q * bivecMat X b c * star (bivecMat X d e))
        i j k l m =
      (X * B) i q * bivecMat X j k * star (bivecMat X l m) := by
  simp only [certificateMixedCarrier, certificateAlt₃, Matrix.mul_apply,
    Fin.sum_univ_two, bivecMat_apply, star_mul', star_sub]
  ring

end PolynomialRelations

section FeatureNorms

/-- Squared norm of a product vector, in the association used by `SixRegisters`. -/
theorem vecNormSq_prod_left_assoc {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (u : a → ℂ) (v : b → ℂ) (w : c → ℂ) :
    vecNormSq (fun x : (a × b) × c => u x.1.1 * v x.1.2 * w x.2) =
      vecNormSq u * vecNormSq v * vecNormSq w := by
  simp only [vecNormSq, Fintype.sum_prod_type, Complex.normSq_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- Entrywise conjugation preserves the squared vector norm. -/
theorem vecNormSq_star {a : Type*} [Fintype a] (u : a → ℂ) :
    vecNormSq (fun x => star (u x)) = vecNormSq u := by
  simp only [vecNormSq, Complex.star_def, Complex.normSq_conj]

/-- Section 4.1: the holomorphic feature has squared norm `g² N`. -/
theorem vecNormSq_featureH (C P : Matrix (Fin 3 × Fin 3 × Fin 3)
    (Fin 3 × Fin 3 × Fin 3) ℂ) :
    vecNormSq (featureH C P) = frobSq P ^ 2 * frobSq C := by
  calc
    vecNormSq (featureH C P) = vecNormSq (vec C) * vecNormSq (vec P) *
        vecNormSq (vec P) := vecNormSq_prod_left_assoc (vec C) (vec P) (vec P)
    _ = frobSq P ^ 2 * frobSq C := by simp only [vecNormSq_vec]; ring

/-- Section 4.1: the mixed feature has the same squared norm `g² N`. -/
theorem vecNormSq_featureM (C P : Matrix (Fin 3 × Fin 3 × Fin 3)
    (Fin 3 × Fin 3 × Fin 3) ℂ) :
    vecNormSq (featureM C P) = frobSq P ^ 2 * frobSq C := by
  calc
    vecNormSq (featureM C P) = vecNormSq (vec C) * vecNormSq (vec P) *
        vecNormSq (fun x => star (vec P x)) :=
      vecNormSq_prod_left_assoc (vec C) (vec P) (fun x => star (vec P x))
    _ = frobSq P ^ 2 * frobSq C := by
      simp only [vecNormSq_star, vecNormSq_vec]
      ring

/-- Section 4.1: the antiholomorphic feature has the same squared norm `g² N`. -/
theorem vecNormSq_featureA (C P : Matrix (Fin 3 × Fin 3 × Fin 3)
    (Fin 3 × Fin 3 × Fin 3) ℂ) :
    vecNormSq (featureA C P) = frobSq P ^ 2 * frobSq C := by
  calc
    vecNormSq (featureA C P) = vecNormSq (vec C) * vecNormSq (fun x => star (vec P x)) *
        vecNormSq (fun x => star (vec P x)) :=
      vecNormSq_prod_left_assoc (vec C) (fun x => star (vec P x)) (fun x => star (vec P x))
    _ = frobSq P ^ 2 * frobSq C := by
      simp only [vecNormSq_star, vecNormSq_vec]
      ring

end FeatureNorms

end ThreeCopyQutritWerner
