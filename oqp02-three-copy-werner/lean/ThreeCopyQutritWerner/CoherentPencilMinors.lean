module

public import ThreeCopyQutritWerner.Imports
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Polynomial

@[expose] public section


/-!
# The common-site polynomial step for a coherent pencil

The quadratic-null argument considers the local flattenings of `X+zY`.
If at every parameter in an infinite set all cubic minors vanish at some
physical site, a single site has all its minor polynomials identically zero.
The constant and cubic coefficients then give vanishing minors for both X
and Y at that same site. The two endpoint local planes need not coincide.

This is the algebraic final step. The analytic assertion that the coherent
positive pencil is thin at infinitely many phases is an explicit hypothesis here;
the conversion of the resulting minor conditions to physical reduced-Gram support
dimensions is in later modules.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A finite collection of polynomial zero loci cannot cover an infinite set unless
one entire family consists of zero polynomials. The family index itself need not be finite. -/
theorem exists_polynomial_family_eq_zero_of_infinite_cover
    {ι κ : Type*} [Fintype ι] (p : ι → κ → Polynomial ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hcover : ∀ z ∈ S, ∃ i, ∀ j, (p i j).eval z = 0) :
    ∃ i, ∀ j, p i j = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  choose j hj using hnone
  let P : Polynomial ℂ := ∏ i, p i (j i)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)
  have hzero : P = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hS.mono
    intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    have hpz : (∏ k, (p k (j k)).eval z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hi (j i))
    simpa only [Set.mem_setOf_eq, P, Polynomial.eval_prod, Polynomial.eval_zero] using hpz
  exact hP hzero

/-- The literal determinant polynomial of a three-column submatrix of `A+zB`.
Repeated selected columns are allowed and cause no problem. -/
def coherentPencilMinor {κ : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (cols : Fin 3 → κ) : Polynomial ℂ :=
  Matrix.det ((Polynomial.X : Polynomial ℂ) • (B.submatrix id cols).map Polynomial.C +
    (A.submatrix id cols).map Polynomial.C)

/-- Evaluation recovers the actual local-flattening determinant, not a proxy polynomial. -/
theorem coherentPencilMinor_eval {κ : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (cols : Fin 3 → κ) (z : ℂ) :
    (coherentPencilMinor A B cols).eval z = ((A + z • B).submatrix id cols).det := by
  change (Polynomial.evalRingHom z) (Matrix.det
    ((Polynomial.X : Polynomial ℂ) • (B.submatrix id cols).map Polynomial.C +
      (A.submatrix id cols).map Polynomial.C)) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (Polynomial.X * Polynomial.C (B i (cols j)) +
    Polynomial.C (A i (cols j))).eval z = A i (cols j) + z * B i (cols j)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  exact add_comm _ _

/-- Every local minor has degree at most three, including degenerate pencils. -/
theorem coherentPencilMinor_natDegree_le {κ : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (cols : Fin 3 → κ) :
    (coherentPencilMinor A B cols).natDegree ≤ 3 := by
  simpa only [coherentPencilMinor, Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le (B.submatrix id cols) (A.submatrix id cols)

/-- The constant coefficient retains the X-side local minor. -/
theorem coherentPencilMinor_coeff_zero {κ : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (cols : Fin 3 → κ) :
    (coherentPencilMinor A B cols).coeff 0 = (A.submatrix id cols).det :=
  Polynomial.coeff_det_X_add_C_zero (B.submatrix id cols) (A.submatrix id cols)

/-- The cubic coefficient retains the Y-side minor even when the degree drops. -/
theorem coherentPencilMinor_coeff_three {κ : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (cols : Fin 3 → κ) :
    (coherentPencilMinor A B cols).coeff 3 = (B.submatrix id cols).det := by
  simpa only [coherentPencilMinor, Fintype.card_fin] using
    Polynomial.coeff_det_X_add_C_card (B.submatrix id cols) (A.submatrix id cols)

/-- QR1--9's common-site step: infinitely many thin-pencil parameters force both
endpoint families of local cubic minors to vanish at one fixed physical site. -/
theorem exists_common_site_minor_zero_of_infinite_pencil
    {κ : Type*} (A B : Fin 3 → Matrix (Fin 3) κ ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hthin : ∀ z ∈ S, ∃ i, ∀ cols : Fin 3 → κ,
      ((A i + z • B i).submatrix id cols).det = 0) :
    ∃ i, (∀ cols : Fin 3 → κ, ((A i).submatrix id cols).det = 0) ∧
      (∀ cols : Fin 3 → κ, ((B i).submatrix id cols).det = 0) := by
  obtain ⟨i, hi⟩ := exists_polynomial_family_eq_zero_of_infinite_cover
    (fun i cols => coherentPencilMinor (A i) (B i) cols) S hS (by
      intro z hz
      obtain ⟨i, hi⟩ := hthin z hz
      exact ⟨i, fun cols => (coherentPencilMinor_eval (A i) (B i) cols z).trans (hi cols)⟩)
  refine ⟨i, ?_, ?_⟩
  · intro cols
    rw [← coherentPencilMinor_coeff_zero (A i) (B i) cols, hi cols]
    simp
  · intro cols
    rw [← coherentPencilMinor_coeff_three (A i) (B i) cols, hi cols]
    simp

end ThreeCopyQutritWerner

end
