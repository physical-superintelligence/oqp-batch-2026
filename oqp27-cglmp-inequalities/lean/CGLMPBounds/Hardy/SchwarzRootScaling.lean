module

public import CGLMPBounds.Hardy.RootEnumeration
public import CGLMPBounds.Hardy.SchwarzExteriorContour

@[expose] public section


/-!
# Scaling the actual characteristic-root multiset

The proof uses the characteristic determinant and its split product, so every
algebraic multiplicity is preserved without a diagonalizability assumption.
Multiplication by a negative imaginary scalar carries the strictly left root
sum to the strictly upper root sum. These identities prepare the exterior g/q
bridge, but do not assert the global Schwarz-slit formula.
-/

open Complex Matrix Polynomial
open scoped Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma charpoly_smul_eq_rootVectorPolynomial (A : Matrix ι ι ℂ)
    (c : ℂ) (hc : c ≠ 0) :
    (c • A).charpoly = rootVectorPolynomial (fun i => c * charpolyRootVector A i) := by
  apply Polynomial.funext
  intro z
  rw [Matrix.eval_charpoly, rootVectorPolynomial_eval]
  have hm : Matrix.scalar ι z - c • A = c • (Matrix.scalar ι (z / c) - A) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, smul_eq_mul]
      field_simp [hc] <;> ring
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [hm, Matrix.det_smul, ← Matrix.eval_charpoly,
    charpoly_eq_rootVectorPolynomial, rootVectorPolynomial_eval]
  calc
    c ^ Fintype.card ι * ∏ i, (z / c - charpolyRootVector A i) =
        (∏ _i : ι, c) * ∏ i, (z / c - charpolyRootVector A i) := by simp
    _ = ∏ i, c * (z / c - charpolyRootVector A i) :=
      (Finset.prod_mul_distrib).symm
    _ = ∏ i, (z - c * charpolyRootVector A i) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp [hc] <;> ring

/-- Scaling preserves the complete multiset of roots and its multiplicities. -/
theorem charpoly_roots_smul (A : Matrix ι ι ℂ) (c : ℂ) (hc : c ≠ 0) :
    (c • A).charpoly.roots = A.charpoly.roots.map (fun a => c * a) := by
  rw [charpoly_smul_eq_rootVectorPolynomial A c hc, rootVectorPolynomial_roots,
    ← charpolyRootVector_multiset A, Multiset.map_map]
  rfl

/-- Pointwise strict left-half-plane root sum. It is used near zero only after
identifying it with the fixed contour; it does not define analytic continuation. -/
def negativeClusterTrace (A : Matrix ι ι ℂ) : ℂ :=
  (A.charpoly.roots.map (fun a => if a.re < 0 then a else 0)).sum /
    (Fintype.card ι : ℂ)

theorem upperClusterTrace_neg_imag_smul (A : Matrix ι ι ℂ)
    (t : ℝ) (ht : 0 < t) :
    upperClusterTrace ((-(t : ℂ) * Complex.I) • A) =
      (-(t : ℂ) * Complex.I) * negativeClusterTrace A := by
  classical
  have hc : -(t : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast ht.ne')) Complex.I_ne_zero
  have hsel (a : ℂ) : 0 < ((-(t : ℂ) * Complex.I) * a).im ↔ a.re < 0 := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, zero_sub, zero_add, add_zero, neg_zero]
    constructor <;> intro h <;> nlinarith
  have hfun : (fun a : ℂ => if 0 < ((-(t : ℂ) * Complex.I) * a).im
      then (-(t : ℂ) * Complex.I) * a else 0) =
      (fun a : ℂ => (-(t : ℂ) * Complex.I) * (if a.re < 0 then a else 0)) := by
    funext a
    simp only [hsel, mul_ite, mul_zero]
  unfold upperClusterTrace negativeClusterTrace
  rw [charpoly_roots_smul A _ hc, Multiset.map_map]
  change (A.charpoly.roots.map (fun a => if 0 < ((-(t : ℂ) * Complex.I) * a).im
      then (-(t : ℂ) * Complex.I) * a else 0)).sum / _ = _
  rw [hfun, Multiset.sum_map_mul_left]
  ring

/-- The source's exact exterior change of variables, before selecting roots. -/
theorem traceDensityPencil_eq_exterior_smul (H Y : Matrix ι ι ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    traceDensityPencil H Y z = (-z) • exteriorPencil H Y z⁻¹ := by
  have hc : (-z) * z⁻¹ = -1 := by simp [hz]
  unfold traceDensityPencil exteriorPencil
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul]
  rw [hc]
  simp [neg_smul, sub_eq_add_neg, add_comm]

end
end CGLMPBounds.Hardy
