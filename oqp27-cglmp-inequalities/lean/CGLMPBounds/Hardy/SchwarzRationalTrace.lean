module

public import CGLMPBounds.Hardy.SchwarzPartialFractions
public import CGLMPBounds.Hardy.SchwarzResolventDerivative
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section


/-! The actual C.7 matrix integrand as a rational function with explicit
polynomial numerator and characteristic-polynomial denominator. Applying the
constructed scalar partial-fraction theorem produces explicit coefficient data
for this very integrand, retaining every root multiplicity. No spectral
simplicity, simultaneous diagonalization or contour identity is assumed. -/

open Polynomial Complex
open scoped Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Polynomial numerator of z^m Tr((R_H(z)Y)^n), before division by det^n. -/
def resolventPowerNumerator (H Y : Matrix ι ι ℂ) (m n : ℕ) : ℂ[X] :=
  X ^ m * Matrix.trace ((H.charmatrix.adjugate * Y.map C) ^ n)

lemma eval_charmatrix_as_scalar_sub (H : Matrix ι ι ℂ) (z : ℂ) :
    (Polynomial.evalRingHom z).mapMatrix H.charmatrix =
      algebraMap ℂ (Matrix ι ι ℂ) z - H := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sub_apply, Matrix.diagonal_apply]
  · simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sub_apply, Matrix.diagonal_apply, hij]

lemma eval_resolventPowerNumerator (H Y : Matrix ι ι ℂ) (m n : ℕ) (z : ℂ) :
    (resolventPowerNumerator H Y m n).eval z =
      z ^ m * Matrix.trace (((algebraMap ℂ (Matrix ι ι ℂ) z - H).adjugate * Y) ^ n) := by
  have hY : (Polynomial.evalRingHom z).mapMatrix (Y.map C) = Y := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold resolventPowerNumerator
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    ← Polynomial.coe_evalRingHom, AddMonoidHom.map_trace]
  change z ^ m * Matrix.trace ((Polynomial.evalRingHom z).mapMatrix
    ((H.charmatrix.adjugate * Y.map C) ^ n)) = _
  rw [map_pow, map_mul, RingHom.map_adjugate, eval_charmatrix_as_scalar_sub, hY]

lemma resolvent_eq_charpoly_inverse_smul_adjugate (H : Matrix ι ι ℂ) (z : ℂ) :
    resolvent H z = (H.charpoly.eval z)⁻¹ •
      (algebraMap ℂ (Matrix ι ι ℂ) z - H).adjugate := by
  change Ring.inverse (algebraMap ℂ (Matrix ι ι ℂ) z - H) = _
  rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.eval_charpoly] <;> rfl

lemma weighted_resolvent_trace_eq_rational (H Y : Matrix ι ι ℂ) (m n : ℕ) (z : ℂ) :
    z ^ m * Matrix.trace ((resolvent H z * Y) ^ n) =
      (resolventPowerNumerator H Y m n).eval z * (H.charpoly.eval z)⁻¹ ^ n := by
  rw [resolvent_eq_charpoly_inverse_smul_adjugate, smul_mul_assoc,
    _root_.smul_pow, Matrix.trace_smul, smul_eq_mul, eval_resolventPowerNumerator]
  ring

lemma inverse_charpoly_power_eq_root_product (H : Matrix ι ι ℂ) (n : ℕ) (z : ℂ) :
    (H.charpoly.eval z)⁻¹ ^ n =
      ∏ a ∈ H.charpoly.roots.toFinset, (z - a)⁻¹ ^ (H.charpoly.roots.count a * n) := by
  classical
  rw [(IsAlgClosed.splits H.charpoly).eval_eq_prod_roots_of_monic H.charpoly_monic,
    Finset.prod_multiset_map_count, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro a _
  simp only [inv_pow, pow_mul]

/-- Actual finite partial fractions for the noncommutative resolvent-power
trace. All coefficients are constructed from its literal polynomial
numerator; the identity is not supplied as a theorem premise. -/
theorem weighted_resolvent_trace_has_partial_fractions
    (H Y : Matrix ι ι ℂ) (m n : ℕ) :
    ∃ (q : ℂ[X]) (b : (a : ℂ) → Fin (H.charpoly.roots.count a * n) → ℂ),
      ∀ z : ℂ, z ∉ spectrum ℂ H →
        z ^ m * Matrix.trace ((resolvent H z * Y) ^ n) =
          q.eval z + ∑ a ∈ H.charpoly.roots.toFinset,
            ∑ j : Fin (H.charpoly.roots.count a * n), b a j * (z - a)⁻¹ ^ (j.val + 1) := by
  classical
  obtain ⟨q, b, he⟩ := exists_complex_partial_fractions
    (resolventPowerNumerator H Y m n) H.charpoly.roots.toFinset
      (fun a => H.charpoly.roots.count a * n)
  refine ⟨q, b, ?_⟩
  intro z hz
  have hzr : z ∉ H.charpoly.roots.toFinset := by
    intro hr
    exact hz (Matrix.mem_spectrum_of_isRoot_charpoly
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)))
  rw [weighted_resolvent_trace_eq_rational, inverse_charpoly_power_eq_root_product]
  exact he z hzr

end
end CGLMPBounds.Hardy
