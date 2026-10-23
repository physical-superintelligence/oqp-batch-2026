module

public import ThreeCopyQutritWerner.ZeroReserveAlgebra
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section


/-!
# Finite scalar equality certificates for the reserve route

This file proves the ordinary finite Cauchy step and its exact sum-of-squares
equality certificate. It also completes the square in the already proved
literal two-ray reserve expansion. The sharp transition cross bound remains
an independent analytic obligation; the square-completion identity alone does
not assert reserve nonnegativity or classify its zeros.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section Scalars

variable {ι : Type*} [Fintype ι]

/-- Exact Lagrange identity, keeping all ordered pairs and their factor of two. -/
theorem zeroReserve_lagrange_identity (p q : ι → ℝ) :
    ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2 =
      2 * ((∑ i, p i ^ 2) * (∑ i, q i ^ 2) - (∑ i, p i * q i) ^ 2) := by
  have h1 : (∑ i, ∑ j, p i ^ 2 * q j ^ 2) =
      (∑ i, p i ^ 2) * (∑ j, q j ^ 2) := by rw [Finset.sum_mul_sum]
  have h2 : (∑ i, ∑ j, p j ^ 2 * q i ^ 2) =
      (∑ i, p i ^ 2) * (∑ j, q j ^ 2) := by
    rw [Finset.sum_comm]
    exact h1
  have h3 : (∑ i, ∑ j, (p i * q i) * (p j * q j)) =
      (∑ i, p i * q i) ^ 2 := by rw [pow_two, Finset.sum_mul_sum]
  have he : (∑ i, ∑ j, (p i * q j - p j * q i) ^ 2) =
      (∑ i, ∑ j, p i ^ 2 * q j ^ 2) + (∑ i, ∑ j, p j ^ 2 * q i ^ 2) -
        2 * (∑ i, ∑ j, (p i * q i) * (p j * q j)) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [he, h1, h2, h3]
  ring

/-- Equality in finite real Cauchy is equivalent to vanishing of every two-coordinate minor. -/
theorem zeroReserve_cauchy_eq_iff (p q : ι → ℝ) :
    (∑ i, p i ^ 2) * (∑ i, q i ^ 2) = (∑ i, p i * q i) ^ 2 ↔
      ∀ i j, p i * q j = p j * q i := by
  have hn : ∀ i, 0 ≤ ∑ j, (p i * q j - p j * q i) ^ 2 :=
    fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor
  · intro h
    have hz : (∑ i, ∑ j, (p i * q j - p j * q i) ^ 2) = 0 := by
      rw [zeroReserve_lagrange_identity, h, sub_self, mul_zero]
    have hi := (Fintype.sum_eq_zero_iff_of_nonneg hn).mp hz
    intro i j
    have hj := (Fintype.sum_eq_zero_iff_of_nonneg
      (fun k => sq_nonneg (p i * q k - p k * q i))).mp (congrFun hi i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (congrFun hj j))
  · intro h
    have hz : (∑ i, ∑ j, (p i * q j - p j * q i) ^ 2) = 0 := by
      simp only [h, sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    rw [zeroReserve_lagrange_identity] at hz
    linarith

/-- Finite square-root Cauchy, in exactly the form summing the three cut bounds. -/
theorem zeroReserve_sum_sqrt_mul_le (e f : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, Real.sqrt (e i * f i)) ≤ Real.sqrt ((∑ i, e i) * (∑ i, f i)) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => he i) (fun i _ => hf i)
    (fun i _ => (Real.sq_sqrt (mul_nonneg (he i) (hf i))).le)
  have hp : 0 ≤ (∑ i, e i) * (∑ i, f i) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => he i) (Finset.sum_nonneg fun i _ => hf i)
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg ((∑ i, e i) * (∑ i, f i))
  nlinarith

/-- At equality the square-root entropy vectors have every 2×2 minor zero. -/
theorem zeroReserve_sum_sqrt_mul_eq_iff (e f : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, Real.sqrt (e i * f i)) = Real.sqrt ((∑ i, e i) * (∑ i, f i)) ↔
      ∀ i j, Real.sqrt (e i) * Real.sqrt (f j) =
        Real.sqrt (e j) * Real.sqrt (f i) := by
  have hp : 0 ≤ (∑ i, e i) * (∑ i, f i) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => he i) (Finset.sum_nonneg fun i _ => hf i)
  have hc := zeroReserve_cauchy_eq_iff (fun i => Real.sqrt (e i))
    (fun i => Real.sqrt (f i))
  have heq : (∑ i, Real.sqrt (e i) ^ 2) = ∑ i, e i :=
    Finset.sum_congr rfl fun i _ => Real.sq_sqrt (he i)
  have hfq : (∑ i, Real.sqrt (f i) ^ 2) = ∑ i, f i :=
    Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hf i)
  rw [heq, hfq] at hc
  have hm : (∑ i, Real.sqrt (e i) * Real.sqrt (f i)) =
      ∑ i, Real.sqrt (e i * f i) := by
    exact Finset.sum_congr rfl fun i _ => (Real.sqrt_mul (he i) (f i)).symm
  rw [hm] at hc
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg ((∑ i, e i) * (∑ i, f i))
  have ht : 0 ≤ ∑ i, Real.sqrt (e i * f i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  constructor
  · intro h
    apply hc.mp
    rw [h, hs]
  · intro h
    have hh := hc.mpr h
    nlinarith

/-- Exact weighted square completion, before asserting a sign on its cross gap. -/
theorem zeroReserve_complete_square (E F K lam mu : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    lam ^ 2 * E + mu ^ 2 * F - 2 * lam * mu * K =
      (lam * Real.sqrt E - mu * Real.sqrt F) ^ 2 +
        2 * lam * mu * (Real.sqrt (E * F) - K) := by
  rw [Real.sqrt_mul hE]
  calc
    lam ^ 2 * E + mu ^ 2 * F - 2 * lam * mu * K =
        lam ^ 2 * Real.sqrt E ^ 2 + mu ^ 2 * Real.sqrt F ^ 2 -
          2 * lam * mu * K := by rw [Real.sq_sqrt hE, Real.sq_sqrt hF]
    _ = _ := by ring

end Scalars

section Physical

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The literal reserve splits into a square and the still-analytic sharp cross gap. -/
theorem zeroReserve_two_ray_square_identity (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) :
    4 * zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) =
      (lam * Real.sqrt (zeroReserveLocalEntropy u) -
        mu * Real.sqrt (zeroReserveLocalEntropy v)) ^ 2 +
      2 * lam * mu * (Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v) -
        (2 * invB (ketBra u v) - invA (ketBra u v))) := by
  rw [zeroReserve_two_ray_expansion u v hu hv huv]
  exact zeroReserve_complete_square _ _ _ _ _
    (zeroReserveLocalEntropy_nonneg u hu) (zeroReserveLocalEntropy_nonneg v hv)

end Physical

end ThreeCopyQutritWerner
