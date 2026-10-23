module

public import ThreeCopyQutritWerner.SharpQutritCentralSpectrum
public import Mathlib.Order.Fin.Basic

@[expose] public section


/-!
# Ordered actual central eigenvalues and the exact middle-square deficit

The order comes from the pinned Hermitian spectral theorem. An explicit
equivalence relates it to the previously recorded actual eigenvalue family.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Actual central eigenvalues in decreasing order: indices zero, one and two
are respectively the maximum, middle and minimum eigenvalues. -/
def sharpQutritCentralOrdered (d : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (sharpQutritCentralBlock_isHermitian d).eigenvalues₀
    (Fin.castOrderIso (Fintype.card_fin 3).symm i)

theorem sharpQutritCentralOrdered_antitone (d : Fin 3 → ℝ) :
    Antitone (sharpQutritCentralOrdered d) := by
  intro i j hij
  exact (sharpQutritCentralBlock_isHermitian d).eigenvalues₀_antitone
    ((Fin.castOrderIso (Fintype.card_fin 3).symm).monotone hij)

/-- This is an explicit reindexing of the original actual spectrum, not an
independently supplied triple with the same polynomial invariants. -/
theorem sharpQutritCentralOrdered_reindex (d : Fin 3 → ℝ) :
    ∃ e : Fin 3 ≃ Fin 3,
      ∀ i, sharpQutritCentralOrdered d i = sharpQutritCentralEigenvalue d (e i) := by
  let c := Fin.castOrderIso (Fintype.card_fin 3).symm
  let s : Fin (Fintype.card (Fin 3)) ≃ Fin 3 :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨c.toEquiv.trans s, ?_⟩
  intro i
  change (sharpQutritCentralBlock_isHermitian d).eigenvalues₀ (c i) =
    (sharpQutritCentralBlock_isHermitian d).eigenvalues₀ (s.symm (s (c i)))
  rw [s.symm_apply_apply]

theorem sharpQutritCentralOrdered_sum (d : Fin 3 → ℝ) :
    ∑ i, sharpQutritCentralOrdered d i = 0 := by
  obtain ⟨e, he⟩ := sharpQutritCentralOrdered_reindex d
  simp_rw [he]
  rw [e.sum_comp (sharpQutritCentralEigenvalue d), sharpQutritCentralEigenvalue_sum]

theorem sharpQutritCentralOrdered_sum_sq (d : Fin 3 → ℝ) :
    ∑ i, sharpQutritCentralOrdered d i ^ 2 = 2 * ∑ i, d i ^ 2 := by
  obtain ⟨e, he⟩ := sharpQutritCentralOrdered_reindex d
  simp_rw [he]
  rw [e.sum_comp (fun i => sharpQutritCentralEigenvalue d i ^ 2),
    sharpQutritCentralEigenvalue_sum_sq]

/-- Trace zero and the actual spectral order put the middle absolute value
below both extremes; the extremes are the largest two central singular weights. -/
theorem sharpQutritCentralOrdered_middle_abs_le (d : Fin 3 → ℝ) :
    |sharpQutritCentralOrdered d 1| ≤ |sharpQutritCentralOrdered d 0| ∧
      |sharpQutritCentralOrdered d 1| ≤ |sharpQutritCentralOrdered d 2| := by
  have hs := sharpQutritCentralOrdered_sum d
  simp only [Fin.sum_univ_three] at hs
  have h01 := sharpQutritCentralOrdered_antitone d (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := sharpQutritCentralOrdered_antitone d (show (1 : Fin 3) ≤ 2 by decide)
  have h0 : 0 ≤ sharpQutritCentralOrdered d 0 := by linarith
  have h2 : sharpQutritCentralOrdered d 2 ≤ 0 := by linarith
  constructor
  · rw [abs_of_nonneg h0]
    exact abs_le.mpr ⟨by linarith, h01⟩
  · rw [abs_of_nonpos h2]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The two extreme squares lose exactly the square of the actual middle
eigenvalue from twice the original squared coefficient norm. -/
theorem sharpQutritCentralOrdered_extreme_deficit (d : Fin 3 → ℝ) :
    sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 =
      2 * (∑ i, d i ^ 2) - sharpQutritCentralOrdered d 1 ^ 2 := by
  have h := sharpQutritCentralOrdered_sum_sq d
  simp only [Fin.sum_univ_three] at h ⊢
  linarith

theorem sharpQutritCentralOrdered_extreme_bound (d : Fin 3 → ℝ) :
    sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 ≤
      2 * ∑ i, d i ^ 2 := by
  rw [sharpQutritCentralOrdered_extreme_deficit]
  linarith [sq_nonneg (sharpQutritCentralOrdered d 1)]

/-- Equality in the central extreme-square bound is exactly a zero middle
eigenvalue, including every degenerate or zero-coefficient case. -/
theorem sharpQutritCentralOrdered_extreme_eq_iff (d : Fin 3 → ℝ) :
    sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 =
      2 * (∑ i, d i ^ 2) ↔ sharpQutritCentralOrdered d 1 = 0 := by
  rw [sharpQutritCentralOrdered_extreme_deficit]
  constructor
  · intro h
    have hz : sharpQutritCentralOrdered d 1 ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hz
  · intro h
    simp [h]

/-- Central saturation forces a zero original coefficient, after transporting
the actual middle eigenvalue through the explicit spectral reindexing. -/
theorem sharpQutritCentralOrdered_extreme_eq_forces_coefficient_zero
    (d : Fin 3 → ℝ)
    (h : sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 =
      2 * ∑ i, d i ^ 2) : d 0 = 0 ∨ d 1 = 0 ∨ d 2 = 0 := by
  obtain ⟨e, he⟩ := sharpQutritCentralOrdered_reindex d
  have hm := (sharpQutritCentralOrdered_extreme_eq_iff d).mp h
  rw [he] at hm
  exact sharpQutritCentralEigenvalue_zero_forces_coefficient_zero d (e 1) hm

end ThreeCopyQutritWerner
