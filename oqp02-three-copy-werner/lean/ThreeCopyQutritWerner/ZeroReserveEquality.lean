module

public import ThreeCopyQutritWerner.ZeroReserveSign
public import ThreeCopyQutritWerner.ZeroReservePureEquality

@[expose] public section


/-!
# Necessary saturation conditions for a positive-source reserve zero

Every inequality in the proved reserve chain saturates when both spectral
weights are positive and the reserve is zero. This includes all three sharp
partial-trace bounds and exterior-transition bounds. These are necessary
equalities on the original contractions, not a classification of the branch
with strictly positive entropy at every site.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The middle quantity between the sharp partial-trace and exterior bounds. -/
def zeroReserveCutNuclearDefect (u v : a × b × c → ℂ) : Fin 3 → ℝ :=
  ![nuclearTrace (ptrace₁ (ketBra u v)) ^ 2 - frobSq (ptrace₁ (ketBra u v)),
    nuclearTrace (ptrace₂ (ketBra u v)) ^ 2 - frobSq (ptrace₂ (ketBra u v)),
    nuclearTrace (ptrace₃ (ketBra u v)) ^ 2 - frobSq (ptrace₃ (ketBra u v))]

theorem zeroReserveCutCross_le_nuclearDefect (u v : a × b × c → ℂ)
    (huv : braket u v = 0) (i : Fin 3) :
    zeroReserveCutCross u v i ≤ zeroReserveCutNuclearDefect u v i := by
  have h1 := nuclearTrace_partialTrace_bound_of_trace_zero (ptrace₁ (ketBra u v))
    (zeroReserveTransition_site1_trace_zero u v huv)
  have h2 := nuclearTrace_partialTrace_bound_of_trace_zero (ptrace₂ (ketBra u v))
    (zeroReserveTransition_site2_trace_zero u v huv)
  have h3 := nuclearTrace_partialTrace_bound_of_trace_zero (ptrace₃ (ketBra u v))
    (zeroReserveTransition_site3_trace_zero u v huv)
  rw [(zeroReserveTransition_site1_traces _).1, (zeroReserveTransition_site1_traces _).2] at h1
  rw [(zeroReserveTransition_site2_traces _).1, (zeroReserveTransition_site2_traces _).2] at h2
  rw [(zeroReserveTransition_site3_traces _).1, (zeroReserveTransition_site3_traces _).2] at h3
  fin_cases i
  · change frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₁₃ (ketBra u v)) -
      frobSq (ptrace₁ (ketBra u v)) ≤
        nuclearTrace (ptrace₁ (ketBra u v)) ^ 2 - frobSq (ptrace₁ (ketBra u v))
    linarith only [h1]
  · change frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
      frobSq (ptrace₂ (ketBra u v)) ≤
        nuclearTrace (ptrace₂ (ketBra u v)) ^ 2 - frobSq (ptrace₂ (ketBra u v))
    linarith only [h2]
  · change frobSq (ptrace₁₃ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
      frobSq (ptrace₃ (ketBra u v)) ≤
        nuclearTrace (ptrace₃ (ketBra u v)) ^ 2 - frobSq (ptrace₃ (ketBra u v))
    linarith only [h3]

theorem zeroReserveCutNuclearDefect_le (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (i : Fin 3) :
    zeroReserveCutNuclearDefect u v i ≤
      Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i) := by
  fin_cases i
  · exact zeroReserveTransition_site1 u v hu hv
  · exact zeroReserveTransition_site2 u v hu hv
  · exact zeroReserveTransition_site3 u v hu hv

/-- With positive spectral weights, reserve zero is exactly weighted entropy
balance together with equality in the sharp total cross bound. -/
theorem zeroReserve_two_ray_eq_zero_iff (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0 ↔
      lam * Real.sqrt (zeroReserveLocalEntropy u) =
        mu * Real.sqrt (zeroReserveLocalEntropy v) ∧
      2 * invB (ketBra u v) - invA (ketBra u v) =
        Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v) := by
  have he := zeroReserve_two_ray_square_identity u v hu hv huv lam mu
  have hgap := sub_nonneg.mpr (zeroReserve_sharp_cross_bound u v hu hv huv)
  have hc : 0 < 2 * lam * mu := mul_pos (mul_pos (by norm_num) hlam) hmu
  constructor
  · intro hz
    rw [hz, mul_zero] at he
    have hs : (lam * Real.sqrt (zeroReserveLocalEntropy u) -
        mu * Real.sqrt (zeroReserveLocalEntropy v)) ^ 2 = 0 := by
      nlinarith [mul_nonneg hc.le hgap]
    have hg : Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v) -
        (2 * invB (ketBra u v) - invA (ketBra u v)) = 0 := by
      nlinarith [sq_nonneg (lam * Real.sqrt (zeroReserveLocalEntropy u) -
        mu * Real.sqrt (zeroReserveLocalEntropy v))]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hs), (sub_eq_zero.mp hg).symm⟩
  · rintro ⟨hs, hg⟩
    rw [hs, hg] at he
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] at he
    linarith only [he]

/-- Equality in the total cross bound forces every cut bound and the final
finite Cauchy inequality to be equalities. -/
theorem zeroReserve_cross_eq_saturates (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (hcross : 2 * invB (ketBra u v) - invA (ketBra u v) =
      Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v)) :
    (∀ i, zeroReserveCutCross u v i =
      Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i)) ∧
    (∑ i, Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i)) =
      Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v) := by
  have hle := zeroReserve_sum_sqrt_mul_le (zeroReserveLocalDeficit u)
    (zeroReserveLocalDeficit v) (zeroReserveLocalDeficit_nonneg u hu)
    (zeroReserveLocalDeficit_nonneg v hv)
  rw [zeroReserveLocalDeficit_sum, zeroReserveLocalDeficit_sum] at hle
  have hsum : (∑ i, zeroReserveCutCross u v i) ≤
      ∑ i, Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i) :=
    Finset.sum_le_sum fun i _ => zeroReserveCutCross_le u v hu hv huv i
  rw [zeroReserveCutCross_sum, hcross] at hsum
  have heq := le_antisymm hle hsum
  have hz : (∑ i, (Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i) -
      zeroReserveCutCross u v i)) = 0 := by
    rw [Finset.sum_sub_distrib, heq, zeroReserveCutCross_sum, hcross, sub_self]
  have hi := (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.mpr (zeroReserveCutCross_le u v hu hv huv i))).mp hz
  exact ⟨fun i => (sub_eq_zero.mp (congrFun hi i)).symm, heq⟩

/-- Every reduced transition at a reserve zero saturates both of its analytic
bounds, and the entropy square-root vectors have all two-coordinate minors zero. -/
theorem zeroReserve_two_ray_eq_zero_saturates (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0) :
    (∀ i, zeroReserveCutCross u v i = zeroReserveCutNuclearDefect u v i ∧
      zeroReserveCutNuclearDefect u v i =
        Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i)) ∧
    (∀ i j, Real.sqrt (zeroReserveLocalDeficit u i) * Real.sqrt (zeroReserveLocalDeficit v j) =
      Real.sqrt (zeroReserveLocalDeficit u j) * Real.sqrt (zeroReserveLocalDeficit v i)) := by
  obtain ⟨_, hcross⟩ := (zeroReserve_two_ray_eq_zero_iff u v hu hv huv lam mu hlam hmu).mp hz
  obtain ⟨hi, hs⟩ := zeroReserve_cross_eq_saturates u v hu hv huv hcross
  constructor
  · intro i
    have hleft := zeroReserveCutCross_le_nuclearDefect u v huv i
    have hright := zeroReserveCutNuclearDefect_le u v hu hv i
    constructor <;> linarith [hi i]
  · apply (zeroReserve_sum_sqrt_mul_eq_iff _ _
      (zeroReserveLocalDeficit_nonneg u hu) (zeroReserveLocalDeficit_nonneg v hv)).mp
    simpa only [zeroReserveLocalDeficit_sum] using hs

/-- Reserve equality balances the weighted square-root entropy at each site,
including degenerate entropy vectors. -/
theorem zeroReserve_two_ray_eq_zero_local_balance (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0) :
    ∀ i, lam * Real.sqrt (zeroReserveLocalDeficit u i) =
      mu * Real.sqrt (zeroReserveLocalDeficit v i) := by
  obtain ⟨_, hcross⟩ := (zeroReserve_two_ray_eq_zero_iff u v hu hv huv lam mu hlam hmu).mp hz
  obtain ⟨hcuts, _⟩ := zeroReserve_cross_eq_saturates u v hu hv huv hcross
  have he := zeroReserve_two_ray_expansion u v hu hv huv lam mu
  have hterm (i : Fin 3) :
      (lam * Real.sqrt (zeroReserveLocalDeficit u i) -
        mu * Real.sqrt (zeroReserveLocalDeficit v i)) ^ 2 =
      lam ^ 2 * zeroReserveLocalDeficit u i + mu ^ 2 * zeroReserveLocalDeficit v i -
        2 * lam * mu * zeroReserveCutCross u v i := by
    rw [hcuts i, Real.sqrt_mul (zeroReserveLocalDeficit_nonneg u hu i)]
    calc
      _ = lam ^ 2 * Real.sqrt (zeroReserveLocalDeficit u i) ^ 2 +
          mu ^ 2 * Real.sqrt (zeroReserveLocalDeficit v i) ^ 2 -
          2 * lam * mu * (Real.sqrt (zeroReserveLocalDeficit u i) *
            Real.sqrt (zeroReserveLocalDeficit v i)) := by ring
      _ = _ := by rw [Real.sq_sqrt (zeroReserveLocalDeficit_nonneg u hu i),
        Real.sq_sqrt (zeroReserveLocalDeficit_nonneg v hv i)]
  have hsum : (∑ i, (lam * Real.sqrt (zeroReserveLocalDeficit u i) -
      mu * Real.sqrt (zeroReserveLocalDeficit v i)) ^ 2) = 0 := by
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      zeroReserveLocalDeficit_sum, zeroReserveLocalDeficit_sum,
      zeroReserveCutCross_sum, ← he, hz, mul_zero]
  intro i
  have hi := (Fintype.sum_eq_zero_iff_of_nonneg
    (fun j => sq_nonneg (lam * Real.sqrt (zeroReserveLocalDeficit u j) -
      mu * Real.sqrt (zeroReserveLocalDeficit v j)))).mp hsum
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (congrFun hi i))

/-- A zero local entropy is shared by both rays of a positive-weight reserve zero. -/
theorem zeroReserve_two_ray_eq_zero_deficit_zero_iff (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (i : Fin 3) : zeroReserveLocalDeficit u i = 0 ↔ zeroReserveLocalDeficit v i = 0 := by
  have hb := zeroReserve_two_ray_eq_zero_local_balance u v hu hv huv lam mu hlam hmu hz i
  constructor
  · intro h
    rw [h, Real.sqrt_zero, mul_zero] at hb
    have hs : Real.sqrt (zeroReserveLocalDeficit v i) = 0 :=
      (mul_eq_zero.mp hb.symm).resolve_left (ne_of_gt hmu)
    nlinarith [Real.sq_sqrt (zeroReserveLocalDeficit_nonneg v hv i)]
  · intro h
    rw [h, Real.sqrt_zero, mul_zero] at hb
    have hs : Real.sqrt (zeroReserveLocalDeficit u i) = 0 :=
      (mul_eq_zero.mp hb).resolve_left (ne_of_gt hlam)
    nlinarith [Real.sq_sqrt (zeroReserveLocalDeficit_nonneg u hu i)]

/-- The shared zero-entropy branch implies the actual thin local range at site 1. -/
theorem zeroReserve_two_ray_eq_zero_thin_site1 (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (he : zeroReserveLocalDeficit u 0 = 0) :
    localRangeDim₁ ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) ≤ 2 := by
  have hv0 := (zeroReserve_two_ray_eq_zero_deficit_zero_iff
    u v hu hv huv lam mu hlam hmu hz 0).mp he
  apply zeroReserve_localRange1_le_two_of_local_purity_one u v hu hv
  · change 1 - frobSq (ptrace₂₃ (ketBra u u)) = 0 at he
    linarith
  · change 1 - frobSq (ptrace₂₃ (ketBra v v)) = 0 at hv0
    linarith

end ThreeCopyQutritWerner
