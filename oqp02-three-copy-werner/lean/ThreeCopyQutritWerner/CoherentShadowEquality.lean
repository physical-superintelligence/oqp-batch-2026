module

public import ThreeCopyQutritWerner.BalancedSingularGap

@[expose] public section


/-!
# Zero energy saturates the actual coherent-shadow chain

The same constructed balanced factors satisfy the equal-reserve and geometric
saturation conditions at every phase. Turning zero positive-source reserve into
common physical thinness still requires the independent rigidity theorem.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Each nonnegative term of the scalar shadow floor vanishes at zero energy. -/
theorem coherentShadow_zero_parts
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hq : endpointEnergy (X * Yᴴ) = 0) :
    2 * invN (X * Yᴴ) - frobSq X ^ 2 = 0 ∧
      zeroReserve (X * Xᴴ) = zeroReserve (Y * Yᴴ) ∧
      2 * jointShadowMarginalDefect X Y - invB (X * Xᴴ - Y * Yᴴ) = 0 := by
  have h := coherentShadow_scalar_floor X Y hn hG κ hκ
  rw [hq] at h
  have hg := coherentShadow_gap_nonneg X Y hG
  have hs := jointShadow_logical_slack_nonneg X Y
  have hsq := sq_nonneg (Real.sqrt (zeroReserve (X * Xᴴ)) -
    Real.sqrt (zeroReserve (Y * Yᴴ)))
  have hg0 : 2 * invN (X * Yᴴ) - frobSq X ^ 2 = 0 := by linarith
  have hs0 : 2 * jointShadowMarginalDefect X Y - invB (X * Xᴴ - Y * Yᴴ) = 0 := by
    linarith
  have hrts : Real.sqrt (zeroReserve (X * Xᴴ)) =
      Real.sqrt (zeroReserve (Y * Yᴴ)) := by nlinarith
  have hx : 0 ≤ zeroReserve (X * Xᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg X 0 0 hn
  have hy : 0 ≤ zeroReserve (Y * Yᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg Y 0 0 hn
  have heq : zeroReserve (X * Xᴴ) = zeroReserve (Y * Yᴴ) := by
    calc
      _ = (Real.sqrt (zeroReserve (X * Xᴴ))) ^ 2 := (Real.sq_sqrt hx).symm
      _ = (Real.sqrt (zeroReserve (Y * Yᴴ))) ^ 2 := by rw [hrts]
      _ = _ := Real.sq_sqrt hy
  exact ⟨hg0, heq, hs0⟩

/-- Both original lower bounds vanish, not just their weighted average. -/
theorem coherentShadow_zero_bounds
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hq : endpointEnergy (X * Yᴴ) = 0) :
    coherentShadowP X Y = 0 ∧ jointShadowLowerBound X Y = 0 := by
  obtain ⟨hg, heq, hs⟩ := coherentShadow_zero_parts X Y hn hG κ hκ hq
  have hc := coherentShadow_scalar_overlap_cancel X Y κ hκ
  have hf : coherentShadowFloor X Y = 0 := by
    unfold coherentShadowFloor
    rw [hg, heq, hs]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add, add_zero]
    linarith
  have hp : coherentShadowP X Y ≤ endpointEnergy (X * Yᴴ) :=
    coherentEndpoint_lower_bound X Y hn
  have hj := jointShadow_lower_bound X Y hG
  have hw := coherentShadow_weighted_identity X Y hn hG
  rw [hq] at hp hj
  rw [hf] at hw
  constructor <;> linarith

/-- Every unit phase of the same actual coherent source has zero reserve. -/
theorem coherentShadow_zero_unit_phases
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hq : endpointEnergy (X * Yᴴ) = 0) (z : ℂ) (hz : Complex.normSq z = 1) :
    zeroReserve (coherentPositiveSource X Y z) = 0 := by
  have heq := (coherentShadow_zero_parts X Y hn hG κ hκ hq).2.1
  have hp := (coherentShadow_zero_bounds X Y hn hG κ hκ hq).1
  have hr := zeroReserve_eq_endpoint (X * Yᴴ)
  rw [hq] at hr
  unfold coherentShadowP at hp
  have hsat : coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) + zeroReserve (X * Yᴴ) =
      -Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ)) := by linarith
  exact coherentPositiveSource_reserve_zero_of_saturation X Y hn heq hsat z hz

/-- The shadow projection itself vanishes in squared norm at such a zero. -/
theorem coherentShadow_zero_projection_norm
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hq : endpointEnergy (X * Yᴴ) = 0) :
    vecNormSq (jointShadowProjection (jointShadowSourceTensor X Y)) = 0 := by
  have hj := (coherentShadow_zero_bounds X Y hn hG κ hκ hq).2
  have h := jointShadow_identity X Y hG
  rw [hq, hj] at h
  linarith

/-- The actual scalar-idempotent endpoint zero has zero singular gap. -/
theorem singularGapSq_eq_zero_of_scalar_square_zero
    (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (κ : ℂ) (hκ : C * C = κ • C)
    (hq : endpointEnergy C = 0) : singularGapSq C = 0 := by
  have hn : 2 ≤ Fintype.card (a × b × c) := by
    simpa only [hr] using Matrix.rank_le_card_width C
  obtain ⟨X, Y, hC, hG, hXY⟩ := exists_balanced_scalar_factors C hr κ hκ
  rw [hC, singularGapSq_balanced_factors X Y hG]
  exact (coherentShadow_zero_parts X Y hn hG κ hXY (hC ▸ hq)).1

/-- The common coherent factors and all unit-phase equalities are constructed
from the original scalar-square zero, without phase-dependent factorizations. -/
theorem exists_balanced_coherent_zero_factors
    (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (κ : ℂ) (hκ : C * C = κ • C)
    (hq : endpointEnergy C = 0) :
    ∃ X Y : Matrix (a × b × c) (Fin 2) ℂ,
      C = X * Yᴴ ∧ Xᴴ * X = Yᴴ * Y ∧
        Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        ∀ z : ℂ, Complex.normSq z = 1 → zeroReserve (coherentPositiveSource X Y z) = 0 := by
  have hn : 2 ≤ Fintype.card (a × b × c) := by
    simpa only [hr] using Matrix.rank_le_card_width C
  obtain ⟨X, Y, hC, hG, hXY⟩ := exists_balanced_scalar_factors C hr κ hκ
  exact ⟨X, Y, hC, hG, hXY, coherentShadow_zero_unit_phases X Y hn hG κ hXY (hC ▸ hq)⟩

end ThreeCopyQutritWerner
