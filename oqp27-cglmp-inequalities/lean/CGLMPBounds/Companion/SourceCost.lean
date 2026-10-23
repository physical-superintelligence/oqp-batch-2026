module

public import CGLMPBounds.Companion.Representation
public import CGLMPBounds.Companion.Correlations
public import CGLMPBounds.Companion.CycleValue

@[expose] public section


/-!
# Comparing the original strategy with the extracted tuple's one-edge cost

The coordinate swap preserves both trace and dimension. It therefore transports
the proved clock average `S_d/4` into the physical coordinates used by the Fourier
representation. This connects the actual tuple's scalar formula to the original
strategy, without assuming a Bell-value identity.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

lemma clockReindex_trace
    (X : Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ) :
    Matrix.trace (clockReindex X) = Matrix.trace X := by
  exact Fintype.sum_equiv (clockOutcomeEquiv (d := d) (n := n)).symm _ _ (fun _ => rfl)

lemma meanTraceReal_clockReindex
    (X : Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ) :
    meanTraceReal (clockReindex X) = meanTraceReal X := by
  unfold meanTraceReal
  rw [clockReindex_trace, ← Fintype.card_congr (clockOutcomeEquiv (d := d) (n := n))]

lemma outcomeCost_clockReindex
    (A B : ZMod d → Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ) :
    outcomeCost (fun a => clockReindex (A a)) (fun b => clockReindex (B b)) =
      outcomeCost A B := by
  simp only [outcomeCost, ← map_mul, meanTraceReal_clockReindex]

/-- The actual reordered clock still has normalized one-edge cost `S_d/4`. -/
theorem sourceClock_cost_original (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    outcomeCost sourceComputational
        (fun b => sourceClock P hP * sourceComputational b * (sourceClock P hP)ᴴ) =
      cglmpS d (tracialTable ![P 0, P 2] ![P 1, P 3]) / 4 := by
  calc
    _ = outcomeCost (fun a => clockReindex (clockLift (computational (n := n) a)))
        (fun b => clockReindex (companionClock P hP * clockLift (computational b) *
          (companionClock P hP)ᴴ)) := by
      simp only [map_mul, clockReindex_star, clockReindex_computational, sourceClock]
    _ = outcomeCost (fun a => clockLift (computational (n := n) a))
        (fun b => companionClock P hP * clockLift (computational b) *
          (companionClock P hP)ᴴ) := outcomeCost_clockReindex _ _
    _ = _ := companionClock_cost_cglmpS P hP

/-- Insert the extracted tuple into the scalar one-edge formula for the original strategy. -/
theorem original_residual_sum_eq_formula (hn : 1 ≤ n)
    (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t))
    (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ)
    (hclock : sourceClock P hP = tupleClock V) :
    cglmpS d (tracialTable ![P 0, P 2] ![P 1, P 3]) / 4 =
      ((d : ℝ) - 1) / 2 - (1 / (2 * (d : ℝ))) *
        ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range k,
          pairedCorrelation d j k (unitaryCorrelation (extendUnitary V) j k) := by
  letI : NeZero n := ⟨by omega⟩
  have hsource := sourceClock_cost_original P hP
  rw [hclock] at hsource
  calc
    _ = outcomeCost sourceComputational
        (fun b => tupleClock V * sourceComputational b * (tupleClock V)ᴴ) := hsource.symm
    _ = _ := unitary_tuple_outcomeCost V

end
end CGLMPBounds.Companion
