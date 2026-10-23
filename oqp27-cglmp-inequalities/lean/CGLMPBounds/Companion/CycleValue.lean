module

public import CGLMPBounds.Companion.TransitionCost

@[expose] public section


/-!
# The oriented cycle is the CGLMP residual sum

In cyclic order the PVMs are `A₀, B₀, A₁, B₁`. The closing edge has the
shifted family `P⁰_(b−1)`, which becomes the residual `[b−a−1]_d` after
relabeling and cyclically exchanging the trace factors.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d n : ℕ} [NeZero d]

lemma meanTraceReal_mul_comm (A B : Matrix ι ι ℂ) :
    meanTraceReal (A * B) = meanTraceReal (B * A) := by
  unfold meanTraceReal
  rw [Matrix.trace_mul_comm]

lemma outcomeCost_reverse (P Q : ZMod d → Matrix ι ι ℂ) :
    outcomeCost P Q =
      ∑ a, ∑ b, ((b - a).val : ℝ) * meanTraceReal (Q a * P b) := by
  unfold outcomeCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [meanTraceReal_mul_comm]

lemma outcomeCost_closing (P Q : ZMod d → Matrix ι ι ℂ) :
    outcomeCost Q (fun b => P (b - 1)) =
      ∑ a, ∑ b, ((b - a - 1).val : ℝ) * meanTraceReal (P a * Q b) := by
  unfold outcomeCost
  calc
    (∑ a, ∑ b, ((a - b).val : ℝ) * meanTraceReal (Q a * P (b - 1))) =
        ∑ a, ∑ b, ((a - (b - 1) - 1).val : ℝ) *
          meanTraceReal (P (b - 1) * Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      have hres : a - b = a - (b - 1) - 1 := by abel
      rw [hres, meanTraceReal_mul_comm]
    _ = ∑ a, ∑ b, ((a - b - 1).val : ℝ) * meanTraceReal (P b * Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ (fun _ => rfl)
    _ = _ := by rw [Finset.sum_comm]

/-- Cyclic order `A₀,B₀,A₁,B₁` reproduces all four residual conventions in (B.1). -/
theorem cycleCost_eq_cglmpS (P : Fin 4 → ZMod d → Base n) :
    cycleCost P = cglmpS d (tracialTable ![P 0, P 2] ![P 1, P 3]) := by
  rw [cycleCost, outcomeCost_reverse (P 1) (P 2), outcomeCost_closing (P 0) (P 3)]
  simp only [outcomeCost, meanTraceReal, Fintype.card_fin, cglmpS, Fin.sum_univ_two,
    tracialTable, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [residual]
  ring

/-- One companion-clock edge is exactly `S_d/4` for the original tracial strategy. -/
theorem companionClock_cost_cglmpS (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) :
    outcomeCost (fun a => clockLift (computational (n := n) a))
        (fun b => companionClock P hP * clockLift (computational b) *
          (companionClock P hP)ᴴ) =
      cglmpS d (tracialTable ![P 0, P 2] ![P 1, P 3]) / 4 := by
  rw [companionClock_cost_original, cycleCost_eq_cglmpS]

end
end CGLMPBounds.Companion
