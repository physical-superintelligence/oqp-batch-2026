module

public import CGLMPBounds.Statistics.Ceiling
public import CGLMPBounds.Fourier.LemmaF1

@[expose] public section


/-!
# Statistical strength of the Fourier-phase behaviour (equation (F.15)) and absent contexts

Supplement, Appendix F.5: "From (F.2) and (F.8), `S_μ(Q_d) ≤ (1 - a_d) Ξ(μ)`,
`sup_μ S_μ(Q_d) < (16/25) log₂(4/3)`." Appendix F.4, after (F.13): "If a context is absent, [...]
every no-signalling behaviour has zero strength on the sampled data."

* `statStrength_fourierTable_le` : `S_μ(Q_d) ≤ (1 - a_d) Ξ(μ)` (the local part `a_d L_d` of (F.2));
* `iSup_statStrength_fourierTable_lt` : `sup_μ S_μ(Q_d) ≤ (1 - a_d) log₂(4/3) < (16/25) log₂(4/3)`,
  from `Ξ(μ) ≤ log₂(4/3)` and `a_d ≥ 32/(9π²) > 9/25`;
* `statStrength_eq_zero_of_absent` : `S_μ(q) = 0` if some input pair has probability zero.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

/-- If some input pair is absent, every no-signalling behaviour has zero statistical strength
(Theorem F.2: `S_μ(q) ≤ Ξ(μ) = 0`). -/
theorem statStrength_eq_zero_of_absent {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] {q : Table α β} (hq : IsNoSignalling q) {μ : Fin 2 → Fin 2 → ℝ}
    (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) {x₀ y₀ : Fin 2} (h0 : μ x₀ y₀ = 0) :
    statStrength μ q = 0 := by
  have h := (statistical_ceiling_spec hq hμ hμ1).1.trans (statistical_ceiling_spec hq hμ hμ1).2
  rw [xiMin_eq_zero_of_absent h0] at h
  exact le_antisymm h zero_le

variable (d : ℕ) [NeZero d]

/-- (F.15), first part: `S_μ(Q_d) ≤ (1 - a_d) Ξ(μ)` for every weight `μ ≥ 0`. -/
theorem statStrength_fourierTable_le (hd : 2 ≤ d) {μ : Fin 2 → Fin 2 → ℝ}
    (hμ : ∀ x y, 0 ≤ μ x y) :
    statStrength μ (fourierTable d) ≤ ENNReal.ofReal (1 - localWeight d) * xiMin μ :=
  statStrength_le_of_local (fourierTable_isNoSignalling d) hμ
    (by linarith [localWeight_gt d hd]) (localComponent_mem_localSet d)
    (localWeight_mul_localComponent_le_fourierTable d hd)

/-- (F.15), second part: over input laws `μ`, `sup_μ S_μ(Q_d) < (16/25) log₂(4/3)`. -/
theorem iSup_statStrength_fourierTable_lt (hd : 2 ≤ d) :
    (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
        statStrength μ (fourierTable d)) < ENNReal.ofReal (16 / 25 * cKL) := by
  have ha : 9 / 25 < localWeight d := lt_localWeight_lower.trans_le (localWeight_ge d hd)
  have h1a : 0 ≤ 1 - localWeight d := by linarith [localWeight_le d hd]
  have hle : (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
      statStrength μ (fourierTable d)) ≤ ENNReal.ofReal ((1 - localWeight d) * cKL) := by
    refine iSup₂_le (fun μ hμ => ?_)
    rw [ENNReal.ofReal_mul h1a]
    exact (statStrength_fourierTable_le d hd hμ.1).trans
      (mul_le_mul_of_nonneg_left (xiMin_le_cKL hμ.1 hμ.2) zero_le)
  refine hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) cKL_pos)).mpr ?_)
  exact mul_lt_mul_of_pos_right (by linarith) cKL_pos

end

end CGLMPBounds
