module

public import CGLMPBounds.Defs.Visibility
public import CGLMPBounds.Scenario.Local

@[expose] public section


/-!
# Upper bounds on the critical visibility from a Bell witness

If a linear functional is bounded by `B` on the Bell-local set and its value on the noise mixture
at visibility `v₀` exceeds `B`, then `v_crit < v₀`. This is the argument used for the tensor-CHSH
bound in the proof of Theorem A.3 (Appendix F.2): `G_{M,k}(v₀ T_M + (1 - v₀) u) > 1/2`.
-/

namespace CGLMPBounds

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A Bell functional is affine along the noise line. -/
theorem bell_noisy (c q : Table α β) (v : ℝ) :
    bell c (noisy v q) = v * bell c q + (1 - v) * bell c (uniformTable α β) := by
  simp only [noisy, map_add, map_smul, smul_eq_mul]

variable [DecidableEq α] [DecidableEq β]

theorem critVisibility_le_one (q : Table α β) : critVisibility q ≤ 1 :=
  Real.sSup_le (fun _ hv => hv.2.1) zero_le_one

/-- Witness criterion: if `bell c ≤ B` on the local set and on the uniform table, and the noise
mixture at visibility `v₀ > 0` has `bell c > B`, then `v_crit(q) < v₀`. -/
theorem critVisibility_lt_of_witness {c q : Table α β} {B v₀ : ℝ}
    (hloc : ∀ p ∈ localSet α β, bell c p ≤ B) (hu : bell c (uniformTable α β) ≤ B)
    (hv₀ : 0 < v₀) (h : B < v₀ * bell c q + (1 - v₀) * bell c (uniformTable α β)) :
    critVisibility q < v₀ := by
  have hab : 0 < bell c q - bell c (uniformTable α β) := by
    by_contra hneg
    have hneg' : bell c q - bell c (uniformTable α β) ≤ 0 := not_lt.mp hneg
    have hprod : 0 ≤ v₀ * (bell c (uniformTable α β) - bell c q) :=
      mul_nonneg hv₀.le (by linarith)
    nlinarith [hprod, hu, h]
  have hbound : critVisibility q
      ≤ (B - bell c (uniformTable α β)) / (bell c q - bell c (uniformTable α β)) := by
    refine Real.sSup_le (fun v hv => ?_) (div_nonneg (sub_nonneg.mpr hu) hab.le)
    have hv' := hloc _ hv.2.2
    rw [bell_noisy] at hv'
    rw [le_div_iff₀ hab]
    nlinarith [hv']
  refine lt_of_le_of_lt hbound ?_
  rw [div_lt_iff₀ hab]
  nlinarith [h]

end

end CGLMPBounds
