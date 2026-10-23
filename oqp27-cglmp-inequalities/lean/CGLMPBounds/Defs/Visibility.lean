module

public import CGLMPBounds.Defs.Scenario

@[expose] public section


/-!
# Critical visibility under uniform noise (definition)

Appendix B of the manuscript: `v_crit(q) = max {v ∈ [0,1] : v q + (1 - v) u_d ∈ C_d}`; smaller
visibility means greater white-noise resistance. We define it as the supremum of the same set
(the two agree whenever the maximum exists). This file contains definitions only.
-/

namespace CGLMPBounds

noncomputable section

/-- Global critical visibility of a table under uniform noise:
the supremum of the visibilities `v ∈ [0,1]` at which `v q + (1 - v) u` is Bell-local. -/
def critVisibility {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (q : Table α β) : ℝ :=
  sSup {v : ℝ | 0 ≤ v ∧ v ≤ 1 ∧ noisy v q ∈ localSet α β}

end

end CGLMPBounds
