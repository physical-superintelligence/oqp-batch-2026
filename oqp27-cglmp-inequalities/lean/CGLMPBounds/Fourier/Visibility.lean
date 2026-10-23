module

public import CGLMPBounds.Fourier.LocalWeight
public import CGLMPBounds.Noise.HalfNoise

@[expose] public section


/-!
# Visibility bound from a local part of weight `a_d`

Skeleton of (F.3) in Lemma F.1: a table with a Bell-local part of weight `a_d` whose remainder
is half-noise local has `v_crit ≥ 1/(2 - a_d) > 3049/5000`. Applying it to the Fourier-phase
behaviour `Q_d` still requires `Q_d ≥ a_d L_d` and the uniform marginals of the remainder.
-/

namespace CGLMPBounds

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem lt_critVisibility_of_localWeight_part (d : ℕ) (hd : 2 ≤ d) {q L r : Table α β}
    (hL : L ∈ localSet α β)
    (hr : (1 / 2 : ℝ) • r + (1 / 2 : ℝ) • uniformTable α β ∈ localSet α β)
    (hq : q = localWeight d • L + (1 - localWeight d) • r) :
    (3049 : ℝ) / 5000 < critVisibility q :=
  lt_of_lt_of_le (visibility_bound d hd)
    (le_critVisibility_of_local_part ((localWeight_le d hd).trans (by norm_num))
      ((by norm_num : (0 : ℝ) ≤ 1098 / 3049).trans (localWeight_gt d hd).le) hL hr hq)

end

end CGLMPBounds
