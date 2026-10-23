module

public import CGLMPBounds.CGLMP.LocalBound

@[expose] public section


/-!
# Deterministic CGLMP₄ saturators

Supplement, proof of Proposition G.1: "A deterministic CGLMP_d saturator is specified by an anchor
outcome and four nonnegative residuals summing to `d − 1`. Its saturation count is `d·C(d+2, 3)`.
At `d = 4`, the counts 80 and 72 distinguish the two classes."

* `cglmpS_detTable` : on a deterministic table, `S_d` is the sum of the four residuals;
* `cglmp_four_detTable_eq_two_iff` : `I₄(q_s) = 2` iff the residuals of `s` sum to `3`;
* `cglmp_four_saturation_count_spec` : exactly `80 = 4·C(6, 3)` deterministic strategies attain
  `I₄ = 2`.
-/

namespace CGLMPBounds

open Finset

/-- On a deterministic table, `S_d` is the sum of the four oriented residuals. -/
theorem cglmpS_detTable (d : ℕ) [NeZero d] (s : Strategy (ZMod d) (ZMod d)) :
    cglmpS d (detTable s) = ((∑ x, ∑ y, residual d x y (s.1 x) (s.2 y) : ℕ) : ℝ) := by
  rw [cglmpS_eq_bell, bell_detTable]
  simp only [Nat.cast_sum]
  rfl

/-- `I₄(q_s) = 2` iff the four residuals of `s` sum to `3 = d - 1`. -/
theorem cglmp_four_detTable_eq_two_iff (s : Strategy (ZMod 4) (ZMod 4)) :
    cglmp 4 (detTable s) = 2 ↔ ∑ x, ∑ y, residual 4 x y (s.1 x) (s.2 y) = 3 := by
  unfold cglmp
  rw [cglmpS_detTable]
  have h4 : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
  rw [h4]
  constructor
  · intro h
    have h' : ((∑ x, ∑ y, residual 4 x y (s.1 x) (s.2 y) : ℕ) : ℝ) = 3 := by linarith
    exact_mod_cast h'
  · intro h
    rw [h]
    norm_num

/-- **The CGLMP₄ saturation count.** Exactly `80 = 4·C(6, 3)` deterministic strategies attain the
local bound `I₄ = 2`. -/
theorem cglmp_four_saturation_count_spec :
    (Finset.univ.filter (fun s : Strategy (ZMod 4) (ZMod 4) =>
      cglmp 4 (detTable s) = 2)).card = 80 ∧ 80 = 4 * Nat.choose 6 3 := by
  refine ⟨?_, by decide⟩
  rw [Finset.filter_congr (fun s _ => cglmp_four_detTable_eq_two_iff s)]
  decide +kernel

end CGLMPBounds
