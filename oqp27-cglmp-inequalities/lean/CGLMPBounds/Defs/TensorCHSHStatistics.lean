module

public import CGLMPBounds.Defs.Scenario
public import CGLMPBounds.Defs.TensorCHSH

@[expose] public section


/-! Literal tensor CHSH law and finite signed binomial tail. Definitions only.
The real-parameter formulas remain totalized; probability claims require their
explicit theorem hypotheses. -/

namespace CGLMPBounds.TensorCHSH
noncomputable section

/-- The CHSH error rate `r = (2 - √2)/4`. -/
def chshErrRate : ℝ := (2 - Real.sqrt 2) / 4

/-- The closed formula (F.5) with error rate `ρ`:
`(a,b|x,y) ↦ 2^{-m} (1-ρ)^{m-K_{xy}(a,b)} ρ^{K_{xy}(a,b)}`. `T_m` is `tensorTable m chshErrRate`. -/
def tensorTable (m : ℕ) (ρ : ℝ) : Table (Fin m → Bool) (Fin m → Bool) :=
  fun x y a b => (1 / 2 : ℝ) ^ m * ((1 - ρ) ^ (m - errCount x y a b) * ρ ^ errCount x y a b)

/-- `Pr{Bin(m, ρ) ≤ k} - Pr{Bin(m, ρ) ≥ h}`: the value of `G_{m,k}` on `tensorTable m ρ`. -/
def tailDiff (m k h : ℕ) (ρ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)
    * (((if j ≤ k then (1 : ℝ) else 0) - (if h ≤ j then (1 : ℝ) else 0))
      * ((1 - ρ) ^ (m - j) * ρ ^ j))

end
end CGLMPBounds.TensorCHSH
