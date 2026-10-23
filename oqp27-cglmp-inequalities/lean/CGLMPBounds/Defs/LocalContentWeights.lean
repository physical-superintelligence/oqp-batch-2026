module

public import Mathlib

@[expose] public section


/-! Literal scalar root and Hilbert-space weights in (F.11)–(F.12).
The formulas retain totalized division; properties are proved in separate modules. -/
namespace CGLMPBounds
noncomputable section
open Finset

/-- The smaller root `(w - √(w² - 4k²))/2` of `h² - w h + k² = 0`. -/
def lowRoot (w k : ℝ) : ℝ := (w - Real.sqrt (w ^ 2 - 4 * k ^ 2)) / 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- `t^y_{acb} = |⟨u^y_{ab}, v^y_{cb}⟩|² / max(‖u^y_{ab}‖², ‖v^y_{cb}‖²)`, with `0/0 = 0`. -/
def tWeight (u v : Fin 2 → α → β → E) (y : Fin 2) (a c : α) (b : β) : ℝ :=
  ‖inner ℂ (u y a b) (v y c b)‖ ^ 2 / max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2)

/-- `T_y = Σ_b t^y_{acb}`. -/
def tTotal (u v : Fin 2 → α → β → E) (y : Fin 2) (a c : α) : ℝ :=
  ∑ b, tWeight u v y a c b

end
end CGLMPBounds
