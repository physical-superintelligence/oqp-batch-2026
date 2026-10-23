module

public import VacuumBellSeparation.Gaussian.CrossRankOneSeries

@[expose] public section


/-!
# Summability preserved by bounded regional maps and matrix elements
-/

namespace VacuumBellSeparation.Gaussian

variable {E F G H ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem summable_norm_product_map {u : ι → E} {v : ι → F}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) (R : E →L[ℂ] G) (S : F →L[ℂ] H) :
    Summable fun i => ‖R (u i)‖ * ‖S (v i)‖ := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (f := fun i => (‖R‖ * ‖S‖) * (‖u i‖ * ‖v i‖)) _ (hs.mul_left _)
  intro i
  calc
    _ ≤ (‖R‖ * ‖u i‖) * (‖S‖ * ‖v i‖) :=
      mul_le_mul (R.le_opNorm _) (S.le_opNorm _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem summable_inner_product {u : ι → E} {v : ι → F}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) (x : E) (y : F) :
    Summable fun i => inner ℂ x (u i) * inner ℂ (v i) y := by
  apply Summable.of_norm_bounded (hs.mul_left (‖x‖ * ‖y‖))
  intro i
  rw [norm_mul]
  calc
    _ ≤ (‖x‖ * ‖u i‖) * (‖v i‖ * ‖y‖) :=
      mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end VacuumBellSeparation.Gaussian
