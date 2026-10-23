module

public import VacuumBellSeparation.FreeField.EvolutionPointwiseDerivative

@[expose] public section


/-! # The literal Cauchy solution satisfies the massive equation pointwise -/

namespace VacuumBellSeparation

set_option maxHeartbeats 1600000 in
theorem hasDerivAt_massiveSchwartzCauchyVelocity_pointwise {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzCauchyVelocity m s f g x)
      (-(massiveSchwartzPower m 2 (massiveSchwartzCauchy m t f g)) x) t := by
  have hp := (hasDerivAt_massiveSchwartzEvolution_pointwise m t
    (massiveSchwartzPower m 1 (cauchyPositiveData m f g)) x).const_mul Complex.I
  have hn := (hasDerivAt_massiveSchwartzEvolution_neg_pointwise m t
    (massiveSchwartzPower m 1 (cauchyNegativeData m f g)) x).const_mul Complex.I
  have h := hp.sub hn
  simpa only [massiveSchwartzCauchyVelocity, SchwartzMap.sub_apply,
    SchwartzMap.smul_apply, SchwartzMap.neg_apply, Pi.sub_def, Pi.add_def, Pi.neg_def, Pi.add_apply, Pi.neg_apply, smul_eq_mul, ← mul_assoc, Complex.I_mul_I,
    neg_one_mul, mul_neg, neg_neg, massiveSchwartzPower_add hm,
    show (1 : ℝ) + 1 = 2 by norm_num, massiveSchwartzEvolution_commute_power,
    massiveSchwartzCauchy_eq_phases, map_add, SchwartzMap.add_apply,
    neg_add_rev, sub_eq_add_neg, add_comm] using h

open Laplacian in
theorem hasDerivAt_massiveSchwartzCauchy_pointwise_kleinGordon {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzCauchyVelocity m s f g x)
      ((Δ (massiveSchwartzCauchy m t f g)) x -
        (m ^ 2 : ℂ) * massiveSchwartzCauchy m t f g x) t := by
  simpa only [massiveSchwartzPower_two hm, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
    smul_eq_mul, Complex.ofReal_pow, neg_sub] using
    hasDerivAt_massiveSchwartzCauchyVelocity_pointwise hm t f g x

end VacuumBellSeparation
