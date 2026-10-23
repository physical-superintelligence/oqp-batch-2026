module

public import VacuumBellSeparation.Gaussian.ThermalPowers

@[expose] public section


/-!
# Actual CFC thermal power divided by its actual trace

This construction is separated from its later specification proofs.
-/

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

noncomputable def normalizedThermalPower (q τ : ℝ) :
    OscillatorSpace →L[ℂ] OscillatorSpace :=
  (positiveTrace (thermalDensity q ^ τ)).toReal⁻¹ • (thermalDensity q ^ τ)


end VacuumBellSeparation.Gaussian
