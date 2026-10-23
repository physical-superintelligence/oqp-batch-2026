module

public import CGLMPBounds.Defs.CircularHilbert
public import CGLMPBounds.Defs.HardyMatrixPotential

@[expose] public section


/-! Actual Herglotz/Poisson extension in the C.6 proof. Circle measure is
normalized Haar measure. Every extension is an explicit Bochner integral;
no analyticity, boundary limit, mean identity or norm bound is a field. -/

namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory

/-- The holomorphic kernel with positive real part in the unit disk. -/
def circleHerglotzKernel (z : ℂ) (t : UnitCircle) : ℂ :=
  (fourier 1 t + z) / (fourier 1 t - z)

/-- The actual Poisson kernel, written as the real part of the Herglotz kernel. -/
def circlePoissonKernel (z : ℂ) (t : UnitCircle) : ℝ :=
  (circleHerglotzKernel z t).re

/-- The analytic matrix extension whose boundary is B+iHB for Hermitian B.
The finite-dimensional matrix Bochner integral is written entrywise so its
definition is independent of the chosen equivalent matrix norm. -/
def matrixPoissonAnalytic {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (z : ℂ) : Circulation.Mat r :=
  fun i j => ∫ t, circleHerglotzKernel z t * B t i j ∂circleMeasure

/-- Actual radial values, parametrized by the same unit circle as the boundary. -/
def matrixPoissonRadial {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (ρ : ℝ) (t : UnitCircle) : Circulation.Mat r :=
  matrixPoissonAnalytic B ((ρ : ℂ) * fourier 1 t)

end
end CGLMPBounds.Hardy
