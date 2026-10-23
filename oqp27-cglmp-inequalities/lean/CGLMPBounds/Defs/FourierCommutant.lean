module

public import CGLMPBounds.Defs.Fourier

@[expose] public section


/-!
# Actual Fourier basis matrices and transition (definitions only)

These are the original standard Fourier-phase vectors in matrix form and the
actual first-to-second basis transition used in supplement Appendix E.1.
The bodies are extracted verbatim from FourierCommutantStandard for independent
source-only review; no commutant or nonzero-entry assertion is assumed here.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds
noncomputable section

variable (d : ℕ) [NeZero d]

/-- Columns are the source vectors `ψ_(t,a)` with their original indexing. -/
def fourierBasisMatrix (t : ℕ) : Matrix (Fin d) (ZMod d) ℂ :=
  Matrix.of fun j a => fourierVector d t a j

/-- The next basis in the gauge where the first PVM is computational. -/
def fourierTransition : Matrix (ZMod d) (ZMod d) ℂ :=
  (fourierBasisMatrix d 0)ᴴ * fourierBasisMatrix d 1

end
end CGLMPBounds
