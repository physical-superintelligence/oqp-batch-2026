module

public import CGLMPBounds.Hardy.RootContinuity

@[expose] public section


/-!
# Continuity of the literal trace density in Lemma C.3

This specializes continuity of a symmetric characteristic-root sum to |Im z|.
No continuous choice of eigenvalues, diagonalization, or root-continuity oracle
is assumed. Hermiticity and invertibility are not needed for this particular
property: for fixed H the totalized inverse H⁻¹ is simply a constant matrix.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuous_traceDensity (H Y : Matrix ι ι ℂ) :
    Continuous (traceDensity H Y) := by
  have hp : Continuous (fun y : ℝ => traceDensityPencil H Y (y : ℂ)) := by
    unfold traceDensityPencil
    fun_prop
  have hf : Continuous (fun z : ℂ => |z.im|) := by fun_prop
  have hs := (continuous_charpoly_root_sum (ι := ι) (fun z : ℂ => |z.im|) hf).comp hp
  exact hs.div_const (2 * Real.pi * Fintype.card ι)

end
end CGLMPBounds.Hardy
