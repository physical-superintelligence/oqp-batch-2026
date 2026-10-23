module

public import VacuumBellSeparation.FreeField.LiteralFockVacuumNorm
public import VacuumBellSeparation.Fock.PhysicalTestTotality
public import VacuumBellSeparation.FreeField.Uniqueness

@[expose] public section


/-!
# Construction of the original cyclic free-field vacuum on literal Fock space

This construction is separated from its later specification proofs.
-/

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

-- Reuse the already sealed native completed-Fock instance at this literal carrier.
local instance literalFockConstructionComplete (m : ℝ) :
    CompleteSpace (LiteralFockSpace (m := m)) :=
  physicalTotalityFockComplete (Lp ℂ 2 (oneParticleMeasure m))

variable {m : ℝ} (hm : 0 < m)

theorem literalFockWeyl_vacuum (v : Lp ℂ 2 (oneParticleMeasure m)) :
    fockWeyl _ v (literalFockVacuumVector (m := m)) = coherentVector _ v := by
  rw [literalFockVacuumVector, fockWeyl_coherentVector,
    weylPhase_zero_right _ (fun _ _ => rfl), one_smul, add_zero]

set_option maxHeartbeats 2000000 in
/-- The original field's actual cyclic vacuum system on literal Fock space. -/
def literalFockVacuum : FreeFieldVacuum m (LiteralFockSpace (m := m)) where
  weyl F := fockWeyl _ (oneParticleL2 hm F)
  vacuum := literalFockVacuumVector
  weyl_mem_unitary F := fockWeyl_mem_unitary _ _
  weyl_mul F G := by
    rw [fockWeyl_mul, ← oneParticleL2_add, weylPhase]
    simp only [id_eq, inner_oneParticleL2]
  vacuum_norm := literalFockVacuumVector_norm
  vacuum_weyl F := by
    rw [literalFockWeyl_vacuum, literalFockVacuumVector, inner_coherentVector,
      ← inner_weylVec, inner_weylVec_zero_left _ (fun _ _ => rfl)]
    simp only [id_eq, norm_oneParticleL2_sq]
  cyclic := by
    have h : (fun F : RealTestFunction => fockWeyl _ (oneParticleL2 hm F)
        (literalFockVacuumVector (m := m))) =
        fun F => coherentVector _ (oneParticleL2 hm F) :=
      funext fun F => literalFockWeyl_vacuum _
    rw [h]
    exact physical_coherentVector_dense_span hm


end VacuumBellSeparation
