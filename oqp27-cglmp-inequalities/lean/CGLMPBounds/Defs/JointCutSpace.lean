module

public import CGLMPBounds.Defs.FourthRootCut
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section


/-! The actual common scalar cut eigenspace from (E.1). -/

namespace CGLMPBounds.Circulation
noncomputable section

def fourthRootCutSpace {d r : ℕ} (V : Fin d → Mat r) (a : Fin 4) (j₀ : Fin d) :
    Submodule ℂ (EuclideanSpace ℂ (Fin r)) :=
  ⨅ j, Module.End.eigenspace (V j).toEuclideanLin
    (Complex.I ^ (fourthRootCutLabels a j₀ j).val)

end
end CGLMPBounds.Circulation
