module

public import CausalNonpurifiability.Definitions.PortsSwapCore

@[expose] public section


/-! Literal laboratory-index and process swaps, without their symmetry theorem provider. -/

set_option autoImplicit false
namespace CausalNonpurifiability
noncomputable section
variable (D : Ports)

/-- `((a,o),(b,t)) ↦ ((b,t),(a,o))`: laboratory indices of `D` and of `D.swap`. -/
def swapLab : LabIndex D ≃ LabIndex D.swap where
  toFun x := (x.2, x.1)
  invFun y := (y.2, y.1)
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl


/-- The swapped process matrix `swapP W = reindex swapLab swapLab W`. -/
def swapP (W : PMat D) : PMat D.swap := Matrix.reindex (swapLab D) (swapLab D) W


end
end CausalNonpurifiability
