module

public import CausalNonpurifiability.Linear.Indices

@[expose] public section


/-! Operator norm vocabulary shared by statements and the separate norm-bound proof. The original definition and fully qualified name are retained. -/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

namespace CausalNonpurifiability

noncomputable section

variable {ι : Type}

/-- Operator norm of a matrix: the operator norm of the bounded operator it induces on
`EuclideanSpace ℂ ι` (the `ℓ²` norm on vectors). -/
noncomputable def opNorm [Fintype ι] [DecidableEq ι] (H : Op ι) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) H‖

end
end CausalNonpurifiability
