module

public import CausalNonpurifiability.Definitions.OrderedMarginalCore
public import CausalNonpurifiability.Definitions.Process

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.OrderedMarginal`

The operator `T̂ = Tr_{A_O} T / d` on `A_I B_I B_O`, which appears in Lemma 2.5
(`lem:ordered`, `eq:ordered-marginal`) for the order `B ≺ A` ("the lemma holds with the two
parties exchanged"). The operator for the order `A ≺ B` is `hatAB` (`Definitions/Process.lean`).
-/

set_option autoImplicit false

namespace CausalNonpurifiability

variable (D : Ports)

theorem hatBA_apply (T : PMat D) (a a' : Fin D.m) (b b' : Fin D.n) (t t' : Fin D.e) :
    hatBA D T (a, (b, t)) (a', (b', t')) =
      ((D.d : ℂ))⁻¹ * ∑ o, T ((a, o), (b, t)) ((a', o), (b', t')) := by
  simp only [hatBA, Matrix.smul_apply, smul_eq_mul, ptraceOut_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, eqAO_symm_apply]

end CausalNonpurifiability
