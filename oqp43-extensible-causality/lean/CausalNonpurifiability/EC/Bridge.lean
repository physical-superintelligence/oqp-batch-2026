module

public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.Classical.Transport
public import CausalNonpurifiability.Certificates.Qubit
public import CausalNonpurifiability.EC.Rectangles

@[expose] public section


/-!
# `CausalNonpurifiability.EC.Bridge`

Whole-experiment decomposition: from rectangle bounds for every finite ancillary extension
to `HalfCausal`, hence `ExtensiblyCausal` (§5 entire, `eq:rectangle`, `eq:causal-components`).

`ec_of_rectangles` unfolds `ExtensiblyCausal`: validity gives normalized
nonnegative Born distributions (`valid_born_extended`), the rectangle bounds with
setting-local endpoint arrays of mass `1/2` give the transport decomposition
(`causal_of_rectangles`, i.e. `transport_of_rectangles` + `eq:causal-components`).
The endpoint arrays are existentially quantified per extension; `EC/Rectangles` supplies
them (`eq:endpoints`, `eq:rectangle`).

Manuscript anchors: §5, `eq:rectangle`, `eq:causal-components`, Oreshkov–Giarmatzi Def. 3.2.
-/

set_option autoImplicit false

open scoped Kronecker

namespace CausalNonpurifiability

/-- **Rectangle bounds for every finite extension give extensible causality.**
For a valid `W`, if for every shared ancilla `σ` (any finite dimensions `r+1`, `s+1`) and
every pair of extended instruments there are setting-local endpoint arrays `rA x`, `rB y`,
nonnegative, of mass `1/2`, dominating every outcome rectangle of the extended Born
distribution (`eq:rectangle`), then `W` is extensibly causal. -/
theorem ec_of_rectangles {D : Ports} {W : PMat D} (hW : Valid D W)
    (hrect : ∀ (r s nx ny na nb : ℕ) (σ : Op (Fin (r + 1) × Fin (s + 1))), Density σ →
      ∀ (M : Instrument (Fin D.m × Fin (r + 1)) (Fin D.d) (Fin (nx + 1)) (Fin (na + 1)))
        (N : Instrument (Fin D.n × Fin (s + 1)) (Fin D.e) (Fin (ny + 1)) (Fin (nb + 1))),
        ∃ (rA : Fin (nx + 1) → Fin (na + 1) → ℝ) (rB : Fin (ny + 1) → Fin (nb + 1) → ℝ),
          (∀ x a, 0 ≤ rA x a) ∧ (∀ y b, 0 ≤ rB y b) ∧
          (∀ x, ∑ a, rA x a = 1 / 2) ∧ (∀ y, ∑ b, rB y b = 1 / 2) ∧
          ∀ x y (S : Finset (Fin (na + 1))) (T : Finset (Fin (nb + 1))),
            (∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b) ≤
              (∑ a ∈ S, rA x a) + ∑ b ∈ T, rB y b) :
    ExtensiblyCausal D W := by
  refine ⟨hW, fun r s nx ny na nb σ hσ M N => ?_⟩
  obtain ⟨rA, rB, hrA, hrB, hmA, hmB, hbound⟩ := hrect r s nx ny na nb σ hσ M N
  have hcond := valid_born_extended D hW hσ M N
  exact causal_of_rectangles (bornExtended D W σ M N) rA rB hcond.1 hrA hrB hcond.2 hmA hmB
    hbound

/-- **`W_0` is extensibly causal in every port dimension `≥ 2`** (`thm:main` (ii), §5):
validity (`w0_valid`) and the rectangle bounds with the fixed endpoint arrays
(`rectangles_W0`) feed the transport decomposition `ec_of_rectangles`. -/
theorem w0_extensiblyCausal {D : Ports} (h : AllPortsGE2 D) :
    ExtensiblyCausal D (toC (W0 D.m D.d D.n D.e)) :=
  ec_of_rectangles (w0_valid (D := D) h) (rectangles_W0 (D := D) h)

end CausalNonpurifiability
