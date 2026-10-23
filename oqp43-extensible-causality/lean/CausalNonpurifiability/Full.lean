module

public import CausalNonpurifiability.Uniform
public import CausalNonpurifiability.Robustness
public import CausalNonpurifiability.RobustnessEC
public import CausalNonpurifiability.Linear.OpNorm
public import CausalNonpurifiability.EC.Bridge
public import CausalNonpurifiability.Boundary.Order
public import CausalNonpurifiability.Definitions.Hypotheses

@[expose] public section


/-!
# `CausalNonpurifiability.Full`

Uniform endpoints of `thm:main`, assembled from
the certificates (`Certificates/*`, `Uniform`, `Robustness`) and the extensible
causality theorem `w0_extensiblyCausal` (`EC/Bridge`):

* `w0_not_causallySeparable` — `W_0 ∉ O_{A≺B} + O_{B≺A}` in every port dimension `≥ 2`
  (`eq:negative`: `Tr(S_0 W_0) = -1/5` against `witness_nonneg_on_cs`);
* `uniform_kernel` — `thm:main` (i): `W_0` is valid, of rank `4de`, extensibly causal and not
  causally separable, for every `m, d, n, e ≥ 2`;
* `uniform_not_purifiable_of_purCS`, `dichotomy_forward_of_purCS` — the "⇒" direction of
  `eq:dichotomy` for `min{m,d,n,e} ≥ 2`, conditional on `PurificationNecessity` (`eq:purcs`,
  passed as a parameter); the "⇐" direction (`min = 1`) is in `Dichotomy`;
* `relative_ball_kernel_noEC` — the closed ball `eq:ball` without the EC clause
  (`Robustness.ball_kernel` re-exported);
* `relative_ball_kernel` — `thm:main` (ii) in PSD-bound form (`InBall`), adding
  `ball_extensiblyCausal` (`RobustnessEC`);
* `inBall_of_opNorm`, `relative_ball_kernel_norm` — the manuscript's operator-norm form
  `‖H‖_∞ ≤ 1/(300 m n)` (with `Wc D := WcC D`),
  via `psd_bounds_of_opNorm_le` (`Linear/OpNorm`).
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped ComplexOrder

section UniformEndpoints
variable (D : Ports)

/-- **`W_0` is not causally separable in any port dimension `≥ 2`** (`eq:negative`,
`sec:witness`): `Tr(S_0 W_0) = -1/5 < 0` while `Tr(S_0 ·) ≥ 0` on `O_{A≺B} + O_{B≺A}`. -/
theorem w0_not_causallySeparable (hD : AllPortsGE2 D) :
    ¬ CausallySeparable D (toC (W0 D.m D.d D.n D.e)) := by
  intro h
  have h0 := (Complex.nonneg_iff.mp (witness_nonneg_on_cs D hD.2.1 hD.2.2.2 _ h)).1
  rw [← Matrix.map_mul, trace_toC, witness_negative hD.1 hD.2.1 hD.2.2.1 hD.2.2.2,
    Complex.ratCast_re] at h0
  norm_num at h0

/-- **Uniform kernel theorem** (`thm:main` (i) in every port dimension `≥ 2`): `W_0` is a valid
process of rank `4de`, extensibly causal, and not causally separable. -/
theorem uniform_kernel (hD : AllPortsGE2 D) :
    Valid D (toC (W0 D.m D.d D.n D.e)) ∧
      Matrix.rank (toC (W0 D.m D.d D.n D.e)) = 4 * D.d * D.e ∧
      ExtensiblyCausal D (toC (W0 D.m D.d D.n D.e)) ∧
      ¬ CausallySeparable D (toC (W0 D.m D.d D.n D.e)) :=
  ⟨w0_valid D hD, uniform_rank hD.1 hD.2.1 hD.2.2.1 hD.2.2.2, w0_extensiblyCausal hD,
    w0_not_causallySeparable D hD⟩

/-- Nonpurifiability of `W_0` in every port dimension `≥ 2`, conditional on the published
purification-necessity theorem (`eq:purcs`, passed as a parameter). -/
theorem uniform_not_purifiable_of_purCS (hPurCS : PurificationNecessity) (hD : AllPortsGE2 D) :
    ¬ Purifiable D (toC (W0 D.m D.d D.n D.e)) :=
  fun hPur => w0_not_causallySeparable D hD (hPurCS D _ (w0_valid D hD) hPur)

/-- **`eq:dichotomy`, "⇒" for `min{m,d,n,e} ≥ 2`**: an extensibly causal process without a
finite purification exists on every such port tuple (conditional on `PurificationNecessity`). -/
theorem dichotomy_forward_of_purCS (hPurCS : PurificationNecessity) (hD : AllPortsGE2 D) :
    ∃ W : PMat D, ExtensiblyCausal D W ∧ ¬ Purifiable D W :=
  ⟨toC (W0 D.m D.d D.n D.e), w0_extensiblyCausal hD, uniform_not_purifiable_of_purCS D hPurCS hD⟩

/-- **Closed ball, EC-free part** (`thm:main` (ii) without the EC clause; `eq:ball`,
`eq:ball-fullrank`, `eq:ball-negative`): every point of the ball is a valid, full-rank, causally
nonseparable process. The full `relative_ball_kernel` (adding `ExtensiblyCausal D (WcC D + H)`)
is to be assembled here from `ball_extensiblyCausal` (`RobustnessEC`). -/
theorem relative_ball_kernel_noEC (hD : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    Valid D (WcC D + H) ∧ (WcC D + H).PosDef ∧ ¬ CausallySeparable D (WcC D + H) :=
  ball_kernel D hD hH

/-- **Closed relative ball** (`thm:main` (ii), PSD-bound form of `eq:ball`): every point of the
ball is a valid, full-rank, extensibly causal, causally nonseparable process. -/
theorem relative_ball_kernel (hD : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    Valid D (WcC D + H) ∧ (WcC D + H).PosDef ∧ ExtensiblyCausal D (WcC D + H) ∧
      ¬ CausallySeparable D (WcC D + H) :=
  ⟨ball_valid hD hH, ball_posDef hH, ball_extensiblyCausal D hD hH,
    ball_not_causallySeparable D hD hH⟩

/-- The operator-norm form of `eq:ball` implies the PSD-bound form: for Hermitian `H ∈ L_V`
with `Tr H = 0` and `‖H‖_∞ ≤ 1/(300 m n)`, `H ∈ InBall D` (`Linear/OpNorm`,
`psd_bounds_of_opNorm_le`). -/
theorem inBall_of_opNorm {H : PMat D} (hLV : InLV D H) (htr : H.trace = 0)
    (hnorm : opNorm H ≤ 1 / (300 * D.m * D.n)) : InBall D H := by
  have hr : (0 : ℝ) ≤ 1 / (300 * D.m * D.n) := by positivity
  obtain ⟨h1, h2⟩ := psd_bounds_of_opNorm_le hLV.isHermitian hr hnorm
  refine ⟨hLV, htr, ?_, ?_⟩
  · rwa [ballRadius_eq_ofReal]
  · rwa [ballRadius_eq_ofReal]

/-- **Closed relative ball, operator-norm form** (`thm:main` (ii), `eq:ball`): for `H ∈ L_V`, `Tr H = 0`, `‖H‖_∞ ≤ 1/(300 m n)`,
`W_c + H` is valid, full rank, extensibly causal and not causally separable. -/
theorem relative_ball_kernel_norm (hD : AllPortsGE2 D) {H : PMat D} (hLV : InLV D H)
    (htr : H.trace = 0) (hnorm : opNorm H ≤ 1 / (300 * D.m * D.n)) :
    Valid D (WcC D + H) ∧ (WcC D + H).PosDef ∧ ExtensiblyCausal D (WcC D + H) ∧
      ¬ CausallySeparable D (WcC D + H) :=
  relative_ball_kernel D hD (inBall_of_opNorm D hLV htr hnorm)

/-- Nonpurifiability throughout the closed ball, conditional on `PurificationNecessity`. -/
theorem ball_not_purifiable_of_purCS (hPurCS : PurificationNecessity) (hD : AllPortsGE2 D)
    {H : PMat D} (hH : InBall D H) : ¬ Purifiable D (WcC D + H) :=
  fun hPur => ball_not_causallySeparable D hD hH (hPurCS D _ (ball_valid hD hH) hPur)

/-- Nonpurifiability throughout the closed ball, operator-norm form. -/
theorem ball_not_purifiable_of_purCS_norm (hPurCS : PurificationNecessity) (hD : AllPortsGE2 D)
    {H : PMat D} (hLV : InLV D H) (htr : H.trace = 0)
    (hnorm : opNorm H ≤ 1 / (300 * D.m * D.n)) : ¬ Purifiable D (WcC D + H) :=
  ball_not_purifiable_of_purCS D hPurCS hD (inBall_of_opNorm D hLV htr hnorm)

end UniformEndpoints

end CausalNonpurifiability
