module

public import CausalNonpurifiability.EC.Bridge

@[expose] public section


/-!
# `CausalNonpurifiability.EC.Components`

Theorem 5.6 (`thm:EC`) with its components (`eq:causal-components`). In every experiment with
`W₀` (all port dimensions `≥ 2`) there are conditional probability distributions `p^{A≺B}`,
`p^{B≺A}` with

* `p = ½ p^{A≺B} + ½ p^{B≺A}`,
* `∑_b p^{A≺B}(a,b|x,y) = 2 r_A(a|x)` and `∑_a p^{B≺A}(a,b|x,y) = 2 r_B(b|y)`,

where `r_A(a|x) = Tr[(χ_A ⊗ σ^{R_A}) E_{a|x}]`, `r_B(b|y) = Tr[(χ_B ⊗ σ^{R_B}) H_{b|y}]`
(`eq:endpoints`; `rA`, `rB` of `EC/Rectangles`), `χ_A = θ_m/2`, `χ_B = θ_n/2`
(`eq:reference-states`), `E_{a|x} = Tr_{A_O} M_{a|x}` and `H_{b|y} = Tr_{B_O} N_{b|y}`.

`EC/Bridge` keeps only the conclusion "extensibly causal"; here the two components and their
marginals are kept. The statements are also given with `rA`, `rB`, `χ_A`, `χ_B` unfolded
(`w0_causal_components`, `w0_rectangle`), in the vocabulary of the Comparator challenge.
-/

set_option autoImplicit false

open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

/-- `eq:causal-components` from transports: if for every pair of settings `z` splits the table
`p x y` so that the rows of `z` carry the masses `eA x a` and the columns of `p - z` the masses
`eB y b` (masses `1/2` each), then `2 z` and `2 (p - z)` are conditional probability
distributions with average `p` and marginals `2 eA x a` and `2 eB y b`. -/
theorem components_of_transport {X Y A B : Type} [Fintype A] [Fintype B]
    (p : Prob X Y A B) (eA : X → A → ℝ) (eB : Y → B → ℝ)
    (hmA : ∀ x, ∑ a, eA x a = 1 / 2) (hmB : ∀ y, ∑ b, eB y b = 1 / 2)
    (htr : ∀ x y, ∃ z : A → B → ℝ,
      (∀ a b, 0 ≤ z a b ∧ z a b ≤ p x y a b) ∧
      (∀ a, ∑ b, z a b = eA x a) ∧
      (∀ b, ∑ a, (p x y a b - z a b) = eB y b)) :
    ∃ pAB pBA : Prob X Y A B,
      Conditional pAB ∧ Conditional pBA ∧
      (∀ x y a b, p x y a b = (1 / 2) * pAB x y a b + (1 / 2) * pBA x y a b) ∧
      (∀ x y a, ∑ b, pAB x y a b = 2 * eA x a) ∧
      (∀ x y b, ∑ a, pBA x y a b = 2 * eB y b) := by
  choose z hz using htr
  refine ⟨fun x y a b => 2 * z x y a b, fun x y a b => 2 * (p x y a b - z x y a b),
    ⟨fun x y a b => ?_, fun x y => ?_⟩, ⟨fun x y a b => ?_, fun x y => ?_⟩, ?_, ?_, ?_⟩
  · have := (hz x y).1 a b
    linarith
  · simp only [← Finset.mul_sum, (hz x y).2.1, hmA x]
    norm_num
  · have := (hz x y).1 a b
    linarith
  · rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hz x y).2.2, hmB y]
    norm_num
  · intro x y a b
    ring
  · intro x y a
    simp only [← Finset.mul_sum, (hz x y).2.1]
  · intro x y b
    simp only [← Finset.mul_sum, (hz x y).2.2]

/-- **Lemma 5.1** (`lem:signed`, `eq:signed-decomposition`, `eq:reference-states`):
`U ∈ O_{A≺B}`, `V ∈ O_{B≺A}`, `W₀ = U + V + 2 Q_C`, `ω_A(U) = P_m/10`,
`χ_A := ω_A(U) + C_A = θ_m/2`, `ω_B(V) = P_n/10`, `χ_B := ω_B(V) + C_B = θ_n/2`, with
`C_A = Tr_{B_I} C` and `C_B = Tr_{A_I} C`; `χ_A`, `χ_B` are positive with trace `1/2`. -/
theorem lemma_5_1 (D : Ports) (hD : AllPortsGE2 D) :
    OrderedAB D (toC (U D.m D.d D.n D.e)) ∧ OrderedBA D (toC (V D.m D.d D.n D.e)) ∧
      toC (W0 D.m D.d D.n D.e) =
        toC (U D.m D.d D.n D.e) + toC (V D.m D.d D.n D.e) + (2 : ℂ) • QC D (toC (C D.m D.n)) ∧
      omegaA D (toC (U D.m D.d D.n D.e)) = toC ((1 / 10 : ℚ) • P D.m) ∧
      omegaA D (toC (U D.m D.d D.n D.e)) + ptraceOut (toC (C D.m D.n)) =
        toC ((1 / 2 : ℚ) • theta D.m) ∧
      omegaB D (toC (V D.m D.d D.n D.e)) = toC ((1 / 10 : ℚ) • P D.n) ∧
      omegaB D (toC (V D.m D.d D.n D.e)) + ptraceFst (toC (C D.m D.n)) =
        toC ((1 / 2 : ℚ) • theta D.n) ∧
      (toC ((1 / 2 : ℚ) • theta D.m)).PosSemidef ∧ (toC ((1 / 2 : ℚ) • theta D.n)).PosSemidef ∧
      (toC ((1 / 2 : ℚ) • theta D.m)).trace = 1 / 2 ∧
      (toC ((1 / 2 : ℚ) • theta D.n)).trace = 1 / 2 :=
  ⟨u_orderedAB D hD, v_orderedBA D hD, W0_signed D, omegaA_toC_U D hD, (chiA_eq D hD).symm,
    omegaB_toC_V D hD, (chiB_eq D hD).symm, chiA_posSemidef D, chiB_posSemidef D,
    (chiA_trace D hD.1).trans (by norm_num), (chiB_trace D hD.2.2.1).trans (by norm_num)⟩

/-- **Lemma 5.2** (`lem:SOS`, `eq:operator-SOS`) for effects `E₀, E₁, H₀, H₁` on `ℂ^ι` with
`E_i H_j = H_j E_i`, where `D_ij = E_i + H_j - 2 E_i H_j`, `Λ = 7E₀ + E₁ - 7H₀ - H₁` and
`Γ = -E₀ + E₁ - H₀ + H₁`: the identity of `eq:operator-SOS` **multiplied by `2`** (its
coefficients `16, 1/2, 7/2, 44, 4` become `32, 1, 7, 88, 8`), and the operator inequality
`37 D₀₀ + 7 D₀₁ + 7 D₁₀ - 3 D₁₁ ≥ 0`. -/
theorem lemma_5_2 {ι : Type} [Fintype ι] [DecidableEq ι] {E0 E1 H0 H1 : Matrix ι ι ℂ}
    (hE0 : Effect E0) (hE1 : Effect E1) (hH0 : Effect H0) (hH1 : Effect H1)
    (h00 : E0 * H0 = H0 * E0) (h01 : E0 * H1 = H1 * E0) (h10 : E1 * H0 = H0 * E1)
    (h11 : E1 * H1 = H1 * E1) :
    2 * (37 * (E0 + H0 - 2 * E0 * H0) + 7 * (E0 + H1 - 2 * E0 * H1) +
        7 * (E1 + H0 - 2 * E1 * H0) - 3 * (E1 + H1 - 2 * E1 * H1)) =
      32 * (E0 - H0) ^ 2 + (7 * E0 + E1 - 7 * H0 - H1) ^ 2 + 7 * (-E0 + E1 - H0 + H1) ^ 2 +
        88 * (E0 - E0 ^ 2 + H0 - H0 ^ 2) + 8 * (E1 - E1 ^ 2 + H1 - H1 ^ 2) ∧
    (37 * (E0 + H0 - 2 * E0 * H0) + 7 * (E0 + H1 - 2 * E0 * H1) +
        7 * (E1 + H0 - 2 * E1 * H0) - 3 * (E1 + H1 - 2 * E1 * H1)).PosSemidef :=
  ⟨operator_sos_two E0 E1 H0 H1 h00 h01 h10 h11, by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, dXor] using
      sos_psd_of_commute hE0 hE1 hH0 hH1 h00 h01 h10 h11⟩

variable {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Proposition 5.4** (`prop:rectangles`, `eq:rectangle`), with `r_A`, `r_B` unfolded: in every
experiment with `W₀`, `p(S,T|x,y) ≤ r_A(S|x) + r_B(T|y)` for all settings and all sets of
outcomes. -/
theorem w0_rectangle (D : Ports) (h : AllPortsGE2 D) {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (S : Finset A) (T : Finset B) :
    (∑ a ∈ S, ∑ b ∈ T, bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N x y a b) ≤
      (∑ a ∈ S,
          (((toC ((1 / 2 : ℚ) • theta D.m) ⊗ₖ ptraceOut σ) *
            ptraceOut (M.elem x a)).trace).re) +
        ∑ b ∈ T,
          (((toC ((1 / 2 : ℚ) • theta D.n) ⊗ₖ ptraceFst σ) *
            ptraceOut (N.elem y b)).trace).re :=
  (rectangle_interface_W0 D h hσ M N).2.2.2.2 x y S T

/-- **Theorem 5.6** (`thm:EC`, `eq:causal-components`), with `r_A`, `r_B` unfolded: in every
experiment with `W₀` (all ports `≥ 2`) the distribution is the average of two conditional
probability distributions whose marginals are `2 r_A(a|x)` (independent of `y`) and `2 r_B(b|y)`
(independent of `x`). "In particular, `W₀` is extensibly causal" is `w0_extensiblyCausal`. -/
theorem w0_causal_components (D : Ports) (h : AllPortsGE2 D) {σ : Op (RA × RB)}
    (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    ∃ pAB pBA : Prob X Y A B, Conditional pAB ∧ Conditional pBA ∧
      (∀ x y a b, bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N x y a b =
        (1 / 2) * pAB x y a b + (1 / 2) * pBA x y a b) ∧
      (∀ x y a, ∑ b, pAB x y a b =
        2 * (((toC ((1 / 2 : ℚ) • theta D.m) ⊗ₖ ptraceOut σ) *
          ptraceOut (M.elem x a)).trace).re) ∧
      (∀ x y b, ∑ a, pBA x y a b =
        2 * (((toC ((1 / 2 : ℚ) • theta D.n) ⊗ₖ ptraceFst σ) *
          ptraceOut (N.elem y b)).trace).re) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rectangle_interface_W0 D h hσ M N
  have hcond := valid_born_extended D (w0_valid (D := D) h) hσ M N
  exact components_of_transport (bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N)
    (rA D σ (chiA D) M) (rB D σ (chiB D) N) h3 h4 fun x y =>
      transport_of_rectangles _ (rA D σ (chiA D) M x) (rB D σ (chiB D) N y) (hcond.1 x y)
        (h1 x) (h2 y) (hcond.2 x y) (h3 x) (h4 y) (h5 x y)

end CausalNonpurifiability
