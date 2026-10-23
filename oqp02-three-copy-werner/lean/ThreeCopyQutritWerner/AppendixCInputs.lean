module

public import ThreeCopyQutritWerner.ZeroFamilies

@[expose] public section


/-!
# The analytic inputs of the qutrit zero classification, as named statements

Manuscript Theorem 5.1 (inclusion "⊆": every normalized rank-≤-2 qutrit endpoint zero lies in the
union of families I–III) rests on (a) a property of the saturated kernel of the endpoint SOS
certificate of T2.1a (claim `S5.1-kernel`), (b) the zero relations and the rank-two minor algebra of
Section 5.1 and Appendix C (`S5.1-H`, `AppC-alg`), (c) the exclusion of rank-one zeros, `q(x y†) ≥ N/8`
(`endpointEnergy_ketBra_ge`, `rank_eq_two_of_endpointEnergy_eq_zero`), and (d) three analytic equality
results listed in Appendix C. This file states (d) as named propositions, in the same way
`QutritEndpointInequality` records claim T2.1a; they are proved in later modules (`appCInput1_proved`,
`appCInput2_product_ray`, `appCInput3_proved`):

* `AppCInput1` (claim `AppC-1`): a rank-two qutrit matrix with `C² = κ C` obeys
  `q(C) ≥ (s₁ - s₂)²/6`; at a zero its range and corange are both thin at a common site;
* `AppCInput2` (`AppC-2`): a rank-two endpoint zero whose range contains a nonzero fully
  product vector has local range dimension at most two at every site;
* `AppCInput3` (`AppC-3`): a normalized rank-≤-2 endpoint zero with a thin local range lies in
  the union of families I–III (`IsQutritZeroFamilyMember`, whose members have both singular
  values `1/√2` by `isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember`, in
  `ZeroFamilies`).

`ThinSourceProperty` is the conclusion of (a)–(c)+`AppCInput1`+`AppCInput2` in the manuscript's
argument (every endpoint zero has a thin source); `QutritZeroClassification` is the inclusion
"⊆". Their quantifier "rank ≤ 2" covers rank one only vacuously, since by (c) a nonzero endpoint
zero has rank exactly two. The only theorem here is the trivial step of the manuscript's argument
that combines them: `ThinSourceProperty → AppCInput3 → QutritZeroClassification`.

Conventions. The local range (support) of `C` at site 1 is the range of the reduced operator
`Tr₂₃(C C†)`, and its dimension is that operator's rank (`localRangeDim₁`); the corange uses
`C† C`. For a matrix of rank at most two, with its two largest singular values `s₁ ≥ s₂ ≥ 0`
(`s₂ = 0` if the rank is below two), one has
`s₁² + s₂² = ‖C‖_F²` and `s₁² s₂² = (‖C‖_F⁴ - ‖C†C‖_F²)/2`, so
`(s₁ - s₂)² = ‖C‖_F² - 2 √((‖C‖_F⁴ - ‖C†C‖_F²)/2)` (`singularGapSq`).
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

section Local

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Dimension of the local support of `ran C` at site 1: `rank Tr₂₃(C C†)`. -/
def localRangeDim₁ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℕ := (ptrace₂₃ (C * Cᴴ)).rank

/-- Dimension of the local support of `ran C` at site 2: `rank Tr₁₃(C C†)`. -/
def localRangeDim₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℕ := (ptrace₁₃ (C * Cᴴ)).rank

/-- Dimension of the local support of `ran C` at site 3: `rank Tr₁₂(C C†)`. -/
def localRangeDim₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℕ := (ptrace₁₂ (C * Cᴴ)).rank

/-- Dimension of the local support of the corange `ran C†` at site 1. -/
def localCorangeDim₁ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℕ := (ptrace₂₃ (Cᴴ * C)).rank

/-- Dimension of the local support of the corange `ran C†` at site 2. -/
def localCorangeDim₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℕ := (ptrace₁₃ (Cᴴ * C)).rank

/-- Dimension of the local support of the corange `ran C†` at site 3. -/
def localCorangeDim₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℕ := (ptrace₁₂ (Cᴴ * C)).rank

/-- `ran C` is thin (local dimension at most two) at some site. -/
def HasThinLocalRange (C : Matrix (a × b × c) (a × b × c) ℂ) : Prop :=
  localRangeDim₁ C ≤ 2 ∨ localRangeDim₂ C ≤ 2 ∨ localRangeDim₃ C ≤ 2

/-- A fully product vector `u ⊗ v ⊗ w`. -/
def IsFullyProduct (ψ : a × b × c → ℂ) : Prop :=
  ∃ (u : a → ℂ) (v : b → ℂ) (w : c → ℂ), ∀ x, ψ x = u x.1 * v x.2.1 * w x.2.2

/-- `(s₁ - s₂)²` for a matrix of rank at most two with nonzero singular values `s₁, s₂`. -/
def singularGapSq (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  frobSq C - 2 * Real.sqrt ((frobSq C ^ 2 - frobSq (Cᴴ * C)) / 2)

end Local

/-- The qutrit three-site index type. -/
abbrev QutritSites := Fin 3 × Fin 3 × Fin 3

/-- Claim AppC-1 (statement): a rank-two qutrit matrix with
`C² = κ C` obeys `q(C) ≥ (s₁ - s₂)²/6`, and at a zero its range and corange are both thin at a
common site. -/
def AppCInput1 : Prop :=
  ∀ (C : Matrix QutritSites QutritSites ℂ) (κ : ℂ), C.rank = 2 → C * C = κ • C →
    singularGapSq C / 6 ≤ endpointEnergy C ∧
      (endpointEnergy C = 0 →
        (localRangeDim₁ C ≤ 2 ∧ localCorangeDim₁ C ≤ 2) ∨
          (localRangeDim₂ C ≤ 2 ∧ localCorangeDim₂ C ≤ 2) ∨
            (localRangeDim₃ C ≤ 2 ∧ localCorangeDim₃ C ≤ 2))

/-- Claim AppC-2 (statement): a rank-two endpoint zero whose range
contains a nonzero fully product vector has local range dimension at most two at every site. -/
def AppCInput2 : Prop :=
  ∀ C : Matrix QutritSites QutritSites ℂ, C.rank = 2 → endpointEnergy C = 0 →
    (∃ x : QutritSites → ℂ, C *ᵥ x ≠ 0 ∧ IsFullyProduct (C *ᵥ x)) →
      localRangeDim₁ C ≤ 2 ∧ localRangeDim₂ C ≤ 2 ∧ localRangeDim₃ C ≤ 2

/-- Claim AppC-3 (statement): a normalized rank-≤-2 qutrit endpoint
zero with a thin local range lies in the union of families I–III. -/
def AppCInput3 : Prop :=
  ∀ C : Matrix QutritSites QutritSites ℂ, C.rank ≤ 2 → invN C = 1 → endpointEnergy C = 0 →
    HasThinLocalRange C → IsQutritZeroFamilyMember C

/-- Statement: every normalized rank-≤-2 qutrit endpoint zero has a thin local range (the manuscript
derives this from the certificate kernel, the zero relations, `AppCInput1` and `AppCInput2`). -/
def ThinSourceProperty : Prop :=
  ∀ C : Matrix QutritSites QutritSites ℂ, C.rank ≤ 2 → invN C = 1 → endpointEnergy C = 0 →
    HasThinLocalRange C

/-- Claim T5.1, inclusion "⊆" (statement): every normalized rank-≤-2 qutrit endpoint zero lies in the
union of families I–III. -/
def QutritZeroClassification : Prop :=
  ∀ C : Matrix QutritSites QutritSites ℂ, C.rank ≤ 2 → invN C = 1 → endpointEnergy C = 0 →
    IsQutritZeroFamilyMember C

/-- The combining step of the manuscript's argument (a REDUCTION, not a proof of Theorem 5.1). -/
theorem qutritZeroClassification_of_thinSource (h1 : ThinSourceProperty) (h3 : AppCInput3) :
    QutritZeroClassification := by
  unfold QutritZeroClassification
  intro C hr hN hq
  exact h3 C hr hN hq (h1 C hr hN hq)

end ThreeCopyQutritWerner

end
