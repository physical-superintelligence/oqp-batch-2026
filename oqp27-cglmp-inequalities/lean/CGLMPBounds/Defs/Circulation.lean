module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


open scoped Matrix

/-!
# Fourth-root circulation: definitions

Supplement, Appendix C (pp. 5–6), Lemma D.4 (p. 15), and Appendix H (pp. 33–34).
All four-outcome spectral labels are in `Fin 4`, whose addition is modulo four.
The trace and squared Hilbert–Schmidt norm are normalized by the matrix dimension.
These definitions contain no positivity, commutativity, or desired inequality assumptions.
-/

namespace CGLMPBounds.Circulation

noncomputable section

abbrev Mat (r : ℕ) := Matrix (Fin r) (Fin r) ℂ

/-- Normalized complex matrix trace. -/
def tr {r : ℕ} (X : Mat r) : ℂ := Matrix.trace X / r

/-- Real part of the normalized trace. -/
def reTr {r : ℕ} (X : Mat r) : ℝ := (tr X).re

/-- Squared normalized Hilbert–Schmidt norm. -/
def hsSq {r : ℕ} (X : Mat r) : ℝ := reTr (Xᴴ * X)

/-- The fourth-root unitary represented by a four-outcome spectral PVM. -/
def root {r : ℕ} (E : Fin 4 → Mat r) : Mat r :=
  ∑ l, (Complex.I ^ l.val) • E l

/-- The normalized fourth-root correlation `tau(V†W)`. -/
def corr {r : ℕ} (V W : Mat r) : ℂ := tr (Vᴴ * W)

/-- The forbidden-overlap quantity of Appendix C. -/
def forbidden {r : ℕ} (V W : Mat r) : ℝ :=
  (1 - (corr V W).re + (corr V W).im) / 2

/-- The oriented three-edge circulation of Lemma D.4. -/
def circulation {r : ℕ} (U V W : Mat r) : ℝ :=
  (corr U V).im + (corr V W).im - (corr U W).im

/-- Sum of squared first-successor overlaps over the three pairs in Appendix H. -/
def positiveMass {r : ℕ} (A B C : Fin 4 → Mat r) : ℝ :=
  ∑ l, (hsSq (A l * B (l + 1)) + hsSq (B l * C (l + 1)) + hsSq (A l * C (l + 1)))

/-- Sum of squared opposite-label overlaps over the three pairs in Appendix H. -/
def oppositeMass {r : ℕ} (A B C : Fin 4 → Mat r) : ℝ :=
  ∑ l, (hsSq (A l * B (l + 2)) + hsSq (B l * C (l + 2)) + hsSq (A l * C (l + 2)))

/-- The right-hand side of (H.1), with Table H.1 expanded in its displayed order. -/
def sos {r : ℕ} (A B C : Fin 4 → Mat r) (σ : ℝ) : ℝ :=
  ∑ l, (
    hsSq (A l * B (l + 1) - (σ : ℂ) • (A l * C (l + 2))) +
    hsSq ((B (l + 1) * C (l + 2))ᴴ - (σ : ℂ) • (A l * C (l + 2))ᴴ) +
    hsSq ((A l * B (l + 1))ᴴ - (σ : ℂ) • (B (l + 1) * C (l + 3))) +
    hsSq (A l * C (l + 1) + (σ : ℂ) • (A l * B (l + 2))) +
    hsSq (B (l + 2) * C (l + 3) - (σ : ℂ) • (A l * B (l + 2))ᴴ) +
    hsSq ((A l * C (l + 1))ᴴ + (σ : ℂ) • (B (l + 3) * C (l + 1))ᴴ) +
    3 * hsSq (A l * B (l + 2) - ((σ / 3 : ℝ) : ℂ) • (A l * C (l + 2))) +
    3 * hsSq ((B l * C (l + 2))ᴴ - ((σ / 3 : ℝ) : ℂ) • (A l * C (l + 2))ᴴ) +
    (7 / 3 + 2 * σ) * hsSq (A l * C (l + 2)))

/-- The average of a cyclic fourth-root action, the projector onto its eigenvalue one. -/
def average4 {r : ℕ} (V : Mat r) : Mat r :=
  (1 / 4 : ℂ) • (1 + V + V ^ 2 + V ^ 3)

/-- Explicit spectral projector for the eigenvalue `i^l`, requiring no choice of eigenbasis. -/
def spectral {r : ℕ} (V : Mat r) (l : Fin 4) : Mat r :=
  average4 (((-Complex.I) ^ l.val) • V)

end
end CGLMPBounds.Circulation
