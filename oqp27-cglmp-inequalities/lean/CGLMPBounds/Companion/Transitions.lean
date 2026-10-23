module

public import CGLMPBounds.Companion.Shift
public import CGLMPBounds.Companion.Clock

@[expose] public section


/-!
# Transition telescoping and the source companion clock

The transition sequence is `Z₀⁻¹Z₁, Z₁⁻¹Z₂, Z₂⁻¹Z₃, Z₃⁻¹Z₀J`.
Its four cyclic products are `J` when the covariance unitaries commute with `J`.
This proves the fourth-power identity before Fourier transformation.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

section Group
variable {G : Type*} [Group G]

/-- The four transitions, including the twisted closing edge `Z₄=Z₀J`. -/
def transitions (Z : Fin 4 → G) (J : G) : Fin 4 → G :=
  ![(Z 0)⁻¹ * Z 1, (Z 1)⁻¹ * Z 2, (Z 2)⁻¹ * Z 3, (Z 3)⁻¹ * Z 0 * J]

lemma transitions_commute (Z : Fin 4 → G) (J : G) (hJ : ∀ t, Commute J (Z t))
    (t : Fin 4) : Commute J (transitions Z J t) := by
  fin_cases t
  · exact (hJ 0).inv_right.mul_right (hJ 1)
  · exact (hJ 1).inv_right.mul_right (hJ 2)
  · exact (hJ 2).inv_right.mul_right (hJ 3)
  · exact ((hJ 3).inv_right.mul_right (hJ 0)).mul_right (Commute.refl J)

lemma rotate_product_four {a b c e J : G} (h : a * b * c * e = J)
    (ha : Commute a J) : b * c * e * a = J := by
  calc
    b * c * e * a = a⁻¹ * (a * b * c * e) * a := by group
    _ = a⁻¹ * J * a := by rw [h]
    _ = J := ha.inv_mul_cancel

/-- All four cyclic products telescope to the same outcome shift. -/
theorem transitions_cycle (Z : Fin 4 → G) (J : G) (hJ : ∀ t, Commute J (Z t))
    (t : Fin 4) :
    transitions Z J t * transitions Z J (t + 1) * transitions Z J (t + 2) *
      transitions Z J (t + 3) = J := by
  have h0 : transitions Z J 0 * transitions Z J 1 * transitions Z J 2 *
      transitions Z J 3 = J := by
    simp [transitions, mul_assoc]
  have h1 := rotate_product_four h0 (transitions_commute Z J hJ 0).symm
  have h2 := rotate_product_four h1 (transitions_commute Z J hJ 1).symm
  have h3 := rotate_product_four h2 (transitions_commute Z J hJ 2).symm
  fin_cases t
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end Group

variable {d n : ℕ} [NeZero d]

/-- The four-dimensional clock of Lemma C.1, before reordering and Fourier transformation. -/
def companionClock (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ :=
  clockMatrix fun t =>
    (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
      (fun s => unitaryConjugator (P s) (hP s))
      (unitaryShift (d := d) (n := n)) t : OutcomeMat d n)

lemma companionClock_star_mul (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    (companionClock P hP)ᴴ * companionClock P hP = 1 := by
  unfold companionClock
  apply clockMatrix_star_mul
  intro t
  exact (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
    (fun s => unitaryConjugator (P s) (hP s))
    (unitaryShift (d := d) (n := n)) t).property.1

lemma companionClock_mul_star (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    companionClock P hP * (companionClock P hP)ᴴ = 1 := by
  unfold companionClock
  apply clockMatrix_mul_star
  intro t
  exact (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
    (fun s => unitaryConjugator (P s) (hP s))
    (unitaryShift (d := d) (n := n)) t).property.2

/-- The exact source identity `R⁴=I₄⊗J⊗I_n`, from PVM assumptions alone. -/
theorem companionClock_fourth (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) :
    companionClock P hP ^ 4 = clockLift (shift (d := d) (n := n)) := by
  unfold companionClock
  apply clockMatrix_fourth
  intro t
  exact congrArg (fun U : Matrix.unitaryGroup (OutcomeSpace d n) ℂ =>
      (U : OutcomeMat d n))
    (transitions_cycle (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
      (fun s => unitaryConjugator (P s) (hP s)) (unitaryShift (d := d) (n := n))
      (fun s => unitaryShift_commutes (P s) (hP s)) t)

end
end CGLMPBounds.Companion
