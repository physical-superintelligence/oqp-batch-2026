module

public import VacuumBellSeparation.FreeField.OQP12
public import VacuumBellSeparation.FreeField.Existence
public import VacuumBellSeparation.FreeField.LocalAlgebraNonabelian

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` and is proved
by the corresponding theorem of the library `VacuumBellSeparation`:

* `no_chsh_violation_far_apart`, `no_chsh_violation_far_apart_uniform`, and `theorem_1_1`,
  `corollary_1_2` with the Bell correlation written out: `FreeField/OQP12.lean`, from Theorem 1.1
  and Corollary 1.2 of `FreeField/MainTheorems.lean`;
* `freeFieldVacuum_exists`: `FreeField/Existence.lean`;
* `localAlgebra_open_nonabelian`: `FreeField/LocalAlgebraNonabelian.lean`.
-/

open scoped InnerProductSpace

namespace VacuumBellSeparation.OQP12

theorem no_chsh_violation_far_apart (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂)
    (a : Spacetime) (ha : a.1 ^ 2 < ‖a.2‖ ^ 2) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2 :=
  VacuumBellSeparation.no_chsh_violation_far_apart m hm O₁ O₂ hO₁ hO₂ a ha

theorem theorem_1_1 :
    ∃ Cstar : ℝ, 2 < Cstar ∧
      ∀ m R L : ℝ, 0 < m → 0 < R → Cstar * R ≤ L →
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H),
          sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
            A₀ ∈ localAlgebra V (doubleCone 0 R) ∧ A₁ ∈ localAlgebra V (doubleCone 0 R) ∧
            B₀ ∈ localAlgebra V (doubleCone (0, L • e₁) R) ∧
            B₁ ∈ localAlgebra V (doubleCone (0, L • e₁) R) ∧
            IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
            ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
            v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} = 1 :=
  VacuumBellSeparation.theorem_1_1_explicit

theorem corollary_1_2 :
    ∀ m : ℝ, 0 < m → ∀ O₁ O₂ : Set Spacetime, Bornology.IsBounded O₁ → Bornology.IsBounded O₂ →
      ∀ a : Spacetime, a.1 ^ 2 < ‖a.2‖ ^ 2 →
        ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
            (V : FreeFieldVacuum m H),
            sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
              A₀ ∈ localAlgebra V O₁ ∧ A₁ ∈ localAlgebra V O₁ ∧
              B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) ∧
              B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) ∧
              IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
              ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
              v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} =
              1 :=
  VacuumBellSeparation.corollary_1_2_explicit

theorem freeFieldVacuum_exists :
    ∀ m : ℝ, 0 < m → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H), Nonempty (FreeFieldVacuum m H) :=
  VacuumBellSeparation.freeFieldVacuum_exists

theorem no_chsh_violation_far_apart_uniform (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂) :
    ∃ D : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), D ≤ ‖x‖ →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        B₁ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2 :=
  VacuumBellSeparation.no_chsh_violation_far_apart_uniform m hm O₁ O₂ hO₁ hO₂

theorem localAlgebra_open_nonabelian (m : ℝ) (hm : 0 < m)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : FreeFieldVacuum m H) (O : Set Spacetime) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ A ∈ localAlgebra V O, ∃ B ∈ localAlgebra V O, A * B ≠ B * A :=
  V.localAlgebra_open_nonabelian hm hO hne

end VacuumBellSeparation.OQP12
