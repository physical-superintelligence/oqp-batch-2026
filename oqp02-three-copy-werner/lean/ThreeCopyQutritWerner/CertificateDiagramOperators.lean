module

public import ThreeCopyQutritWerner.CertificateDiagramCommutation
public import ThreeCopyQutritWerner.CertificateDescendants

@[expose] public section


/-!
# Complex physical diagram operators

This scalar-extension layer exposes the exact commutation premise used by the
complete-frame action theorem. Arbitrary complex linear combinations of literal
PT-permutation diagrams commute with both physical simple lowering operators.
No positivity, Hermiticity, compression data, or endpoint conclusion is assumed.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Literal zero/one diagrams are unchanged by an exact scalar ring map. -/
theorem certificateLocalDiagram_map {k : ℕ} {n R : Type*} [Fintype n]
    [DecidableEq n] [Semiring R] (f : ℤ →+* R)
    (S : Finset (Fin k)) (σ : Equiv.Perm (Fin k)) :
    (certificateLocalDiagram (n := n) (R := ℤ) S σ).map f =
      certificateLocalDiagram (R := R) S σ := by
  ext r c
  simp [certificateLocalDiagram, certificateWordTranspose, Matrix.map_apply,
    PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]

/-- A literal finite linear combination, with all 720 register permutations available. -/
def certificateLocalDiagramCombination (S : Finset (Fin 6))
    (weight : Equiv.Perm (Fin 6) → ℂ) :
    Matrix CertificateLocalWord CertificateLocalWord ℂ :=
  ∑ σ, weight σ • certificateLocalDiagram S σ

/-- The source-bound integer commutation equation persists over the complex field. -/
theorem certificateLocalDiagram_generator_complex (S : Finset (Fin 6))
    (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalDiagram (R := ℂ) S σ *
        (certificateLocalGenerator Sᶜ i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator Sᶜ i j).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagram S σ := by
  have h := congrArg (fun M : Matrix CertificateLocalWord CertificateLocalWord ℤ =>
      M.map (Int.castRingHom ℂ)) (certificateLocalDiagram_commutes_generator S σ i j)
  simp only [Matrix.map_mul (f := Int.castRingHom ℂ), certificateLocalDiagram_map] at h
  exact h.symm

/-- Complementary fundamental/dual conventions give the same complex commutant. -/
theorem certificateLocalDiagram_complement_generator_complex (S : Finset (Fin 6))
    (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalDiagram (R := ℂ) S σ *
        (certificateLocalGenerator S i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator S i j).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagram S σ := by
  have h := congrArg (fun M : Matrix CertificateLocalWord CertificateLocalWord ℤ =>
      M.map (Int.castRingHom ℂ))
        (certificateLocalDiagram_commutes_complement_generator S σ i j)
  simp only [Matrix.map_mul (f := Int.castRingHom ℂ), certificateLocalDiagram_map] at h
  exact h.symm

/-- Weighted sums retain exact commutation, without restrictions on their coefficients. -/
theorem certificateDiagramCombination_commutes_of_each
    (S : Finset (Fin 6)) (weight : Equiv.Perm (Fin 6) → ℂ)
    (E : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (h : ∀ σ, certificateLocalDiagram S σ * E = E * certificateLocalDiagram S σ) :
    certificateLocalDiagramCombination S weight * E =
      E * certificateLocalDiagramCombination S weight := by
  rw [certificateLocalDiagramCombination, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

/-- All physical diagram combinations commute with the corresponding simple lowering. -/
theorem certificateDiagramCombination_lowering (S : Finset (Fin 6))
    (weight : Equiv.Perm (Fin 6) → ℂ) (g : Fin 2) :
    certificateLocalDiagramCombination S weight *
        (certificateLocalLowering Sᶜ g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering Sᶜ g).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagramCombination S weight := by
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  by_cases hg : g = 0
  · simpa only [certificateLocalLowering, hg, if_true] using
      certificateLocalDiagram_generator_complex S σ 1 0
  · simpa only [certificateLocalLowering, hg, if_false] using
      certificateLocalDiagram_generator_complex S σ 2 1

theorem certificateDiagramCombination_complement_lowering (S : Finset (Fin 6))
    (weight : Equiv.Perm (Fin 6) → ℂ) (g : Fin 2) :
    certificateLocalDiagramCombination S weight *
        (certificateLocalLowering S g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering S g).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagramCombination S weight := by
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  by_cases hg : g = 0
  · simpa only [certificateLocalLowering, hg, if_true] using
      certificateLocalDiagram_complement_generator_complex S σ 1 0
  · simpa only [certificateLocalLowering, hg, if_false] using
      certificateLocalDiagram_complement_generator_complex S σ 2 1

/-- Sector 2's full-frame commutation premise follows for any diagram coefficients. -/
theorem certificateDiagramCombination2_lowering (weight : Equiv.Perm (Fin 6) → ℂ)
    (g : Fin 2) :
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight *
        (certificateLocalLowering {0} g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering {0} g).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight := by
  have h : ({1, 2, 3, 4, 5} : Finset (Fin 6))ᶜ = {0} := by decide
  simpa only [h] using certificateDiagramCombination_lowering {1, 2, 3, 4, 5} weight g

/-- Sector 1's full-frame commutation premise follows for any diagram coefficients. -/
theorem certificateDiagramCombination1_lowering (weight : Equiv.Perm (Fin 6) → ℂ)
    (g : Fin 2) :
    certificateLocalDiagramCombination {3, 4, 5} weight *
        (certificateLocalLowering {0, 1, 2} g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering {0, 1, 2} g).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagramCombination {3, 4, 5} weight := by
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateDiagramCombination_lowering {3, 4, 5} weight g

/-- Sector 0 uses the complementary one-register source-frame convention. -/
theorem certificateDiagramCombination0_lowering (weight : Equiv.Perm (Fin 6) → ℂ)
    (g : Fin 2) :
    certificateLocalDiagramCombination {5} weight *
        (certificateLocalLowering {5} g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering {5} g).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagramCombination {5} weight :=
  certificateDiagramCombination_complement_lowering {5} weight g

end ThreeCopyQutritWerner
