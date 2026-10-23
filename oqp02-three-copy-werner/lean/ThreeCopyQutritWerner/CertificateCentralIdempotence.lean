module

public import ThreeCopyQutritWerner.CertificateCharacterConvolutionCases
public import ThreeCopyQutritWerner.CertificateProjector
public import ThreeCopyQutritWerner.CertificateRegisterMatrix
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.Idempotent

@[expose] public section


/-!
# Exact finite character arithmetic and central-projector idempotence

The only computed propositions are rational character convolutions on
`S₄` and `S₅`. They have respectively `24²` and `120²` summands and use
ordinary kernel `decide`, never native evaluation or an external checker.
The matrix theorem is generic in the ambient tensor dimension.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The exact `[22]` character convolution, over all permutations. -/
theorem certificateCharacter_convolution_four :
    ∀ τ : Equiv.Perm (Fin 4),
      (∑ σ : Equiv.Perm (Fin 4),
        certificateCharacter σ * certificateCharacter (σ⁻¹ * τ)) =
          12 * certificateCharacter τ := by
  intro τ
  obtain ⟨t, rfl⟩ := certificatePerm4_bijective.surjective τ
  fin_cases t
  · exact certificateCharacter_convolution4_case000_pilot
  · exact certificateCharacter_convolution4_case001
  · exact certificateCharacter_convolution4_case002
  · exact certificateCharacter_convolution4_case003
  · exact certificateCharacter_convolution4_case004
  · exact certificateCharacter_convolution4_case005
  · exact certificateCharacter_convolution4_case006
  · exact certificateCharacter_convolution4_case007
  · exact certificateCharacter_convolution4_case008
  · exact certificateCharacter_convolution4_case009
  · exact certificateCharacter_convolution4_case010
  · exact certificateCharacter_convolution4_case011
  · exact certificateCharacter_convolution4_case012
  · exact certificateCharacter_convolution4_case013
  · exact certificateCharacter_convolution4_case014
  · exact certificateCharacter_convolution4_case015
  · exact certificateCharacter_convolution4_case016
  · exact certificateCharacter_convolution4_case017
  · exact certificateCharacter_convolution4_case018
  · exact certificateCharacter_convolution4_case019
  · exact certificateCharacter_convolution4_case020
  · exact certificateCharacter_convolution4_case021
  · exact certificateCharacter_convolution4_case022
  · exact certificateCharacter_convolution4_case023

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- The exact `[32]` character convolution, over all permutations. -/
theorem certificateCharacter_convolution_five :
    ∀ τ : Equiv.Perm (Fin 5),
      (∑ σ : Equiv.Perm (Fin 5),
        certificateCharacter σ * certificateCharacter (σ⁻¹ * τ)) =
          24 * certificateCharacter τ := by
  intro τ
  obtain ⟨t, rfl⟩ := certificatePerm5_bijective.surjective τ
  fin_cases t
  · exact certificateCharacter_convolution5_case000_pilot
  · exact certificateCharacter_convolution5_case001
  · exact certificateCharacter_convolution5_case002
  · exact certificateCharacter_convolution5_case003_pilot
  · exact certificateCharacter_convolution5_case004
  · exact certificateCharacter_convolution5_case005
  · exact certificateCharacter_convolution5_case006
  · exact certificateCharacter_convolution5_case007
  · exact certificateCharacter_convolution5_case008
  · exact certificateCharacter_convolution5_case009
  · exact certificateCharacter_convolution5_case010
  · exact certificateCharacter_convolution5_case011
  · exact certificateCharacter_convolution5_case012
  · exact certificateCharacter_convolution5_case013
  · exact certificateCharacter_convolution5_case014
  · exact certificateCharacter_convolution5_case015
  · exact certificateCharacter_convolution5_case016
  · exact certificateCharacter_convolution5_case017
  · exact certificateCharacter_convolution5_case018
  · exact certificateCharacter_convolution5_case019
  · exact certificateCharacter_convolution5_case020
  · exact certificateCharacter_convolution5_case021
  · exact certificateCharacter_convolution5_case022
  · exact certificateCharacter_convolution5_case023
  · exact certificateCharacter_convolution5_case024
  · exact certificateCharacter_convolution5_case025
  · exact certificateCharacter_convolution5_case026
  · exact certificateCharacter_convolution5_case027
  · exact certificateCharacter_convolution5_case028
  · exact certificateCharacter_convolution5_case029
  · exact certificateCharacter_convolution5_case030
  · exact certificateCharacter_convolution5_case031
  · exact certificateCharacter_convolution5_case032
  · exact certificateCharacter_convolution5_case033
  · exact certificateCharacter_convolution5_case034
  · exact certificateCharacter_convolution5_case035
  · exact certificateCharacter_convolution5_case036
  · exact certificateCharacter_convolution5_case037
  · exact certificateCharacter_convolution5_case038
  · exact certificateCharacter_convolution5_case039
  · exact certificateCharacter_convolution5_case040
  · exact certificateCharacter_convolution5_case041
  · exact certificateCharacter_convolution5_case042
  · exact certificateCharacter_convolution5_case043
  · exact certificateCharacter_convolution5_case044
  · exact certificateCharacter_convolution5_case045
  · exact certificateCharacter_convolution5_case046
  · exact certificateCharacter_convolution5_case047
  · exact certificateCharacter_convolution5_case048
  · exact certificateCharacter_convolution5_case049
  · exact certificateCharacter_convolution5_case050
  · exact certificateCharacter_convolution5_case051
  · exact certificateCharacter_convolution5_case052
  · exact certificateCharacter_convolution5_case053
  · exact certificateCharacter_convolution5_case054
  · exact certificateCharacter_convolution5_case055
  · exact certificateCharacter_convolution5_case056
  · exact certificateCharacter_convolution5_case057
  · exact certificateCharacter_convolution5_case058
  · exact certificateCharacter_convolution5_case059
  · exact certificateCharacter_convolution5_case060
  · exact certificateCharacter_convolution5_case061
  · exact certificateCharacter_convolution5_case062
  · exact certificateCharacter_convolution5_case063
  · exact certificateCharacter_convolution5_case064
  · exact certificateCharacter_convolution5_case065
  · exact certificateCharacter_convolution5_case066
  · exact certificateCharacter_convolution5_case067
  · exact certificateCharacter_convolution5_case068
  · exact certificateCharacter_convolution5_case069
  · exact certificateCharacter_convolution5_case070
  · exact certificateCharacter_convolution5_case071
  · exact certificateCharacter_convolution5_case072
  · exact certificateCharacter_convolution5_case073
  · exact certificateCharacter_convolution5_case074
  · exact certificateCharacter_convolution5_case075
  · exact certificateCharacter_convolution5_case076
  · exact certificateCharacter_convolution5_case077
  · exact certificateCharacter_convolution5_case078
  · exact certificateCharacter_convolution5_case079
  · exact certificateCharacter_convolution5_case080
  · exact certificateCharacter_convolution5_case081
  · exact certificateCharacter_convolution5_case082
  · exact certificateCharacter_convolution5_case083
  · exact certificateCharacter_convolution5_case084
  · exact certificateCharacter_convolution5_case085
  · exact certificateCharacter_convolution5_case086
  · exact certificateCharacter_convolution5_case087
  · exact certificateCharacter_convolution5_case088
  · exact certificateCharacter_convolution5_case089
  · exact certificateCharacter_convolution5_case090
  · exact certificateCharacter_convolution5_case091
  · exact certificateCharacter_convolution5_case092
  · exact certificateCharacter_convolution5_case093
  · exact certificateCharacter_convolution5_case094
  · exact certificateCharacter_convolution5_case095
  · exact certificateCharacter_convolution5_case096
  · exact certificateCharacter_convolution5_case097
  · exact certificateCharacter_convolution5_case098
  · exact certificateCharacter_convolution5_case099
  · exact certificateCharacter_convolution5_case100
  · exact certificateCharacter_convolution5_case101
  · exact certificateCharacter_convolution5_case102
  · exact certificateCharacter_convolution5_case103
  · exact certificateCharacter_convolution5_case104
  · exact certificateCharacter_convolution5_case105
  · exact certificateCharacter_convolution5_case106
  · exact certificateCharacter_convolution5_case107
  · exact certificateCharacter_convolution5_case108
  · exact certificateCharacter_convolution5_case109
  · exact certificateCharacter_convolution5_case110
  · exact certificateCharacter_convolution5_case111
  · exact certificateCharacter_convolution5_case112
  · exact certificateCharacter_convolution5_case113
  · exact certificateCharacter_convolution5_case114
  · exact certificateCharacter_convolution5_case115
  · exact certificateCharacter_convolution5_case116
  · exact certificateCharacter_convolution5_case117
  · exact certificateCharacter_convolution5_case118
  · exact certificateCharacter_convolution5_case119

/-- Relabeling the registers does not change the number of fixed registers. -/
theorem certificateFixedCount_conj {k : ℕ} (σ τ : Equiv.Perm (Fin k)) :
    certificateFixedCount (τ * σ * τ⁻¹) = certificateFixedCount σ := by
  unfold certificateFixedCount
  refine Fintype.sum_equiv τ.symm _ _ ?_
  intro i
  simp only [Equiv.Perm.mul_apply]
  simp only [← τ.eq_symm_apply]
  rfl

/-- Appendix B's coefficient is a class function on the full permutation group. -/
theorem certificateCharacter_conj {k : ℕ} (σ τ : Equiv.Perm (Fin k)) :
    certificateCharacter (τ * σ * τ⁻¹) = certificateCharacter σ := by
  have hsquare : (τ * σ * τ⁻¹) * (τ * σ * τ⁻¹) = τ * (σ * σ) * τ⁻¹ := by group
  simp only [certificateCharacter, hsquare, certificateFixedCount_conj]

/-- The full character matrix commutes with every whole-register permutation. -/
theorem certificateCentralMatrix_commutes_register {k : ℕ} {n : Type*}
    [Fintype n] [DecidableEq n] (d : ℚ) (τ : Equiv.Perm (Fin k)) :
    certificateCentralMatrix d * (certificateRegisterPerm (n := n) τ).permMatrix ℂ =
      (certificateRegisterPerm τ).permMatrix ℂ * certificateCentralMatrix d := by
  let e : Equiv.Perm (Equiv.Perm (Fin k)) :=
    { toFun := fun σ => τ⁻¹ * σ * τ
      invFun := fun σ => τ * σ * τ⁻¹
      left_inv := by intro σ; group
      right_inv := by intro σ; group }
  unfold certificateCentralMatrix
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    certificateRegisterMatrix_mul]
  refine Fintype.sum_equiv e _ _ ?_
  intro σ
  change ((certificateCharacter σ / d : ℚ) : ℂ) •
      (certificateRegisterPerm (σ * τ)).permMatrix ℂ =
    ((certificateCharacter (τ⁻¹ * σ * τ) / d : ℚ) : ℂ) •
      (certificateRegisterPerm (τ * (τ⁻¹ * σ * τ))).permMatrix ℂ
  have hchar : certificateCharacter (τ⁻¹ * σ * τ) = certificateCharacter σ := by
    simpa only [inv_inv] using certificateCharacter_conj σ τ⁻¹
  have hm : τ * (τ⁻¹ * σ * τ) = σ * τ := by group
  rw [hchar, hm]

/-- Consequently the character matrix commutes with each minor antisymmetrizer. -/
theorem certificateCentralMatrix_commutes_antisym {k : ℕ} {n : Type*}
    [Fintype n] [DecidableEq n] (d : ℚ) (i j : Fin k) :
    certificateCentralMatrix d * certificateRegisterAntisym (n := n) i j =
      certificateRegisterAntisym i j * certificateCentralMatrix d := by
  simp only [certificateRegisterAntisym, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    certificateCentralMatrix_commutes_register]

/-- The finite convolution identity implies idempotence in any matrix representation. -/
theorem certificate_matrix_sum_idempotent {G n : Type*} [Group G] [Fintype G]
    [Fintype n] [DecidableEq n] (A : G → Matrix n n ℂ) (w : G → ℂ)
    (hA : ∀ σ τ, A σ * A τ = A (σ * τ))
    (hw : ∀ τ, (∑ σ, w σ * w (σ⁻¹ * τ)) = w τ) :
    (∑ σ, w σ • A σ) * (∑ σ, w σ • A σ) = ∑ σ, w σ • A σ := by
  have hprod : ∀ σ τ, (w σ • A σ) * (w τ • A τ) =
      (w σ * w τ) • A (σ * τ) := by
    intro σ τ
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, hprod]
  have hre : ∀ σ : G,
      (∑ τ : G, (w σ * w τ) • A (σ * τ)) =
        ∑ τ : G, (w σ * w (σ⁻¹ * τ)) • A τ := by
    intro σ
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_
    intro τ
    simp
  simp_rw [hre]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← Finset.sum_smul, hw]

/-- Normalize a rational character convolution to the matrix coefficient convolution. -/
theorem certificate_normalized_character_convolution {k : ℕ} (d : ℚ) (hd : d ≠ 0)
    (hconv : ∀ τ : Equiv.Perm (Fin k),
      (∑ σ : Equiv.Perm (Fin k),
        certificateCharacter σ * certificateCharacter (σ⁻¹ * τ)) =
          d * certificateCharacter τ)
    (τ : Equiv.Perm (Fin k)) :
    (∑ σ : Equiv.Perm (Fin k),
      ((certificateCharacter σ / d : ℚ) : ℂ) *
        ((certificateCharacter (σ⁻¹ * τ) / d : ℚ) : ℂ)) =
      ((certificateCharacter τ / d : ℚ) : ℂ) := by
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hconvC : (∑ σ : Equiv.Perm (Fin k),
      (certificateCharacter σ : ℂ) * (certificateCharacter (σ⁻¹ * τ) : ℂ)) =
        (d : ℂ) * (certificateCharacter τ : ℂ) := by exact_mod_cast hconv τ
  calc
    _ = (∑ σ : Equiv.Perm (Fin k),
        (certificateCharacter σ : ℂ) * (certificateCharacter (σ⁻¹ * τ) : ℂ)) /
          (d : ℂ) ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro σ _
      push_cast
      ring
    _ = _ := by
      rw [hconvC]
      push_cast
      field_simp
      <;> ring

/-- The literal `[22]` central character matrix is idempotent. -/
theorem certificateCentralMatrix_four_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateCentralMatrix (k := 4) (n := n) 12 * certificateCentralMatrix 12 =
      certificateCentralMatrix 12 := by
  apply certificate_matrix_sum_idempotent
  · exact certificateRegisterMatrix_mul
  · exact certificate_normalized_character_convolution 12 (by norm_num)
      certificateCharacter_convolution_four

/-- The literal `[32]` central character matrix is idempotent. -/
theorem certificateCentralMatrix_five_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateCentralMatrix (k := 5) (n := n) 24 * certificateCentralMatrix 24 =
      certificateCentralMatrix 24 := by
  apply certificate_matrix_sum_idempotent
  · exact certificateRegisterMatrix_mul
  · exact certificate_normalized_character_convolution 24 (by norm_num)
      certificateCharacter_convolution_five

/-- Each minor antisymmetrizer is a projector, including the degenerate `i=j` case. -/
theorem certificateRegisterAntisym_idempotent {k : ℕ} {n : Type*}
    [Fintype n] [DecidableEq n] (i j : Fin k) :
    certificateRegisterAntisym (n := n) i j * certificateRegisterAntisym i j =
      certificateRegisterAntisym i j := by
  have hs : (Equiv.swap i j : Equiv.Perm (Fin k)) * Equiv.swap i j = 1 := by
    ext x
    simp [Equiv.Perm.mul_apply]
  have hF : (certificateRegisterPerm (n := n) (Equiv.swap i j)).permMatrix ℂ *
      (certificateRegisterPerm (Equiv.swap i j)).permMatrix ℂ = 1 := by
    rw [certificateRegisterMatrix_mul, hs, certificateRegisterMatrix_one]
  simp only [certificateRegisterAntisym, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hF]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The disjoint minor-pair projectors commute. -/
theorem certificateRegisterAntisym₁₂_commutes₃₄ {n : Type*} [Fintype n] [DecidableEq n] :
    certificateRegisterAntisym (n := n) (1 : Fin 5) 2 * certificateRegisterAntisym 3 4 =
      certificateRegisterAntisym 3 4 * certificateRegisterAntisym 1 2 := by
  have hs : (Equiv.swap (1 : Fin 5) 2) * Equiv.swap 3 4 =
      (Equiv.swap 3 4) * Equiv.swap 1 2 := by decide
  have hF : (certificateRegisterPerm (n := n) (Equiv.swap (1 : Fin 5) 2)).permMatrix ℂ *
        (certificateRegisterPerm (Equiv.swap 3 4)).permMatrix ℂ =
      (certificateRegisterPerm (Equiv.swap 3 4)).permMatrix ℂ *
        (certificateRegisterPerm (Equiv.swap 1 2)).permMatrix ℂ := by
    rw [certificateRegisterMatrix_mul, certificateRegisterMatrix_mul, hs]
  simp only [certificateRegisterAntisym, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hF]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The Hermitian sandwich is literally the manuscript's `E_[32] A₁₂ A₃₄`. -/
theorem certificateHolomorphicCarrier_eq {n : Type*} [Fintype n] [DecidableEq n] :
    certificateHolomorphicCarrier (n := n) =
      certificateCentralMatrix 24 * certificateRegisterAntisym (1 : Fin 5) 2 *
        certificateRegisterAntisym 3 4 := by
  let P := certificateRegisterAntisym (n := n) (1 : Fin 5) 2
  let R := certificateRegisterAntisym (n := n) (3 : Fin 5) 4
  let E : Matrix (Fin 5 → n) (Fin 5 → n) ℂ := certificateCentralMatrix 24
  have hPR : Commute P R := certificateRegisterAntisym₁₂_commutes₃₄
  have hPE : Commute P E := (certificateCentralMatrix_commutes_antisym 24 1 2).symm
  have hRE : Commute R E := (certificateCentralMatrix_commutes_antisym 24 3 4).symm
  have hQ : IsIdempotentElem (P * R) := IsIdempotentElem.mul_of_commute hPR
    (certificateRegisterAntisym_idempotent 1 2) (certificateRegisterAntisym_idempotent 3 4)
  change P * R * E * R * P = E * P * R
  calc
    P * R * E * R * P = (P * R * E) * (P * R) := by
      rw [Matrix.mul_assoc (P * R * E), ← hPR.eq]
    _ = (E * (P * R)) * (P * R) := by rw [(hPE.mul_left hRE).eq]
    _ = E * ((P * R) * (P * R)) := Matrix.mul_assoc _ _ _
    _ = E * (P * R) := by rw [hQ.eq]
    _ = E * P * R := (Matrix.mul_assoc _ _ _).symm

/-- The concrete holomorphic carrier is an idempotent Hermitian matrix. -/
theorem certificateHolomorphicCarrier_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateHolomorphicCarrier (n := n) * certificateHolomorphicCarrier =
      certificateHolomorphicCarrier := by
  let P := certificateRegisterAntisym (n := n) (1 : Fin 5) 2
  let R := certificateRegisterAntisym (n := n) (3 : Fin 5) 4
  let E : Matrix (Fin 5 → n) (Fin 5 → n) ℂ := certificateCentralMatrix 24
  have hPR : Commute P R := certificateRegisterAntisym₁₂_commutes₃₄
  have hEP : Commute E P := certificateCentralMatrix_commutes_antisym 24 1 2
  have hER : Commute E R := certificateCentralMatrix_commutes_antisym 24 3 4
  have hQ : IsIdempotentElem (P * R) := IsIdempotentElem.mul_of_commute hPR
    (certificateRegisterAntisym_idempotent 1 2) (certificateRegisterAntisym_idempotent 3 4)
  have hEQ : IsIdempotentElem (E * (P * R)) := IsIdempotentElem.mul_of_commute
    (hEP.mul_right hER) certificateCentralMatrix_five_idempotent hQ
  simpa only [certificateHolomorphicCarrier_eq, Matrix.mul_assoc] using hEQ.eq

/-- The six-register matrix in the endpoint reduction is therefore an actual projector. -/
theorem certificateQutritCarrier_idempotent :
    certificateQutritCarrier * certificateQutritCarrier = certificateQutritCarrier := by
  unfold certificateQutritCarrier
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    certificateHolomorphicCarrier_idempotent, Matrix.one_mul]

end ThreeCopyQutritWerner
