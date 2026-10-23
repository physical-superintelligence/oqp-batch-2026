module

public import CGLMPBounds.Partition.CircularTriangleIdentity
public import CGLMPBounds.Partition.MatrixScalarBranch

@[expose] public section


/-! The all-identity circular assignment is an actual scalar cut, including
coincident boundaries. Its actual Fourier gap and its triangle integral
vanish; this supplies the scalar subtraction used in D.3. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section

lemma boundaryArcCount_monotone_length (d : ℕ) (origin : ℝ) (T : Fin d → ℝ) :
    Monotone (fun t => boundaryArcCount d origin t T) := by
  intro s t hst
  unfold boundaryArcCount
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans_le hst

/-- A bounded monotone count has a genuine cut point for each positive
threshold. Only the single cut point is excluded; no sorting or distinct
boundary premise is needed. -/
lemma boundaryArcCount_threshold_cut (d : ℕ) (T : Fin d → ℝ)
    (k : ℕ) (hk : 0 < k) :
    ∃ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, t ≠ u →
      (boundaryArcCount d 0 t T < k ↔ t < u) := by
  let A : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ boundaryArcCount d 0 t T < k}
  have hzero : boundaryArcCount d 0 0 T = 0 := by
    have hf : Finset.univ.filter (fun j : Fin d => Int.fract (T j - 0) < 0) = ∅ := by
      ext j
      simp [not_lt.mpr (Int.fract_nonneg (T j))]
    simp only [boundaryArcCount, hf, Finset.card_empty]
  have hz : (0 : ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, by rwa [hzero]⟩
  have hne : A.Nonempty := ⟨0, hz⟩
  have hbd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  refine ⟨sSup A, ⟨le_csSup hbd hz, csSup_le hne (fun t ht => ht.1.2)⟩, ?_⟩
  intro t ht htu
  constructor
  · intro hcount
    exact lt_of_le_of_ne (le_csSup hbd ⟨ht, hcount⟩) htu
  · intro hlt
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne hlt
    exact (boundaryArcCount_monotone_length d 0 T hts.le).trans_lt hs.2

theorem circular_identity_assignment_is_scalar_cut {d r : ℕ} (hd : 0 < d)
    (a : Fin d) (T : Fin d → ℝ) :
    ∃ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, t ≠ u →
      circularAssignmentBranch hd (fun _ => (1 : Circulation.Mat r)) a T t =
        sourceScalarCutBranch 0 u t • (1 : Circulation.Mat r) := by
  obtain ⟨u, hu, hcut⟩ := boundaryArcCount_threshold_cut d T (d - a.val) (by omega)
  refine ⟨u, hu, ?_⟩
  intro t ht htu
  have hbound := boundaryArcCount_le d 0 t T
  by_cases htu' : t < u
  · have hcount := (hcut t ht htu).mpr htu'
    have hlt : a.val + boundaryArcCount d 0 t T < d := by omega
    simp [circularAssignmentBranch, circularAssignmentStep, Nat.div_eq_of_lt hlt,
      sourceScalarCutBranch, not_lt.mpr htu'.le]
  · have hut : u < t := lt_of_le_of_ne (le_of_not_gt htu') (Ne.symm htu)
    have hcount : d - a.val ≤ boundaryArcCount d 0 t T := by
      apply Nat.le_of_not_gt
      exact fun hn => htu' ((hcut t ht htu).mp hn)
    have hdiv : (a.val + boundaryArcCount d 0 t T) / d = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    simp [circularAssignmentBranch, circularAssignmentStep, hdiv,
      sourceScalarCutBranch, hut, Matrix.conjTranspose_smul, smul_smul,
      Complex.star_def]

theorem circular_identity_assignment_negative_energy {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (a : Fin d) (T : Fin d → ℝ) :
    matrixNegativeFourierEnergy
      (circularAssignmentBranch hd (fun _ => (1 : Circulation.Mat r)) a T) =
      sourceFourthRootHardyConstant := by
  letI : ENormedAddMonoid (Circulation.Mat r) :=
    inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))
  obtain ⟨u, hu, he⟩ := circular_identity_assignment_is_scalar_cut (r := r) hd a T
  have hcoef (n : ℕ) :
      matrixNegativeFourierCoefficient
        (circularAssignmentBranch hd (fun _ => (1 : Circulation.Mat r)) a T) n =
      matrixNegativeFourierCoefficient (fun t => sourceScalarCutBranch 0 u t •
        (1 : Circulation.Mat r)) n := by
    unfold matrixNegativeFourierCoefficient
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne u] with t htu ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [he t ⟨ht.1.le, ht.2⟩ htu]
  have henergy : matrixNegativeFourierEnergy
      (circularAssignmentBranch hd (fun _ => (1 : Circulation.Mat r)) a T) =
      matrixNegativeFourierEnergy (fun t => sourceScalarCutBranch 0 u t •
        (1 : Circulation.Mat r)) := by
    unfold matrixNegativeFourierEnergy
    simp_rw [hcoef]
  rw [henergy]
  exact sourceScalarCutBranch_matrix_negative_energy hr 1 (by simp) 0 u hu

/-- The scalar contribution subtracted in D.3 is the actual zero-gap
all-identity circular assignment, not an assumed normalization. -/
theorem circular_identity_assignment_pair_integral_zero {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (a : Fin d) (T : Fin d → ℝ) :
    (∫ p : ℝ × ℝ,
      stepPairIntegrand (circularAssignmentStep hd (fun _ => (1 : Circulation.Mat r)) a T) p
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) = 0 := by
  have h := circularAssignmentBranch_hardyGap_eq_triangle hd hr
    (fun _ => (1 : Circulation.Mat r)) (fun _ => by simp) a T
  rw [circular_identity_assignment_negative_energy hd hr a T, sub_self] at h
  linarith

end
end CGLMPBounds.Partition
