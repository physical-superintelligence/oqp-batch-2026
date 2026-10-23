module

public import CGLMPBounds.Partition.ConditionalMatrixHardyInput
public import CGLMPBounds.CGLMP.DimensionDeficitBellBridge
public import CGLMPBounds.CGLMP.RectangularStandardValue
public import CGLMPBounds.Companion.FiniteStandardization

@[expose] public section


/-! Assembly of the global A.1 bound and its exact classification from the
general matrix Hardy bound C.6, which is a hypothesis here (`hC6`).
`CGLMP/ProjectiveOptimality.lean` discharges it with the proved
`Hardy.fourth_root_matrix_Hardy_bound`, giving A.1 without hypotheses. -/

namespace CGLMPBounds
open MeasureTheory Matrix
open scoped Kronecker
noncomputable section

lemma companionFinite_forbidden_nonneg {d n : ℕ} [NeZero n]
    (V : CompanionFinite.Tuple d n)
    (hfour : ∀ j, (V j : CompanionFinite.MultiplicityMat n)^4=1) :
    0 ≤ scalarForbiddenTotal (fun j => (V j : CompanionFinite.MultiplicityMat n)) := by
  letI : NeZero (4*n) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne n)⟩
  unfold scalarForbiddenTotal
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact Circulation.fourth_root_forbidden_nonneg _ _
      (V i).property.1 (V j).property.1 (hfour i) (hfour j)
  · exact le_rfl

variable (hC6 : ∀ {r : ℕ}, 0 < r → ∀ U : ℝ → Circulation.Mat r,
  AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)) →
  (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) →
  (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
    U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
      (1 : Circulation.Mat r)) →
  Partition.sourceFourthRootHardyConstant ≤ Partition.matrixNegativeFourierEnergy U)
include hC6

theorem companion_forbidden_le_bell_deficit_of_matrixHardy_input
    {d n : ℕ} [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (V : CompanionFinite.Tuple d n)
    (hfour : ∀ j, (V j : CompanionFinite.MultiplicityMat n)^4=1)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (hgap : cglmpFourierValue d-cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) =
      (8*(d : ℝ)/((d : ℝ)-1))*CompanionFinite.gap V) :
    scalarForbiddenTotal (fun j => (V j : CompanionFinite.MultiplicityMat n)) ≤
      (3/4 : ℝ)*(d : ℝ)*((d : ℝ)-1)*((d : ℝ)+1) *
        (cglmpFourierValue d-cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3])) := by
  have hr : 0 < 4*n := Nat.mul_pos (by omega) (NeZero.pos n)
  apply companion_forbidden_le_bell_deficit_of_C6_input hd V hfour P hgap
  exact Filter.Eventually.of_forall (fun T =>
    Partition.circularPartitionHardyAverage_nonneg_of_matrixHardy_input (by omega) hr
      (hC6 hr) (fun j => (V j : Circulation.Mat (4*n)))
      (fun j => (V j).property.1) hfour T)

theorem cglmp_projective_bound_of_matrixHardy_input {d n : ℕ}
    [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, IsPVM (P t)) :
    cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) ≤ cglmpFourierValue d := by
  obtain ⟨V, hfour, hgap, _⟩ := Companion.exists_companion_finite hd (NeZero.pos n) P hP
  have hF := companionFinite_forbidden_nonneg V hfour
  have h := companion_forbidden_le_bell_deficit_of_matrixHardy_input hC6 hd V hfour P hgap
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hc : 0 < (3/4 : ℝ)*(d : ℝ)*((d : ℝ)-1)*((d : ℝ)+1) := by positivity
  by_contra hbad
  have hneg := mul_neg_of_pos_of_neg hc (sub_neg.mpr (lt_of_not_ge hbad))
  linarith

theorem cglmp_eq_fourier_iff_standard_of_matrixHardy_input {d n : ℕ}
    [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, IsPVM (P t)) :
    cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) = cglmpFourierValue d ↔
      ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
        n = d*k ∧ U*Uᴴ=1 ∧ Uᴴ*U=1 ∧
        ∀ (t : Fin 4) (a : ZMod d), P t a =
          U * (fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ := by
  constructor
  · intro heq
    obtain ⟨V, hfour, hgap, _, _, Z, hZ, hinter, hcomm⟩ :=
      Companion.exists_companion_finite hd (NeZero.pos n) P hP
    have h := companion_forbidden_le_bell_deficit_of_matrixHardy_input hC6 hd V hfour P hgap
    rw [heq, sub_self, mul_zero] at h
    have hzero := le_antisymm h (companionFinite_forbidden_nonneg V hfour)
    exact Companion.finite_reducing_standard_of_forbidden_zero P V hfour hzero Z hZ hinter hcomm
  · rintro ⟨k, U, hdim, _, hU, hstd⟩
    rw [tracialTable_of_rectangular_standard P U hdim hU hstd]
    exact cglmp_fourierTable d hd

end
end CGLMPBounds
