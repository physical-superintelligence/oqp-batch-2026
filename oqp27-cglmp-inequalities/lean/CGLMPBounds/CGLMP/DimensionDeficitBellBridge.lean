module

public import CGLMPBounds.Partition.ConditionalCoercivity
public import CGLMPBounds.Companion.FiniteDefinitions

@[expose] public section


/-!
# Internal exact E.5 coefficient assembly, conditional on C.6

The finite tuple, its actual normalized gap, and the literal Bell deficit are
retained. The matrix Hardy input C.6 enters as the premise `hC6`.
-/

namespace CGLMPBounds
noncomputable section
open MeasureTheory
open scoped Matrix

lemma companionFinite_gap_eq_scalarEdgeForm {d n : ℕ} [NeZero d]
    (V : CompanionFinite.Tuple d n) :
    CompanionFinite.gap V = scalarEdgeForm
      (fun h => scalarSecant ((h : ℝ)/d)/(2*(d : ℝ)^2))
      (fun j => (V j : Circulation.Mat (4*n))) := by
  unfold CompanionFinite.gap scalarEdgeForm
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij]
    have hn : d-(j.val-i.val) = d-j.val+i.val := by
      have := i.isLt
      have := j.isLt
      have hij' : i.val < j.val := hij
      omega
    have hc : CompanionFinite.correlation V i j =
        Circulation.corr (V i : Circulation.Mat (4*n)) (V j) := rfl
    rw [hc, hn]
    unfold scalarSecant
    have harg (m : ℕ) : Real.pi*((m : ℝ)/(d : ℝ))/2 =
        Real.pi*(m : ℝ)/(2*(d : ℝ)) := by ring
    rw [harg, harg]
    ring
  · simp only [if_neg hij, zero_div]

/-- The actual E.5 constant, still conditional on the explicit unresolved C.6 input. -/
theorem companion_forbidden_le_bell_deficit_of_C6_input
    {d n : ℕ} [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (V : CompanionFinite.Tuple d n)
    (hfour : ∀ j, (V j : CompanionFinite.MultiplicityMat n)^4=1)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (hgap : cglmpFourierValue d-cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) =
      (8*(d : ℝ)/((d : ℝ)-1))*CompanionFinite.gap V)
    (hC6 : ∀ᵐ T ∂Partition.boundaryProductMeasure d,
      0 ≤ Partition.circularPartitionHardyAverage (by omega : 0 < d)
        (fun j => (V j : Circulation.Mat (4*n))) T) :
    scalarForbiddenTotal (fun j => (V j : Circulation.Mat (4*n))) ≤
      (3/4 : ℝ)*(d : ℝ)*((d : ℝ)-1)*((d : ℝ)+1) *
        (cglmpFourierValue d-cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3])) := by
  letI : NeZero (4*n) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne n)⟩
  have hunit (j : Fin d) : (V j : Circulation.Mat (4*n))ᴴ * V j = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (V j).property
  have h := Partition.scalar_forbidden_lower_of_C6_input hd
    (fun j => (V j : Circulation.Mat (4*n))) hunit hfour hC6
  rw [← companionFinite_gap_eq_scalarEdgeForm] at h
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 6*(d : ℝ)^2*((d : ℝ)+1) := by positivity
  rw [div_le_iff₀ hden] at h
  rw [hgap]
  have he : (3/4 : ℝ)*(d : ℝ)*((d : ℝ)-1)*((d : ℝ)+1) *
      ((8*(d : ℝ)/((d : ℝ)-1))*CompanionFinite.gap V) =
      CompanionFinite.gap V * (6*(d : ℝ)^2*((d : ℝ)+1)) := by
    have hn : (d : ℝ)-1 ≠ 0 := by linarith
    field_simp [hn]
    <;> ring
  rw [he]
  exact h

end
end CGLMPBounds
