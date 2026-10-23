module

public import CGLMPBounds.Circulation.TriangleCoercivity
public import CGLMPBounds.Circulation.Spectral
public import CGLMPBounds.Certificates.ScalarSortedTriangle

@[expose] public section


/-!
# The coercive bound for the actual scalar edge and triangle coefficients

All coefficient and fourth-root hypotheses of the finite assembly lemma are
proved here. This is the coercivity of the expanded D.13 expression; identifying
it with L_(e+s) and the tilted Hardy partition form are separate obligations.
-/

namespace CGLMPBounds.Circulation
noncomputable section
open scoped Matrix

theorem scalar_expanded_coercivity {d r : ℕ} [NeZero r] (hd : 3 ≤ d)
    (V : Fin d → Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1) :
    (1 / (3 * ((d : ℝ) + 1))) *
        (∑ i, ∑ j, if i < j then forbidden (V i) (V j) else 0) ≤
      2 * (∑ i, ∑ j, if i < j then
        (scalarIntegralError d (j.val - i.val) + scalarPartitionCoefficient d (j.val - i.val)) *
          forbidden (V i) (V j) else 0) +
      (1 / (d : ℝ)) * ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        scalarErrorTriangle d i.val j.val k.val * circulation (V i) (V j) (V k) else 0 := by
  have hp (i j : Fin d) (_ : i < j) : 0 ≤ forbidden (V i) (V j) :=
    fourth_root_forbidden_nonneg (V i) (V j) (hunit i) (hunit j) (hfour i) (hfour j)
  have hC (i j k : Fin d) (_ : i < j) (_ : j < k) :
      |circulation (V i) (V j) (V k)| ≤
        5 * (forbidden (V i) (V j) + forbidden (V j) (V k) + forbidden (V i) (V k)) :=
    fourth_root_circulation_bound (V i) (V j) (V k)
      (hunit i) (hunit j) (hunit k) (hfour i) (hfour j) (hfour k)
  have ha (i j k : Fin d) (hij : i < j) (hjk : j < k) :=
    fun h (hh0 : 0 < h) (hhd : h < d) =>
      Certificates.scalar_sorted_triangle_margin d h i.val j.val k.val hd
        hh0 hhd hij hjk k.isLt
  have h := finite_triangle_coercivity (ι := Fin d) (by simpa using hd)
    (fun i j => forbidden (V i) (V j))
    (fun i j => scalarIntegralError d (j.val - i.val) + scalarPartitionCoefficient d (j.val - i.val))
    (fun i j k => scalarErrorTriangle d i.val j.val k.val)
    (fun i j k => circulation (V i) (V j) (V k))
    (1 / (6 * ((d : ℝ) + 1))) hp hC (by
      intro i j k hij hjk
      simp only [Fintype.card_fin]
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have hij' : i.val < j.val := hij
      have hjk' : j.val < k.val := hjk
      exact ⟨ha i j k hij hjk (j.val - i.val) (by omega) (by omega),
        ha i j k hij hjk (k.val - j.val) (by omega) (by omega),
        ha i j k hij hjk (k.val - i.val) (by omega) (by omega)⟩)
  simp only [Fintype.card_fin] at h
  have hc : 2 * (1 / (6 * ((d : ℝ) + 1))) = 1 / (3 * ((d : ℝ) + 1)) := by
    field_simp [show (d : ℝ) + 1 ≠ 0 by positivity]
    <;> ring
  rw [hc] at h
  exact h

end
end CGLMPBounds.Circulation
