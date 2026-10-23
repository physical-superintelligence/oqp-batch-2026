module

public import CGLMPBounds.Defs.ScalarCirculation
public import CGLMPBounds.Defs.ScalarForm
public import CGLMPBounds.Circulation.Hodge
public import CGLMPBounds.Certificates.ScalarPartitionContinuity

@[expose] public section


/-!
# Hodge decomposition of the literal coefficient form

The complete-graph Hodge identity identifies the expanded expression with the
source coefficient form. The Hardy
partition and tilted-law identities relating this form to G_d remain separate.
-/

namespace CGLMPBounds.Circulation
noncomputable section
open scoped Matrix

theorem corr_swap (U V : Mat r) : corr V U = star (corr U V) := by
  unfold corr tr
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem corr_im_skew (U V : Mat r) : (corr U V).im = -(corr V U).im := by
  rw [corr_swap V U]
  simp

theorem fin_reverse_sub_val {d : ℕ} (i j : Fin d) (hij : i < j) :
    (i - j).val = d - (j.val - i.val) := by
  rw [Fin.coe_sub_iff_lt.mpr hij]
  omega

theorem scalar_cyclicSkew {d : ℕ} [NeZero d] (i j : Fin d) (hij : i < j) :
    cyclicSkew (fun h : Fin d => scalarIntegralError d h.val + scalarPartitionCoefficient d h.val)
      i j = scalarErrorSkew d (j.val - i.val) := by
  unfold cyclicSkew
  dsimp only
  rw [Fin.sub_val_of_le hij.le, fin_reverse_sub_val i j hij]
  have hh : j.val - i.val ≤ d := by omega
  rw [← Certificates.scalarPartitionCoefficient_reflect d (j.val - i.val) hh]
  unfold scalarErrorSkew
  ring

theorem scalarEdgeForm_error_partition_decomposition {d r : ℕ} [NeZero d]
    (V : Fin d → Mat r) :
    scalarEdgeForm (fun h => scalarIntegralError d h + scalarPartitionCoefficient d h) V =
      2 * (∑ i, ∑ j, if i < j then
        (scalarIntegralError d (j.val - i.val) + scalarPartitionCoefficient d (j.val - i.val)) *
          forbidden (V i) (V j) else 0) +
      (1 / (d : ℝ)) * ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        scalarErrorTriangle d i.val j.val k.val * circulation (V i) (V j) (V k) else 0 := by
  let e : Fin d → ℝ := fun h => scalarIntegralError d h.val + scalarPartitionCoefficient d h.val
  let z : Fin d → Fin d → ℂ := fun i j => corr (V i) (V j)
  have h := cyclic_form_decomposition e z (fun i j => corr_im_skew (V i) (V j))
  have hL : (∑ i, ∑ j, if i < j then
      e (j - i) * (1 - (z i j).re) + e (i - j) * (z i j).im else 0) =
      scalarEdgeForm (fun h => scalarIntegralError d h + scalarPartitionCoefficient d h) V := by
    unfold scalarEdgeForm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · simp only [e, z, Fin.sub_val_of_le hij.le, fin_reverse_sub_val i j hij]
    · rfl
  have hE : (∑ i, ∑ j, if i < j then
      e (j - i) * ((1 - (z i j).re + (z i j).im) / 2) else 0) =
      ∑ i, ∑ j, if i < j then
        (scalarIntegralError d (j.val - i.val) + scalarPartitionCoefficient d (j.val - i.val)) *
          forbidden (V i) (V j) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · simp only [e, z, forbidden, Fin.sub_val_of_le hij.le]
    · rfl
  have hT : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
      (cyclicSkew e i j + cyclicSkew e j k - cyclicSkew e i k) *
        ((z i j).im + (z j k).im - (z i k).im) else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        scalarErrorTriangle d i.val j.val k.val * circulation (V i) (V j) (V k) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with hij
    · change (cyclicSkew _ i j + cyclicSkew _ j k - cyclicSkew _ i k) * _ = _
      rw [scalar_cyclicSkew i j hij.1, scalar_cyclicSkew j k hij.2,
        scalar_cyclicSkew i k (lt_trans hij.1 hij.2)]
      rfl
    · rfl
  simpa only [hL, hE, hT, Fintype.card_fin] using h

theorem scalarEdgeForm_error_decomposition {d r : ℕ} [NeZero d]
    (V : Fin d → Mat r) :
    scalarEdgeForm (scalarIntegralError d) V =
      2 * (∑ i, ∑ j, if i < j then scalarIntegralError d (j.val - i.val) *
        forbidden (V i) (V j) else 0) +
      (1 / (d : ℝ)) * ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        scalarErrorTriangle d i.val j.val k.val * circulation (V i) (V j) (V k) else 0 := by
  let e : Fin d → ℝ := fun h => scalarIntegralError d h.val
  let z : Fin d → Fin d → ℂ := fun i j => corr (V i) (V j)
  have h := cyclic_form_decomposition e z (fun i j => corr_im_skew (V i) (V j))
  have hsk (i j : Fin d) (hij : i < j) :
      cyclicSkew e i j = scalarErrorSkew d (j.val - i.val) := by
    simp only [cyclicSkew, e, Fin.sub_val_of_le hij.le,
      fin_reverse_sub_val i j hij, scalarErrorSkew]
  have hL : (∑ i, ∑ j, if i < j then
      e (j - i) * (1 - (z i j).re) + e (i - j) * (z i j).im else 0) =
      scalarEdgeForm (scalarIntegralError d) V := by
    unfold scalarEdgeForm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · simp only [e, z, Fin.sub_val_of_le hij.le, fin_reverse_sub_val i j hij]
    · rfl
  have hE : (∑ i, ∑ j, if i < j then
      e (j - i) * ((1 - (z i j).re + (z i j).im) / 2) else 0) =
      ∑ i, ∑ j, if i < j then scalarIntegralError d (j.val - i.val) *
        forbidden (V i) (V j) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · simp only [e, z, forbidden, Fin.sub_val_of_le hij.le]
    · rfl
  have hT : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
      (cyclicSkew e i j + cyclicSkew e j k - cyclicSkew e i k) *
        ((z i j).im + (z j k).im - (z i k).im) else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        scalarErrorTriangle d i.val j.val k.val * circulation (V i) (V j) (V k) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with hij
    · rw [hsk i j hij.1, hsk j k hij.2, hsk i k (lt_trans hij.1 hij.2)]
      rfl
    · rfl
  simpa only [hL, hE, hT, Fintype.card_fin] using h

theorem scalarEdgeForm_add {d r : ℕ} (w v : ℕ → ℝ) (V : Fin d → Mat r) :
    scalarEdgeForm (fun h => w h + v h) V = scalarEdgeForm w V + scalarEdgeForm v V := by
  unfold scalarEdgeForm
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

end
end CGLMPBounds.Circulation
