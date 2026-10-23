module

public import ThreeCopyQutritWerner.CertificateX2InputSegA
public import ThreeCopyQutritWerner.CertificateX2InputLab

@[expose] public section


/-!
# Input stage: A segments assembled from run chunks

A gather segment of the A-pipeline input table checked in ONE kernel declaration costs far more than the
sum of its runs (A2, segment (4, 4) of a type-5 column: ~700 s for 105 runs, against about 1 s per five runs),
so the heavy segments are checked in chunks of runs and assembled here: `segOKA_gR*`/`segOKA_gP*` identify a
segment with its gather branch, `gatherRowsOKA_of`/`gatherPosOKA_of` rebuild the branch from per-run facts,
which come from chunk checks through `rangeAll_sound`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner
namespace X2

/-- One run of `gatherRowsOKA`. -/
def gRrun (Fs : List ℕ) (rows : List (List ℕ)) (pos ov ou nu k : ℕ) : Bool :=
  Nat.beq (rows.getD k []).length nu && Nat.beq (runAtA Fs (ov + k) ou nu) (gatherRun (rows.getD k []) pos)

/-- One run of `gatherPosOKA`. -/
def gPrun (Fs : List ℕ) (row : List ℕ) (posf : ℕ → ℕ) (ov ou nu k : ℕ) : Bool :=
  Nat.beq (runAtA Fs (ov + k) ou nu) (gatherRun row (posf k))

theorem gatherRowsOKA_of (Fs : List ℕ) (rows : List (List ℕ)) (pos ov nv ou nu : ℕ) (hlen : rows.length = nv)
    (h : ∀ k < nv, gRrun Fs rows pos ov ou nu k = true) : gatherRowsOKA Fs rows pos ov nv ou nu = true := by
  unfold gatherRowsOKA
  rw [Bool.and_eq_true]
  refine ⟨by rw [hlen]; exact Nat.beq_refl nv, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  have hk' : k < nv := by
    rw [List.length_zip, List.length_range, hlen, Nat.min_self] at hk
    exact hk
  have hr := h k hk'
  unfold gRrun at hr
  rw [List.getD_eq_getElem _ _ (by omega)] at hr
  rw [← hpk]
  simp only [List.getElem_zip, List.getElem_range]
  exact hr

theorem gatherPosOKA_of (Fs : List ℕ) (row : List ℕ) (posf : ℕ → ℕ) (ov nv ou nu : ℕ) (hlen : row.length = nu)
    (h : ∀ k < nv, gPrun Fs row posf ov ou nu k = true) : gatherPosOKA Fs row posf ov nv ou nu = true := by
  unfold gatherPosOKA
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨by rw [hlen]; exact Nat.beq_refl nu, fun k hk => h k (List.mem_range.mp hk)⟩

/-- Segment `(c, u, v)` in the branch "ASA rows" (`TCasa v u w`). -/
theorem segOKA_gRC (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (Fs : List ℕ) (c : ℕ) (u v w : Fin 8) (hw : typeA s c = w)
    (h1 : ¬ (w ≤ u ∧ v ≤ u)) (h2 : ¬ (u < w ∧ u < v)) (h3 : v ≤ w) (hz : Zd v u w = false) :
    segOKA s TTaas TCaas TTsaa TCasa Zd Fs c u v =
      gatherRowsOKA Fs (TCasa v u w) (posA (x2Mult s w) (c - x2AOff s w)) (x2AOff s v) (nA s v) (x2SOff s u)
        (nS s u) := by
  unfold segOKA
  rw [hw]
  unfold segOKwA
  rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by simp [hz])]

/-- Segment `(c, u, v)` in the branch "SAA rows" (`TTsaa u v w`). -/
theorem segOKA_gRT (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (Fs : List ℕ) (c : ℕ) (u v w : Fin 8) (hw : typeA s c = w)
    (h1 : ¬ (w ≤ u ∧ v ≤ u)) (h2 : u < w ∧ u < v) (h3 : v ≤ w) (hz : Zd u v w = false) :
    segOKA s TTaas TCaas TTsaa TCasa Zd Fs c u v =
      gatherRowsOKA Fs (TTsaa u v w) (posA (x2Mult s w) (c - x2AOff s w)) (x2AOff s v) (nA s v) (x2SOff s u)
        (nS s u) := by
  unfold segOKA
  rw [hw]
  unfold segOKwA
  rw [if_neg h1, if_pos h2, if_pos h3, if_neg (by simp [hz])]

/-- Segment `(c, u, v)` in the branch "SAA positions" (row `c'` of `TTsaa u w v`). -/
theorem segOKA_gPT (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (Fs : List ℕ) (c : ℕ) (u v w : Fin 8) (hw : typeA s c = w)
    (h1 : ¬ (w ≤ u ∧ v ≤ u)) (h2 : u < w ∧ u < v) (h3 : ¬ v ≤ w) (hz : Zd u w v = false) :
    segOKA s TTaas TCaas TTsaa TCasa Zd Fs c u v =
      gatherPosOKA Fs ((TTsaa u w v).getD (c - x2AOff s w) []) (posA (x2Mult s v)) (x2AOff s v) (nA s v)
        (x2SOff s u) (nS s u) := by
  unfold segOKA
  rw [hw]
  unfold segOKwA
  rw [if_neg h1, if_pos h2, if_neg h3, if_neg (by simp [hz])]

/-- Segment `(c, u, v)` in the branch "ASA positions" (row `c'` of `TCasa w u v`). -/
theorem segOKA_gPC (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (Fs : List ℕ) (c : ℕ) (u v w : Fin 8) (hw : typeA s c = w)
    (h1 : ¬ (w ≤ u ∧ v ≤ u)) (h2 : ¬ (u < w ∧ u < v)) (h3 : ¬ v ≤ w) (hz : Zd w u v = false) :
    segOKA s TTaas TCaas TTsaa TCasa Zd Fs c u v =
      gatherPosOKA Fs ((TCasa w u v).getD (c - x2AOff s w) []) (posA (x2Mult s v)) (x2AOff s v) (nA s v)
        (x2SOff s u) (nS s u) := by
  unfold segOKA
  rw [hw]
  unfold segOKwA
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg (by simp [hz])]

end X2
end ThreeCopyQutritWerner
