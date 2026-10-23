module

public import ThreeCopyQutritWerner.CertificateX2InputLab

@[expose] public section


/-!
# Input stage: the A pipelines (mixed parity), generically

`σ · x2EmbedA` (one symmetric site, two antisymmetric sites) at the labels of a sorted type triple
`t₀ ≤ t₁ ≤ t₂`, from the same stored blocks as the S pipeline, in the three canonical arrangements of
x2EmbedA_eight0/1/2 (the last site keeps its orientation):
* AAS (A label of type `t₀`, A label of type `t₁`, S label of type `t₂`): T-blocks over the S labels of `t₂`,
  signs `(+, -, -, +)` (`tCellG … 6 2 2 6`);
* SAA (S label of type `t₀`, A labels of types `t₁`, `t₂`): T-blocks over the full upper triangle of `t₂`, read at
  the positions `posA` of the A pairs, signs `(+, +, -, -)`;
* ASA (A label of type `t₀`, S label of type `t₁`, A label of type `t₂`): the same, signs `(+, -, +, -)`.
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000
set_option maxHeartbeats 0

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### A labels -/

/-- Number of A labels of a type. -/
def nA (s : Fin 3) (u : Fin 8) : ℕ := x2Mult s u * (x2Mult s u - 1) / 2

/-- The `i`-th A label of type `u` (`i < nA s u`). -/
def alab (s : Fin 3) (u : Fin 8) (i : ℕ) : Fin 231 := ⟨(x2AOff s u + i) % 231, Nat.mod_lt _ (by norm_num)⟩

/-- The pairs `a < b < m` in row-major order. -/
def pairsA (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap (fun a => (List.range (m - a - 1)).map (fun d => (a, a + 1 + d)))

def pairsAOK (m : ℕ) : Prop :=
  (pairsA m).length = m * (m - 1) / 2 ∧
    ∀ e < m * (m - 1) / 2, ((pairsA m).getD e (0, 0)).1 < ((pairsA m).getD e (0, 0)).2 ∧
      ((pairsA m).getD e (0, 0)).2 < m ∧
      upos m ((pairsA m).getD e (0, 0)).1 ((pairsA m).getD e (0, 0)).2 < m * (m + 1) / 2

def labelsAOK (s : Fin 3) : Prop :=
  ∀ u : Fin 8, ∀ i < nA s u, x2ALabel s (alab s u i) = (u, (pairsA (x2Mult s u)).getD i (0, 0))

/-- Upper-triangle position of the `e`-th A pair of a type of multiplicity `m`. -/
def posA (m e : ℕ) : ℕ := upos m ((pairsA m).getD e (0, 0)).1 ((pairsA m).getD e (0, 0)).2

/-- T-block check `T = ∑ (sᵢ - 4) Uᵢ` for the pairs `p₀`, `p₁` of the first two sites. -/
noncomputable def tCellG (UBT : List (List (List (List ℕ)))) (L2 s1 s2 s3 s4 : ℕ) (p0 p1 : ℕ × ℕ) (B : ℕ) : Bool :=
  t2Check 256 L2 s1 s2 s3 s4 (UBget UBT p0.1 p1.1 p0.2 p1.2) (UBget UBT p0.2 p1.1 p0.1 p1.2)
    (UBget UBT p0.1 p1.2 p0.2 p1.1) (UBget UBT p0.2 p1.2 p0.1 p1.1) B

/-! ### Specifications -/

/-- AAS, rows by the second A label. -/
def TTspecAAS (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TT : List (List ℕ)) : Prop :=
  ∀ i0 < nA s t0, ∀ i1 < nA s t1, ∀ i2 < nS s t2,
    (ent 256 (256 - 1) ((TT.getD i1 []).getD i0 0) i2 : ℚ) =
      1108531032609225922165724911675932935547910848716289179910144000 *
        x2EmbedA x2DataConcrete s N (slab s t2 i2) (alab s t0 i0) (alab s t1 i1)

/-- AAS, rows by the first A label. -/
def TCspecAAS (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TC : List (List ℕ)) : Prop :=
  ∀ i0 < nA s t0, ∀ i1 < nA s t1, ∀ i2 < nS s t2,
    (ent 256 (256 - 1) ((TC.getD i0 []).getD i1 0) i2 : ℚ) =
      1108531032609225922165724911675932935547910848716289179910144000 *
        x2EmbedA x2DataConcrete s N (slab s t2 i2) (alab s t0 i0) (alab s t1 i1)

/-- SAA, rows by the A label of the middle site, slots at `posA`. -/
def TTspecSAA (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TT : List (List ℕ)) : Prop :=
  ∀ i0 < nS s t0, ∀ i1 < nA s t1, ∀ i2 < nA s t2,
    (ent 256 (256 - 1) ((TT.getD i1 []).getD i0 0) (posA (x2Mult s t2) i2) : ℚ) =
      1108531032609225922165724911675932935547910848716289179910144000 *
        x2EmbedA x2DataConcrete s N (slab s t0 i0) (alab s t1 i1) (alab s t2 i2)

/-- ASA, rows by the A label of the first site, slots at `posA`. -/
def TCspecASA (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TC : List (List ℕ)) : Prop :=
  ∀ i0 < nA s t0, ∀ i1 < nS s t1, ∀ i2 < nA s t2,
    (ent 256 (256 - 1) ((TC.getD i0 []).getD i1 0) (posA (x2Mult s t2) i2) : ℚ) =
      1108531032609225922165724911675932935547910848716289179910144000 *
        x2EmbedA x2DataConcrete s N (slab s t1 i1) (alab s t0 i0) (alab s t2 i2)

/-- `x2EmbedA` vanishes in all three arrangements of a type triple. -/
def ZspecA (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) : Prop :=
  (∀ i0 < nA s t0, ∀ i1 < nA s t1, ∀ i2 < nS s t2,
    x2EmbedA x2DataConcrete s N (slab s t2 i2) (alab s t0 i0) (alab s t1 i1) = 0) ∧
  (∀ i0 < nS s t0, ∀ i1 < nA s t1, ∀ i2 < nA s t2,
    x2EmbedA x2DataConcrete s N (slab s t0 i0) (alab s t1 i1) (alab s t2 i2) = 0) ∧
  (∀ i0 < nA s t0, ∀ i1 < nS s t1, ∀ i2 < nA s t2,
    x2EmbedA x2DataConcrete s N (slab s t1 i1) (alab s t0 i0) (alab s t2 i2) = 0)

/-! ### The three arrangements from checked T-blocks -/

section Gen
variable (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k) (t0 t1 t2 : Fin 8)
  (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (fs : List (ℕ × ℕ × ℕ)) (UBT : List (List (List (List ℕ))))
  (hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] =
        (ibIB 256 fs (kflat (x2Mult s t1) (x2Mult s t2) x0 x1 x2) (kflat (x2Mult s t1) (x2Mult s t2) y0 y1 y2) : ℚ))
  (hU : ∀ a0 < x2Mult s t0, ∀ a1 < x2Mult s t1, ∀ b0 < x2Mult s t0, ∀ b1 < x2Mult s t1, ∀ a2 b2 : ℕ,
      a2 ≤ b2 → b2 < x2Mult s t2 →
      ent 256 (256 - 1) (UBget UBT a0 a1 b0 b1) (upos (x2Mult s t2) a2 b2) =
        ibIB 256 fs (kflat (x2Mult s t1) (x2Mult s t2) a0 a1 a2) (kflat (x2Mult s t1) (x2Mult s t2) b0 b1 b2))

include hs hN h01 h12 hKS hU in
theorem ttSpecAAS (Tget : ℕ → ℕ → ℕ) (hlab : labelsOK s) (hlabA : labelsAOK s)
    (hp0 : pairsAOK (x2Mult s t0)) (hp1 : pairsAOK (x2Mult s t1)) (hp2 : pairsOK (x2Mult s t2))
    (hT : ∀ i0 < nA s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 2 2 6 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) (Tget i0 i1) = true) :
    ∀ i0 < nA s t0, ∀ i1 < nA s t1, ∀ i2 < nS s t2,
      (ent 256 (256 - 1) (Tget i0 i1) i2 : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedA x2DataConcrete s N (slab s t2 i2) (alab s t0 i0) (alab s t1 i1) := by
  intro i0 hi0 i1 hi1 i2 hi2
  obtain ⟨_, hq0⟩ := hp0
  obtain ⟨_, hq1⟩ := hp1
  obtain ⟨_, hq2⟩ := hp2
  obtain ⟨hab0, hb0, _⟩ := hq0 i0 hi0
  obtain ⟨hab1, hb1, _⟩ := hq1 i1 hi1
  obtain ⟨hab2, hb2, hu2⟩ := hq2 i2 hi2
  have hl0 := hlabA t0 i0 hi0
  have hl1 := hlabA t1 i1 hi1
  have hl2 := hlab t2 i2 hi2
  have h8 := x2EmbedA_eight2 s hs N hN (slab s t2 i2) (alab s t0 i0) (alab s t1 i1)
    (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
  rw [hl0, hl1, hl2] at h8
  dsimp only at h8
  have hc := hT i0 hi0 i1 hi1
  unfold tCellG at hc
  have ht := t2Check_sound 256 (nS s t2) 6 2 2 6 _ _ _ _ _ (by norm_num) (by norm_num) hc i2 hi2
  rw [ht]
  set a0 := ((pairsA (x2Mult s t0)).getD i0 (0, 0)).1 with ha0
  set b0 := ((pairsA (x2Mult s t0)).getD i0 (0, 0)).2 with hb0'
  set a1 := ((pairsA (x2Mult s t1)).getD i1 (0, 0)).1 with ha1
  set b1 := ((pairsA (x2Mult s t1)).getD i1 (0, 0)).2 with hb1'
  set a2 := ((pairsU (x2Mult s t2)).getD i2 (0, 0)).1 with ha2
  set b2 := ((pairsU (x2Mult s t2)).getD i2 (0, 0)).2 with hb2'
  have ha0l : a0 < x2Mult s t0 := lt_trans hab0 hb0
  have ha1l : a1 < x2Mult s t1 := lt_trans hab1 hb1
  have ha2l : a2 < x2Mult s t2 := lt_of_le_of_lt hab2 hb2
  have k1 := hKS a0 a1 a2 b0 b1 b2 ha0l ha1l ha2l hb0 hb1 hb2
  have k2 := hKS b0 a1 a2 a0 b1 b2 hb0 ha1l ha2l ha0l hb1 hb2
  have k3 := hKS a0 b1 a2 b0 a1 b2 ha0l hb1 ha2l hb0 ha1l hb2
  have k4 := hKS b0 b1 a2 a0 a1 b2 hb0 hb1 ha2l ha0l ha1l hb2
  have u1 := hU a0 ha0l a1 ha1l b0 hb0 b1 hb1 a2 b2 hab2 hb2
  have u2 := hU b0 hb0 a1 ha1l a0 ha0l b1 hb1 a2 b2 hab2 hb2
  have u3 := hU a0 ha0l b1 hb1 b0 hb0 a1 ha1l a2 b2 hab2 hb2
  have u4 := hU b0 hb0 b1 hb1 a0 ha0l a1 ha1l a2 b2 hab2 hb2
  rw [hu2] at u1 u2 u3 u4
  rw [← u1] at k1
  rw [← u2] at k2
  rw [← u3] at k3
  rw [← u4] at k4
  push_cast at k1 k2 k3 k4 ⊢
  linear_combination (-2 : ℚ) * k1 + 2 * k2 + 2 * k3 - 2 * k4 -
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) * h8

include hs hN h01 h12 hKS hU in
theorem ttSpecSAA (Tget : ℕ → ℕ → ℕ) (hlab : labelsOK s) (hlabA : labelsAOK s)
    (hp0 : pairsOK (x2Mult s t0)) (hp1 : pairsAOK (x2Mult s t1)) (hp2 : pairsAOK (x2Mult s t2))
    (hT : ∀ i0 < nS s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 6 2 2 ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) (Tget i0 i1) = true) :
    ∀ i0 < nS s t0, ∀ i1 < nA s t1, ∀ i2 < nA s t2,
      (ent 256 (256 - 1) (Tget i0 i1) (posA (x2Mult s t2) i2) : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedA x2DataConcrete s N (slab s t0 i0) (alab s t1 i1) (alab s t2 i2) := by
  intro i0 hi0 i1 hi1 i2 hi2
  obtain ⟨_, hq0⟩ := hp0
  obtain ⟨_, hq1⟩ := hp1
  obtain ⟨hlen2, hq2⟩ := hp2
  obtain ⟨hab0, hb0, _⟩ := hq0 i0 hi0
  obtain ⟨hab1, hb1, _⟩ := hq1 i1 hi1
  obtain ⟨hab2, hb2, hup2⟩ := hq2 i2 hi2
  have hl0 := hlab t0 i0 hi0
  have hl1 := hlabA t1 i1 hi1
  have hl2 := hlabA t2 i2 hi2
  have h8 := x2EmbedA_eight0 s hs N hN (slab s t0 i0) (alab s t1 i1) (alab s t2 i2)
    (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
  rw [hl0, hl1, hl2] at h8
  dsimp only at h8
  have hpos : posA (x2Mult s t2) i2 < nS s t2 := by
    unfold posA nS
    exact hup2
  have hc := hT i0 hi0 i1 hi1
  unfold tCellG at hc
  have ht := t2Check_sound 256 (nS s t2) 6 6 2 2 _ _ _ _ _ (by norm_num) (by norm_num) hc _ hpos
  rw [ht]
  unfold posA
  set a0 := ((pairsU (x2Mult s t0)).getD i0 (0, 0)).1 with ha0
  set b0 := ((pairsU (x2Mult s t0)).getD i0 (0, 0)).2 with hb0'
  set a1 := ((pairsA (x2Mult s t1)).getD i1 (0, 0)).1 with ha1
  set b1 := ((pairsA (x2Mult s t1)).getD i1 (0, 0)).2 with hb1'
  set a2 := ((pairsA (x2Mult s t2)).getD i2 (0, 0)).1 with ha2
  set b2 := ((pairsA (x2Mult s t2)).getD i2 (0, 0)).2 with hb2'
  have ha0l : a0 < x2Mult s t0 := lt_of_le_of_lt hab0 hb0
  have ha1l : a1 < x2Mult s t1 := lt_trans hab1 hb1
  have ha2l : a2 < x2Mult s t2 := lt_trans hab2 hb2
  have k1 := hKS a0 a1 a2 b0 b1 b2 ha0l ha1l ha2l hb0 hb1 hb2
  have k2 := hKS b0 a1 a2 a0 b1 b2 hb0 ha1l ha2l ha0l hb1 hb2
  have k3 := hKS a0 b1 a2 b0 a1 b2 ha0l hb1 ha2l hb0 ha1l hb2
  have k4 := hKS b0 b1 a2 a0 a1 b2 hb0 hb1 ha2l ha0l ha1l hb2
  have u1 := hU a0 ha0l a1 ha1l b0 hb0 b1 hb1 a2 b2 (le_of_lt hab2) hb2
  have u2 := hU b0 hb0 a1 ha1l a0 ha0l b1 hb1 a2 b2 (le_of_lt hab2) hb2
  have u3 := hU a0 ha0l b1 hb1 b0 hb0 a1 ha1l a2 b2 (le_of_lt hab2) hb2
  have u4 := hU b0 hb0 b1 hb1 a0 ha0l a1 ha1l a2 b2 (le_of_lt hab2) hb2
  rw [← u1] at k1
  rw [← u2] at k2
  rw [← u3] at k3
  rw [← u4] at k4
  push_cast at k1 k2 k3 k4 ⊢
  linear_combination (-2 : ℚ) * k1 - 2 * k2 + 2 * k3 + 2 * k4 -
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) * h8

include hs hN h01 h12 hKS hU in
theorem ttSpecASA (Tget : ℕ → ℕ → ℕ) (hlab : labelsOK s) (hlabA : labelsAOK s)
    (hp0 : pairsAOK (x2Mult s t0)) (hp1 : pairsOK (x2Mult s t1)) (hp2 : pairsAOK (x2Mult s t2))
    (hT : ∀ i0 < nA s t0, ∀ i1 < nS s t1, tCellG UBT (nS s t2) 6 2 6 2 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) (Tget i0 i1) = true) :
    ∀ i0 < nA s t0, ∀ i1 < nS s t1, ∀ i2 < nA s t2,
      (ent 256 (256 - 1) (Tget i0 i1) (posA (x2Mult s t2) i2) : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedA x2DataConcrete s N (slab s t1 i1) (alab s t0 i0) (alab s t2 i2) := by
  intro i0 hi0 i1 hi1 i2 hi2
  obtain ⟨_, hq0⟩ := hp0
  obtain ⟨_, hq1⟩ := hp1
  obtain ⟨hlen2, hq2⟩ := hp2
  obtain ⟨hab0, hb0, _⟩ := hq0 i0 hi0
  obtain ⟨hab1, hb1, _⟩ := hq1 i1 hi1
  obtain ⟨hab2, hb2, hup2⟩ := hq2 i2 hi2
  have hl0 := hlabA t0 i0 hi0
  have hl1 := hlab t1 i1 hi1
  have hl2 := hlabA t2 i2 hi2
  have h8 := x2EmbedA_eight1 s hs N hN (slab s t1 i1) (alab s t0 i0) (alab s t2 i2)
    (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
  rw [hl0, hl1, hl2] at h8
  dsimp only at h8
  have hpos : posA (x2Mult s t2) i2 < nS s t2 := by
    unfold posA nS
    exact hup2
  have hc := hT i0 hi0 i1 hi1
  unfold tCellG at hc
  have ht := t2Check_sound 256 (nS s t2) 6 2 6 2 _ _ _ _ _ (by norm_num) (by norm_num) hc _ hpos
  rw [ht]
  unfold posA
  set a0 := ((pairsA (x2Mult s t0)).getD i0 (0, 0)).1 with ha0
  set b0 := ((pairsA (x2Mult s t0)).getD i0 (0, 0)).2 with hb0'
  set a1 := ((pairsU (x2Mult s t1)).getD i1 (0, 0)).1 with ha1
  set b1 := ((pairsU (x2Mult s t1)).getD i1 (0, 0)).2 with hb1'
  set a2 := ((pairsA (x2Mult s t2)).getD i2 (0, 0)).1 with ha2
  set b2 := ((pairsA (x2Mult s t2)).getD i2 (0, 0)).2 with hb2'
  have ha0l : a0 < x2Mult s t0 := lt_trans hab0 hb0
  have ha1l : a1 < x2Mult s t1 := lt_of_le_of_lt hab1 hb1
  have ha2l : a2 < x2Mult s t2 := lt_trans hab2 hb2
  have k1 := hKS a0 a1 a2 b0 b1 b2 ha0l ha1l ha2l hb0 hb1 hb2
  have k2 := hKS b0 a1 a2 a0 b1 b2 hb0 ha1l ha2l ha0l hb1 hb2
  have k3 := hKS a0 b1 a2 b0 a1 b2 ha0l hb1 ha2l hb0 ha1l hb2
  have k4 := hKS b0 b1 a2 a0 a1 b2 hb0 hb1 ha2l ha0l ha1l hb2
  have u1 := hU a0 ha0l a1 ha1l b0 hb0 b1 hb1 a2 b2 (le_of_lt hab2) hb2
  have u2 := hU b0 hb0 a1 ha1l a0 ha0l b1 hb1 a2 b2 (le_of_lt hab2) hb2
  have u3 := hU a0 ha0l b1 hb1 b0 hb0 a1 ha1l a2 b2 (le_of_lt hab2) hb2
  have u4 := hU b0 hb0 b1 hb1 a0 ha0l a1 ha1l a2 b2 (le_of_lt hab2) hb2
  rw [← u1] at k1
  rw [← u2] at k2
  rw [← u3] at k3
  rw [← u4] at k4
  push_cast at k1 k2 k3 k4 ⊢
  linear_combination (-2 : ℚ) * k1 + 2 * k2 - 2 * k3 + 2 * k4 -
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) * h8

include hs hN h01 h12 in
theorem zspecA_of_empty (hlab : labelsOK s) (hlabA : labelsAOK s)
    (hpS : ∀ u : Fin 8, pairsOK (x2Mult s u)) (hpA : ∀ u : Fin 8, pairsAOK (x2Mult s u))
    (hKS0 : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] = 0) : ZspecA s N t0 t1 t2 := by
  refine ⟨fun i0 hi0 i1 hi1 i2 hi2 => ?_, fun i0 hi0 i1 hi1 i2 hi2 => ?_, fun i0 hi0 i1 hi1 i2 hi2 => ?_⟩
  · obtain ⟨hab0, hb0, _⟩ := (hpA t0).2 i0 hi0
    obtain ⟨hab1, hb1, _⟩ := (hpA t1).2 i1 hi1
    obtain ⟨hab2, hb2, _⟩ := (hpS t2).2 i2 hi2
    have hl0 := hlabA t0 i0 hi0
    have hl1 := hlabA t1 i1 hi1
    have hl2 := hlab t2 i2 hi2
    have h8 := x2EmbedA_eight2 s hs N hN (slab s t2 i2) (alab s t0 i0) (alab s t1 i1)
      (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
    rw [hl0, hl1, hl2] at h8
    dsimp only at h8
    have ha0 := lt_trans hab0 hb0
    have ha1 := lt_trans hab1 hb1
    have ha2 := lt_of_le_of_lt hab2 hb2
    rw [hKS0 _ _ _ _ _ _ ha0 ha1 ha2 hb0 hb1 hb2, hKS0 _ _ _ _ _ _ hb0 ha1 ha2 ha0 hb1 hb2,
      hKS0 _ _ _ _ _ _ ha0 hb1 ha2 hb0 ha1 hb2, hKS0 _ _ _ _ _ _ hb0 hb1 ha2 ha0 ha1 hb2] at h8
    linarith
  · obtain ⟨hab0, hb0, _⟩ := (hpS t0).2 i0 hi0
    obtain ⟨hab1, hb1, _⟩ := (hpA t1).2 i1 hi1
    obtain ⟨hab2, hb2, _⟩ := (hpA t2).2 i2 hi2
    have hl0 := hlab t0 i0 hi0
    have hl1 := hlabA t1 i1 hi1
    have hl2 := hlabA t2 i2 hi2
    have h8 := x2EmbedA_eight0 s hs N hN (slab s t0 i0) (alab s t1 i1) (alab s t2 i2)
      (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
    rw [hl0, hl1, hl2] at h8
    dsimp only at h8
    have ha0 := lt_of_le_of_lt hab0 hb0
    have ha1 := lt_trans hab1 hb1
    have ha2 := lt_trans hab2 hb2
    rw [hKS0 _ _ _ _ _ _ ha0 ha1 ha2 hb0 hb1 hb2, hKS0 _ _ _ _ _ _ hb0 ha1 ha2 ha0 hb1 hb2,
      hKS0 _ _ _ _ _ _ ha0 hb1 ha2 hb0 ha1 hb2, hKS0 _ _ _ _ _ _ hb0 hb1 ha2 ha0 ha1 hb2] at h8
    linarith
  · obtain ⟨hab0, hb0, _⟩ := (hpA t0).2 i0 hi0
    obtain ⟨hab1, hb1, _⟩ := (hpS t1).2 i1 hi1
    obtain ⟨hab2, hb2, _⟩ := (hpA t2).2 i2 hi2
    have hl0 := hlabA t0 i0 hi0
    have hl1 := hlab t1 i1 hi1
    have hl2 := hlabA t2 i2 hi2
    have h8 := x2EmbedA_eight1 s hs N hN (slab s t1 i1) (alab s t0 i0) (alab s t2 i2)
      (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
    rw [hl0, hl1, hl2] at h8
    dsimp only at h8
    have ha0 := lt_trans hab0 hb0
    have ha1 := lt_of_le_of_lt hab1 hb1
    have ha2 := lt_trans hab2 hb2
    rw [hKS0 _ _ _ _ _ _ ha0 ha1 ha2 hb0 hb1 hb2, hKS0 _ _ _ _ _ _ hb0 ha1 ha2 ha0 hb1 hb2,
      hKS0 _ _ _ _ _ _ ha0 hb1 ha2 hb0 ha1 hb2, hKS0 _ _ _ _ _ _ hb0 hb1 ha2 ha0 ha1 hb2] at h8
    linarith

end Gen

end X2
end ThreeCopyQutritWerner
