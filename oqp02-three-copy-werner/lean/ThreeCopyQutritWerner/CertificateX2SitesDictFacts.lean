module

public import ThreeCopyQutritWerner.CertificateX2SitesDictCheck1
public import ThreeCopyQutritWerner.CertificateX2SitesDictCheck2
public import ThreeCopyQutritWerner.CertificateX2SitesFacts

@[expose] public section


/-!
# Dictionary and target identities in mirror form

* `x2sDict1M`, `x2sDict2M`: the sector-0 compression of `x2SitesW s u` at `(t, i, j)` is
  `x2Qu D s (t, i, j) u`, for any `D` with the exact parity transfers.
* `x2sTargetM`: the sector-0 compression of the endpoint weight `[σ = 1] - [σ = (0 5)] / 2` is
  `x2LocalTarget` (Gram minus half the swap diagram, the bridge's tables).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-! ## The packed tables equal the numerators -/

theorem rows_facts (rows : List (List ℕ)) (n : ℕ) (hlen : rows.length = n)
    (hrow : rows.all (fun r => r.length == n) = true)
    (hb : rows.all (·.all (fun x => Nat.blt x (2 ^ 32))) = true) :
    rows.length = n ∧ (∀ r ∈ rows, r.length = n) ∧ (∀ r ∈ rows, ∀ x ∈ r, x < 2 ^ 32) := by
  refine ⟨hlen, ?_, ?_⟩
  · intro r hr
    exact beq_iff_eq.mp (List.all_eq_true.mp hrow r hr)
  · intro r hr x hx
    exact Nat.blt_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hb r hr) x hx)

theorem trans_facts (s : ℕ) (hs : s = 1 ∨ s = 2) :
    ((transSRows s).length = 282 ∧ (∀ r ∈ transSRows s, r.length = 282) ∧
      (∀ r ∈ transSRows s, ∀ x ∈ r, x < 2 ^ 32)) ∧
    ((transARows s).length = 231 ∧ (∀ r ∈ transARows s, r.length = 231) ∧
      (∀ r ∈ transARows s, ∀ x ∈ r, x < 2 ^ 32)) := by
  have hsh := trans_shape
  have hbd := trans_bounds
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh hbd
  obtain ⟨⟨⟨⟨⟨⟨⟨hS1l, hS1r⟩, hS2l⟩, hS2r⟩, hA1l⟩, hA1r⟩, hA2l⟩, hA2r⟩ := hsh
  obtain ⟨⟨⟨hS1b, hS2b⟩, hA1b⟩, hA2b⟩ := hbd
  rcases hs with rfl | rfl
  · have e1 : transSRows 1 = transS1Tab := rfl
    have e2 : transARows 1 = transA1Tab := rfl
    rw [e1, e2]
    exact ⟨rows_facts _ 282 hS1l hS1r hS1b, rows_facts _ 231 hA1l hA1r hA1b⟩
  · have e1 : transSRows 2 = transS2Tab := rfl
    have e2 : transARows 2 = transA2Tab := rfl
    rw [e1, e2]
    exact ⟨rows_facts _ 282 hS2l hS2r hS2b, rows_facts _ 231 hA2l hA2r hA2b⟩

theorem numSP_eq (s : ℕ) (hs : s = 1 ∨ s = 2) (i j : ℕ) (hi : i < 282) (hj : j < 282) :
    numSP s i j = transSNum s i j := by
  obtain ⟨⟨hl, hr, hb⟩, _⟩ := trans_facts s hs
  have hmem : (transSRows s).getD i [] ∈ transSRows s := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  unfold numSP tsPack transSNum
  rw [ext_packRows 32 282 (transSRows s) hr hb i (by omega),
    ext_packRow 32 _ (hb _ hmem) j (by rw [hr _ hmem]; exact hj)]

theorem numAP_eq (s : ℕ) (hs : s = 1 ∨ s = 2) (i j : ℕ) (hi : i < 231) (hj : j < 231) :
    numAP s i j = transANum s i j := by
  obtain ⟨_, ⟨hl, hr, hb⟩⟩ := trans_facts s hs
  have hmem : (transARows s).getD i [] ∈ transARows s := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  unfold numAP taPack transANum
  rw [ext_packRows 32 231 (transARows s) hr hb i (by omega),
    ext_packRow 32 _ (hb _ hmem) j (by rw [hr _ hmem]; exact hj)]

/-! ## `qformN` at the flat slots of two units -/

theorem qformN_flat (D : X2Data) (hS : D.transS = X2.x2TransS) (hA : D.transA = X2.x2TransA)
    (s : Fin 3) (hs : s = 1 ∨ s = 2) (v : X2U 0) (u : X2U s) :
    ((qformN s (x2sFlatU 0 v) (x2sFlatU s u) : ℤ) : ℚ) = 2 * (transDen s : ℚ) * x2Qu D s v u := by
  have hs' : (s : ℕ) = 1 ∨ (s : ℕ) = 2 := by
    rcases hs with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hs0 : (s : ℕ) ≠ 0 := by omega
  have hden : (transDen s : ℚ) ≠ 0 := by
    rcases hs' with h | h <;> rw [h] <;> norm_num [transDen]
  rw [x2Qu_apply, hS, hA]
  unfold qformN
  rw [decU_flat 0 v, decU_flat s u]
  dsimp only
  rw [numSP_eq s hs' _ _ (x2SIdx 0 v.1 v.2.1 v.2.2).isLt (x2SIdx s u.1 u.2.1 u.2.2).isLt,
    numAP_eq s hs' _ _ (x2AIdx 0 v.1 v.2.1 v.2.2).isLt (x2AIdx s u.1 u.2.1 u.2.2).isLt]
  simp only [X2.x2TransS, X2.x2TransA, Matrix.of_apply, if_neg hs0]
  push_cast
  simp only [sgnZ_cast]
  split_ifs <;> field_simp [hden] <;> ring

/-! ## The integer dictionary identity -/

theorem getD_map_two (l : List ℕ) (n : ℕ) : (l.map (fun x => 2 * x)).getD n 0 = 2 * l.getD n 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem dict_int (Wt : List (List ℕ))
    (hWt : ∀ u < 513, rowOK (Wt.getD u []) = true)
    (s : Fin 3) (u k : ℕ) (hu : u < 513) (hk : k < 513)
    (hcheck : natAxpyCheck 48 513 26 ((Wt.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux s u 513) (natAxpyCorr 48 513 26 x2sComp0) = true) :
    2 * ∑ p : Fin 513, (((Wt.getD u []).getD p 0 : ℤ) - 2 ^ 25) *
      ent 48 (48 - 1) (x2sComp0.getD p 0) k = qformN s k u := by
  obtain ⟨hl, hb⟩ := x2sW_row Wt hWt u hu
  have hl2 : ((Wt.getD u []).map (fun x => 2 * x)).length = 513 := by rw [List.length_map]; exact hl
  have hb2 : ((Wt.getD u []).map (fun x => 2 * x)).all (fun x => Nat.blt x (2 ^ (26 + 1))) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := Nat.blt_eq.mp (List.all_eq_true.mp hb y hy)
    apply Nat.blt_eq.mpr
    rw [pow_succ] at this ⊢
    omega
  have h := axpy_int _ x2sComp0 26 _ hl2 hb2 x2sComp0_shape (by norm_num) hcheck k hk
  rw [ent_qpack s u k hk] at h
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [getD_map_two]
  push_cast
  all_goals ring

/-! ## Mirror form of the dictionary -/

/-- The unit coordinate of a sector-0 frame slot (the bridge's `x2UnitAt 0 … t i j`). -/
def x2sUnitAt0 (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) : X2U 0 :=
  ⟨Fin.castSucc t, (Fin.cast (x2sMult0 t).symm i, Fin.cast (x2sMult0 t).symm j)⟩

theorem x2sFlatU_unitAt0 (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    x2sFlatU 0 (x2sUnitAt0 t i j) = x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j := by
  unfold x2sFlatU x2sUnitAt0
  dsimp only
  rw [x2sOffU0, Fin.val_cast, Fin.val_cast, x2sMult0]

theorem x2sDictM (D : X2Data) (hS : D.transS = X2.x2TransS) (hA : D.transA = X2.x2TransA)
    (s : Fin 3) (hs : s = 1 ∨ s = 2) (Wt : List (List ℕ)) (hWt : x2sWTab s = Wt)
    (hWsh : ∀ u < 513, rowOK (Wt.getD u []) = true)
    (hcheck : ∀ u < 513, natAxpyCheck 48 513 26 ((Wt.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux s u 513) (natAxpyCorr 48 513 26 x2sComp0) = true)
    (hden : (x2sDen s : ℚ) = (transDen s : ℚ))
    (u : X2U s) (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    x2sCompM0 (x2SitesW s u) t i j = ((x2Qu D s (x2sUnitAt0 t i j) u : ℚ) : ℂ) := by
  have hden0 : (x2sDen s : ℚ) ≠ 0 := by
    unfold x2sDen
    split_ifs <;> norm_num
  unfold x2sCompM0 x2sSource0
  rw [comp_entry]
  unfold x2SitesW
  rw [sum_weight_collapse]
  simp only [x2sComp0_spec, hWt]
  have hk : x2sOff0 t + (i : ℕ) * certificateDescendantFrames2SourceSize t + j < 513 :=
    layout_lt _ _ 513 x2s0_end t i j
  have hint := dict_int Wt hWsh s (x2sFlatU s u)
    (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) (x2sFlatU_lt s u) hk
    (hcheck _ (x2sFlatU_lt s u))
  rw [← x2sFlatU_unitAt0] at hint
  have hq := qformN_flat D hS hA s hs (x2sUnitAt0 t i j) u
  rw [← hint] at hq
  have hq' : (x2Qu D s (x2sUnitAt0 t i j) u : ℚ) =
      (∑ p : Fin 513, (((Wt.getD (x2sFlatU s u) []).getD p 0 : ℤ) - 2 ^ 25) *
        ent 48 (48 - 1) (x2sComp0.getD p 0) (x2sFlatU 0 (x2sUnitAt0 t i j)) : ℤ) / (x2sDen s : ℚ) := by
    rw [hden]
    have h2 : (transDen s : ℚ) ≠ 0 := hden ▸ hden0
    push_cast at hq ⊢
    field_simp
    linarith
  rw [hq', x2sFlatU_unitAt0]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  push_cast
  all_goals ring

theorem x2sDict1M (D : X2Data) (hS : D.transS = X2.x2TransS) (hA : D.transA = X2.x2TransA)
    (u : X2U 1) (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    x2sCompM0 (x2SitesW 1 u) t i j = ((x2Qu D 1 (x2sUnitAt0 t i j) u : ℚ) : ℂ) :=
  x2sDictM D hS hA 1 (Or.inl rfl) x2sW1 rfl x2sW1_shape x2sDict1_check (by norm_num [x2sDen, transDen])
    u t i j

theorem x2sDict2M (D : X2Data) (hS : D.transS = X2.x2TransS) (hA : D.transA = X2.x2TransA)
    (u : X2U 2) (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    x2sCompM0 (x2SitesW 2 u) t i j = ((x2Qu D 2 (x2sUnitAt0 t i j) u : ℚ) : ℂ) :=
  x2sDictM D hS hA 2 (Or.inr rfl) x2sW2 rfl x2sW2_shape x2sDict2_check (by norm_num [x2sDen, transDen])
    u t i j

/-! ## The endpoint target -/

theorem x2SitesPiv_493 : x2SitesPiv 493 = 633 := by decide +kernel

theorem x2SitesPerm_piv0 : x2SitesPerm (x2SitesPiv 0) = 1 := by
  rw [x2SitesPiv_zero]
  ext k
  rw [x2SitesPerm_zero]
  rfl

theorem x2SitesPerm_piv493 : x2SitesPerm (x2SitesPiv 493) = Equiv.swap 0 5 := by
  rw [x2SitesPiv_493]
  ext k
  rw [x2SitesPerm_633]

theorem x2sTarget_check : ∀ t : Fin 7, ∀ i < certificateDescendantFrames2SourceSize t,
    ∀ j < certificateDescendantFrames2SourceSize t,
      ent 48 (48 - 1) (x2sComp0.getD ((0 : Fin 513) : ℕ) 0)
          (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) =
        ((x2GramRows 0 (Fin.castSucc t)).getD i []).getD j 0 ∧
      ent 48 (48 - 1) (x2sComp0.getD ((493 : Fin 513) : ℕ) 0)
          (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) =
        ((x2SwapRows (Fin.castSucc t)).getD i []).getD j 0 := by
  decide +kernel

theorem sum_two_term (c : Equiv.Perm (Fin 6) → ℂ) :
    ∑ σ, ((if σ = 1 then 1 else 0) - (1 / 2) * (if σ = Equiv.swap 0 5 then 1 else 0)) * c σ =
      c 1 - (1 / 2) * c (Equiv.swap 0 5) := by
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem x2sTargetM (t : Fin 7) :
    x2sCompM0 (fun σ => (if σ = 1 then 1 else 0) - (1 / 2) * (if σ = Equiv.swap 0 5 then 1 else 0)) t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2sMult0 t).symm i)
        (Fin.cast (x2sMult0 t).symm j) : ℚ) : ℂ) := by
  ext i j
  unfold x2sCompM0 x2sSource0
  rw [comp_entry, sum_two_term, ← x2SitesPerm_piv0, ← x2SitesPerm_piv493, x2sComp0_spec, x2sComp0_spec]
  obtain ⟨h1, h2⟩ := x2sTarget_check t i i.isLt j j.isLt
  rw [h1, h2]
  simp only [Matrix.of_apply, x2LocalTarget, x2Gram, x2SwapDiagram, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, Fin.val_cast, smul_eq_mul]
  push_cast
  all_goals ring

end ThreeCopyQutritWerner.X2Sites
