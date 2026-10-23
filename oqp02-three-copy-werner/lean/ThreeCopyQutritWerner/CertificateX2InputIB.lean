module

public import ThreeCopyQutritWerner.CertificateX2InputV

@[expose] public section


/-!
# Input stage: input-block rows checked against stored upper blocks

For a sorted type triple, the summed input block (times `3 den_c`) is `IB(x, y) = ∑_j αⱼ Fⱼ(x) Fⱼ(y)`
over packed column fibers `Fⱼ` (the columns of `V`, of the partner, of `U`, ...) with integer weights
`αⱼ`. A row `x` is one natural linear combination of the fibers whose offset scalars
`αⱼ · digit + (2^oA - αⱼ 2^(W-1))` are read from the fibers' own slots `x` (`ibPiece`: one slot
range per fiber for all rows of a declaration). The ambient of the row is cut into blocks of `m₂`
slots (the last site); only the upper part `b₂ ≥ a₂` of every block is compared, against stored
blocks `U` (upper triangle of an `m₂ × m₂` block, row-major): `ibRowOK`, one masked comparison per
row against the divide-and-conquer concatenation of the runs of the stored blocks. `ibRowOK_sound`
and `ibBatchOK_sound` turn a passed check into the slot values of the stored blocks.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- Slot `i` by shift and mask (kernel form of `dig`). -/
def digS (W x i : ℕ) : ℕ := (x >>> (W * i)) &&& (2 ^ W - 1)

theorem digS_eq (W x i : ℕ) : digS W x i = dig W x i := by
  unfold digS dig
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem dig_low (W x n i : ℕ) (hW : 1 ≤ W) (hi : i < n) : dig W (x &&& (2 ^ (W * n) - 1)) i = dig W x i := by
  rw [dig_land, dig_lowMask W n i hW, if_pos hi, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (dig_lt W x i)]

/-! ### The value of a natural linear combination, reduced to `L` slots -/

/-- The natural linear combination of `natAxpyCheck`, reduced mod `2^(W L)`. -/
noncomputable def natAxpyVal (W L oA : ℕ) (as' Es : List ℕ) : ℕ :=
  Nat.land (Nat.add (natAxpyFold as' (natFibers W L Es) 0) (natAxpyCorr W L oA Es)) (2 ^ (W * L) - 1)

theorem natAxpyVal_spec (W L oA : ℕ) (as' Es : List ℕ) (hW : 2 ≤ W) (hlen : as'.length = Es.length)
    (hE : ∀ E ∈ Es, E < 2 ^ (W * L)) (hlin : ∀ k < L, |lincomb W (sScalars oA as') Es k| < 2 ^ (W - 1)) :
    natAxpyVal W L oA as' Es < 2 ^ (W * L) ∧
      ∀ k < L, ent W (W - 1) (natAxpyVal W L oA as' Es) k = lincomb W (sScalars oA as') Es k := by
  have hlt : natAxpyVal W L oA as' Es < 2 ^ (W * L) := by
    unfold natAxpyVal
    exact lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos _) one_pos)
  have hc : natAxpyCheck W L oA as' Es (natAxpyVal W L oA as' Es) (natAxpyCorr W L oA Es) = true := by
    unfold natAxpyCheck
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
    exact ⟨hlt, rfl⟩
  exact ⟨hlt, fun k hk => (natAxpyCheck_sound W L oA as' Es _ hW hlen hE hlin hc k hk).symm⟩

/-! ### Masks of the upper runs and runs of stored blocks -/

/-- Slots `b₂ ≥ a₂` of every block of `m₂` slots (`nb` blocks). -/
def upMask (W nb m2 a2 : ℕ) : ℕ := ((2 ^ (W * (m2 - a2)) - 1) * 2 ^ (W * a2)) * repunit (W * m2) nb

theorem upBlk_dig (W m2 a2 t : ℕ) (hW : 1 ≤ W) (ht : t < m2) :
    dig W ((2 ^ (W * (m2 - a2)) - 1) * 2 ^ (W * a2)) t = if a2 ≤ t then 2 ^ W - 1 else 0 := by
  rw [dig_mulPow]
  by_cases h : t < a2
  · rw [if_pos h, if_neg (Nat.not_le_of_lt h)]
  · rw [if_neg h, dig_lowMask W (m2 - a2) _ hW, if_pos (show t - a2 < m2 - a2 by omega),
      if_pos (Nat.le_of_not_lt h)]

theorem upBlk_lt (W m2 a2 : ℕ) (ha : a2 ≤ m2) :
    (2 ^ (W * (m2 - a2)) - 1) * 2 ^ (W * a2) < 2 ^ (W * m2) := by
  calc (2 ^ (W * (m2 - a2)) - 1) * 2 ^ (W * a2) < 2 ^ (W * (m2 - a2)) * 2 ^ (W * a2) :=
        Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) one_pos) (Nat.two_pow_pos _)
    _ = 2 ^ (W * m2) := by rw [← pow_add]; congr 1; rw [← Nat.mul_add]; congr 1; omega

theorem upMask_dig (W nb m2 a2 k : ℕ) (hW : 1 ≤ W) (hm : 1 ≤ m2) (ha : a2 ≤ m2) :
    dig W (upMask W nb m2 a2) k = if k < nb * m2 ∧ a2 ≤ k % m2 then 2 ^ W - 1 else 0 := by
  unfold upMask
  rw [dig_repeat W m2 nb _ k hW hm (upBlk_lt W m2 a2 ha)]
  by_cases hk : k < nb * m2
  · rw [if_pos hk, upBlk_dig W m2 a2 _ hW (Nat.mod_lt _ (by omega))]
    by_cases h : a2 ≤ k % m2
    · rw [if_pos h, if_pos (And.intro hk h)]
    · rw [if_neg h, if_neg (fun h' => h h'.2)]
  · rw [if_neg hk, if_neg (fun h' => hk h'.1)]

/-- Position of the pair `a ≤ b` of `m` units in row-major upper-triangle order. -/
def upos (m a b : ℕ) : ℕ := a * m - a * (a - 1) / 2 + (b - a)

/-- The run `(a₂, a₂), …, (a₂, m₂ - 1)` of a stored upper block. -/
def runU (W m2 a2 U : ℕ) : ℕ := (U >>> (W * upos m2 a2 a2)) &&& (2 ^ (W * (m2 - a2)) - 1)

theorem runU_dig (W m2 a2 U t : ℕ) (hW : 1 ≤ W) (ht : t < m2 - a2) :
    dig W (runU W m2 a2 U) t = dig W U (upos m2 a2 a2 + t) := by
  unfold runU
  rw [dig_low W _ _ t hW ht, dig_shift, Nat.add_comm]

theorem upos_run (m a b : ℕ) (h : a ≤ b) : upos m a a + (b - a) = upos m a b := by
  unfold upos
  rw [Nat.sub_self, Nat.add_zero]

/-! ### Divide-and-conquer concatenation -/

/-- Concatenate adjacent pairs (slot stride `s`). -/
def pairUp (W s : ℕ) : List ℕ → List ℕ
  | a :: b :: rest => (a + b * 2 ^ (W * s)) :: pairUp W s rest
  | l => l

/-- Concatenation of fibers of `s` slots by repeated pairing (`k` rounds). -/
def concatTree (W : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | 0, s, l => concatFibers W s l
  | k + 1, s, l => match l with
    | [] => 0
    | [a] => a
    | l => concatTree W k (2 * s) (pairUp W s l)

theorem concatFibers_pairUp (W s : ℕ) : ∀ l : List ℕ, (∀ f ∈ l, f < 2 ^ (W * s)) →
    concatFibers W (2 * s) (pairUp W s l) = concatFibers W s l ∧ ∀ f ∈ pairUp W s l, f < 2 ^ (W * (2 * s))
  | [], _ => by simp [pairUp, concatFibers]
  | [a], h => by
    refine ⟨by simp [pairUp, concatFibers], ?_⟩
    intro f hf
    simp only [pairUp, List.mem_singleton] at hf
    rw [hf]
    exact lt_of_lt_of_le (h a (by simp)) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left W (by omega)))
  | a :: b :: rest, h => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    obtain ⟨ih1, ih2⟩ := concatFibers_pairUp W s rest (fun f hf => h f (by simp [hf]))
    constructor
    · show (a + b * 2 ^ (W * s)) + concatFibers W (2 * s) (pairUp W s rest) <<< (W * (2 * s)) =
        a + (b + concatFibers W s rest <<< (W * s)) <<< (W * s)
      rw [ih1, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        show W * (2 * s) = W * s + W * s by ring, pow_add]
      ring
    · intro f hf
      simp only [pairUp, List.mem_cons] at hf
      rcases hf with rfl | hf
      · calc a + b * 2 ^ (W * s) < 2 ^ (W * s) + b * 2 ^ (W * s) := by omega
          _ = (b + 1) * 2 ^ (W * s) := by ring
          _ ≤ 2 ^ (W * s) * 2 ^ (W * s) := Nat.mul_le_mul_right _ hb
          _ = 2 ^ (W * (2 * s)) := by rw [← pow_add]; congr 1; ring
      · exact ih2 f hf

theorem concatTree_eq (W : ℕ) : ∀ (k s : ℕ) (l : List ℕ), (∀ f ∈ l, f < 2 ^ (W * s)) →
    concatTree W k s l = concatFibers W s l
  | 0, s, l, _ => rfl
  | k + 1, s, [], _ => rfl
  | k + 1, s, [a], _ => by simp [concatTree, concatFibers]
  | k + 1, s, a :: b :: rest, h => by
    obtain ⟨e, hlt⟩ := concatFibers_pairUp W s (a :: b :: rest) h
    show concatTree W k (2 * s) (pairUp W s (a :: b :: rest)) = _
    rw [concatTree_eq W k (2 * s) _ hlt, e]

/-! ### One row against the stored upper blocks -/

/-- Row check: the masked row value equals the concatenated runs of the stored blocks. -/
noncomputable def ibRowOK (W L oA m2 nb a2 : ℕ) (as' Es Ublks : List ℕ) : Bool :=
  Nat.beq (natAxpyVal W L oA as' Es &&& upMask W nb m2 a2)
    (concatTree W 12 m2 (Ublks.map (fun U => runU W m2 a2 U * 2 ^ (W * a2))))

theorem ibRowOK_sound (W L oA m2 nb a2 : ℕ) (as' Es Ublks : List ℕ) (hW : 2 ≤ W) (hm : 1 ≤ m2)
    (ha : a2 < m2) (hL : L = nb * m2) (hlenU : Ublks.length = nb) (hlen : as'.length = Es.length)
    (hE : ∀ E ∈ Es, E < 2 ^ (W * L)) (hlin : ∀ k < L, |lincomb W (sScalars oA as') Es k| < 2 ^ (W - 1))
    (hc : ibRowOK W L oA m2 nb a2 as' Es Ublks = true) (blk : ℕ) (hblk : blk < nb) (b2 : ℕ)
    (hb1 : a2 ≤ b2) (hb2 : b2 < m2) :
    ent W (W - 1) (Ublks.getD blk 0) (upos m2 a2 b2) = lincomb W (sScalars oA as') Es (blk * m2 + b2) := by
  have hW1 : 1 ≤ W := by omega
  obtain ⟨_, hval⟩ := natAxpyVal_spec W L oA as' Es hW hlen hE hlin
  unfold ibRowOK at hc
  have he := Nat.eq_of_beq_eq_true hc
  have hk : blk * m2 + b2 < L := by rw [hL]; nlinarith
  -- the pieces are below 2^(W m2)
  have hpc : ∀ f ∈ Ublks.map (fun U => runU W m2 a2 U * 2 ^ (W * a2)), f < 2 ^ (W * m2) := by
    intro f hf
    obtain ⟨U, _, rfl⟩ := List.mem_map.mp hf
    have hr : runU W m2 a2 U < 2 ^ (W * (m2 - a2)) := by
      unfold runU
      exact lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos _) one_pos)
    calc runU W m2 a2 U * 2 ^ (W * a2) < 2 ^ (W * (m2 - a2)) * 2 ^ (W * a2) :=
          Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
      _ = 2 ^ (W * m2) := by rw [← pow_add]; congr 1; rw [← Nat.mul_add]; congr 1; omega
  have hdig : dig W (natAxpyVal W L oA as' Es &&& upMask W nb m2 a2) (blk * m2 + b2) =
      dig W (concatTree W 12 m2 (Ublks.map (fun U => runU W m2 a2 U * 2 ^ (W * a2)))) (blk * m2 + b2) := by
    rw [he]
  have hmod : a2 ≤ (blk * m2 + b2) % m2 := by
    rw [Nat.mul_comm blk m2, Nat.mul_add_mod, Nat.mod_eq_of_lt hb2]
    exact hb1
  have hk' : blk * m2 + b2 < nb * m2 := by rw [← hL]; exact hk
  have hblk' : blk < (Ublks.map (fun U => runU W m2 a2 U * 2 ^ (W * a2))).length := by
    rw [List.length_map, hlenU]
    exact hblk
  rw [dig_land, upMask_dig W nb m2 a2 _ hW1 hm (by omega), if_pos (And.intro hk' hmod),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (dig_lt W _ _),
    concatTree_eq W 12 m2 _ hpc, concatFibers_dig W m2 _ hpc blk b2 hblk' hb2,
    List.getD_eq_getElem _ _ hblk', List.getElem_map] at hdig
  rw [dig_mulPow, if_neg (Nat.not_lt_of_le hb1), runU_dig W m2 a2 _ _ hW1 (by omega), upos_run m2 a2 b2 hb1,
    ← List.getD_eq_getElem _ 0 (by rw [hlenU]; exact hblk)] at hdig
  rw [← hval _ hk]
  unfold ent
  rw [hdig]


/-! ### A batch of rows of one row-batch, with scalars read from the fibers -/

/-- Slots `[x0, x0 + R)` of a fiber. -/
def ibPiece (W x0 R F : ℕ) : ℕ := (F >>> (W * x0)) &&& (2 ^ (W * R) - 1)

theorem ibPiece_dig (W x0 R F i : ℕ) (hW : 1 ≤ W) (hi : i < R) :
    digS W (ibPiece W x0 R F) i = dig W F (x0 + i) := by
  rw [digS_eq]
  unfold ibPiece
  rw [dig_low W _ R i hW hi, dig_shift, Nat.add_comm]

/-- Offset scalars of row `x0 + i` read from the pieces of the scalar sources:
`α · slot + (2^oA - α 2^(W-1))`. -/
def ibScalars (W oA i : ℕ) (pcs : List (ℕ × ℕ)) : List ℕ :=
  pcs.map (fun p => p.2 * digS W p.1 i + (2 ^ oA - p.2 * 2 ^ (W - 1)))

/-- `∑_j αⱼ Sⱼ(x) Fⱼ(y)` over triples `(Sⱼ, Fⱼ, αⱼ)` (scalar source, fiber, weight). -/
noncomputable def ibIB (W : ℕ) (fs : List (ℕ × ℕ × ℕ)) (x y : ℕ) : ℤ :=
  (fs.map (fun p => (p.2.2 : ℤ) * ent W (W - 1) p.1 x * ent W (W - 1) p.2.1 y)).sum

/-- Pieces of the scalar sources with their weights. -/
def ibPieces (W x0 R : ℕ) (fs : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  fs.map (fun p => (ibPiece W x0 R p.1, p.2.2))

theorem ibScalars_lincomb (W oA x0 R i k : ℕ) (hW : 1 ≤ W) (hi : i < R) : ∀ fs : List (ℕ × ℕ × ℕ),
    (∀ p ∈ fs, p.2.2 * 2 ^ (W - 1) ≤ 2 ^ oA) →
    lincomb W (sScalars oA (ibScalars W oA i (ibPieces W x0 R fs))) (fs.map (fun p => p.2.1)) k =
      ibIB W fs (x0 + i) k
  | [], _ => by simp [ibScalars, ibPieces, sScalars, lincomb, ibIB]
  | p :: fs, h => by
    have hp := h p (by simp)
    have ih := ibScalars_lincomb W oA x0 R i k hW hi fs (fun q hq => h q (by simp [hq]))
    simp only [ibScalars, ibPieces, sScalars, List.map_cons, lincomb] at ih ⊢
    unfold ibIB at ih ⊢
    rw [List.map_cons, List.sum_cons, ← ih, ibPiece_dig W x0 R p.1 i hW hi]
    unfold ent
    push_cast [Nat.cast_sub hp]
    ring

/-- All rows `lo ≤ a₂ < lo + R` of one row-batch (row `x0 + i` has last unit `lo + i`). -/
noncomputable def ibBatchOK (W L oA m2 nb lo R x0 : ℕ) (fs : List (ℕ × ℕ × ℕ)) (Ublks : List ℕ) : Bool :=
  (List.range R).all (fun i => ibRowOK W L oA m2 nb (lo + i)
    (ibScalars W oA i (ibPieces W x0 R fs)) (fs.map (fun p => p.2.1)) Ublks)

theorem ibBatchOK_sound (W L oA m2 nb lo R x0 : ℕ) (fs : List (ℕ × ℕ × ℕ)) (Ublks : List ℕ) (hW : 2 ≤ W)
    (hm : 1 ≤ m2) (hR : lo + R ≤ m2) (hL : L = nb * m2) (hlenU : Ublks.length = nb)
    (hfs : ∀ p ∈ fs, p.2.1 < 2 ^ (W * L) ∧ p.2.2 * 2 ^ (W - 1) ≤ 2 ^ oA)
    (hlin : ∀ i < R, ∀ k < L, |ibIB W fs (x0 + i) k| < 2 ^ (W - 1))
    (hc : ibBatchOK W L oA m2 nb lo R x0 fs Ublks = true) (i : ℕ) (hi : i < R) (blk : ℕ) (hblk : blk < nb)
    (b2 : ℕ) (hb1 : lo + i ≤ b2) (hb2 : b2 < m2) :
    ent W (W - 1) (Ublks.getD blk 0) (upos m2 (lo + i) b2) = ibIB W fs (x0 + i) (blk * m2 + b2) := by
  have hW1 : 1 ≤ W := by omega
  unfold ibBatchOK at hc
  have hci := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  have hl : ∀ k, lincomb W (sScalars oA (ibScalars W oA i (ibPieces W x0 R fs))) (fs.map (fun p => p.2.1)) k =
      ibIB W fs (x0 + i) k :=
    fun k => ibScalars_lincomb W oA x0 R i k hW1 hi fs (fun p hp => (hfs p hp).2)
  have hE : ∀ E ∈ fs.map (fun p => p.2.1), E < 2 ^ (W * L) := by
    intro E hE
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hE
    exact (hfs p hp).1
  have hlen : (ibScalars W oA i (ibPieces W x0 R fs)).length = (fs.map (fun p => p.2.1)).length := by
    simp [ibScalars, ibPieces]
  rw [ibRowOK_sound W L oA m2 nb (lo + i) _ _ Ublks hW hm (by omega) hL hlenU hlen hE
    (fun k hk => by rw [hl]; exact hlin i hi k hk) hci blk hblk b2 hb1 hb2, hl]

/-- Triples of a sum of parts `(scalar sources, fibers, weight)`. -/
def ibFS (parts : List (List ℕ × List ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  parts.flatMap (fun q => (q.1.zip q.2.1).map (fun sf => (sf.1, sf.2, q.2.2)))

end X2
end ThreeCopyQutritWerner
