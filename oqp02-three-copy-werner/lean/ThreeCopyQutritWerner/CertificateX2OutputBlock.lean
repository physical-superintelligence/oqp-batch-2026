module

public import ThreeCopyQutritWerner.CertificateX2OutputCore

@[expose] public section


/-!
# Output stage: `x2Out D s N b` of one h block from the tables

`x2Out_eq_of_tables`: if the tables `fibS`, `fibA` of a source sector agree with the bridge's transferred
tensors on the reads of block `b` (hypotheses `hS0`, `hA0`, `hA1`, `hA2`)
and are bounded, then `x2Out D s N b = (x2OutNum ⋯ c c' / den)`, where `x2OutNum` is computed from the tables and
the packed image columns by the kernel (three parts, `x2PartProj` each). `x2Out_eq_lit` turns a kernel check
`x2OutNum ⋯ = Olit` into `x2Out D s N b = Olit / den`. `x2_hS0_of_table` and its companions derive the
per-block hypotheses from the global table interface `X2TableS`/`X2TableA`.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Slot orders as flat positions -/

/-- Flat position of the ambient point at position `i` of the order `x2Rot0`. -/
def gRot0 (m0 m1 m2 i : ℕ) : ℕ := ((i % m0) * m1 + (i / m0) / m2) * m2 + (i / m0) % m2

/-- Flat position of the ambient point at position `i` of the order `x2Rot1`. -/
def gRot1 (m0 m1 m2 i : ℕ) : ℕ := (((i / m1) / m2) * m1 + i % m1) * m2 + (i / m1) % m2

theorem gRot0_val (x0 x1 x2 m0 m1 m2 : ℕ) (hx0 : x0 < m0) (hx2 : x2 < m2) :
    gRot0 m0 m1 m2 ((x1 * m2 + x2) * m0 + x0) = (x0 * m1 + x1) * m2 + x2 := by
  unfold gRot0
  obtain ⟨h1, h2⟩ := x2o_divmod (x1 * m2 + x2) x0 m0 hx0
  obtain ⟨h3, h4⟩ := x2o_divmod x1 x2 m2 hx2
  rw [h1, h2, h3, h4]

theorem gRot1_val (x0 x1 x2 m0 m1 m2 : ℕ) (hx1 : x1 < m1) (hx2 : x2 < m2) :
    gRot1 m0 m1 m2 ((x0 * m2 + x2) * m1 + x1) = (x0 * m1 + x1) * m2 + x2 := by
  unfold gRot1
  obtain ⟨h1, h2⟩ := x2o_divmod (x0 * m2 + x2) x1 m1 hx1
  obtain ⟨h3, h4⟩ := x2o_divmod x0 x2 m2 hx2
  rw [h1, h2, h3, h4]

theorem jRows_length (W r N : ℕ) (Jcols : List ℕ) (g : ℕ → ℕ) : (jRows W r N Jcols g).length = N := by
  simp [jRows]

theorem jRows_lt (W r N : ℕ) (Jcols : List ℕ) (g : ℕ → ℕ) (hW : 12 ≤ W) :
    ∀ x ∈ jRows W r N Jcols g, x < 2 ^ (W * r) :=
  x2o_mem_map_range N _ (fun f => f < 2 ^ (W * r)) (fun i _ => jRowOf_lt W r Jcols (g i) hW)

theorem jRows_ent (W r N : ℕ) (Jcols : List ℕ) (g : ℕ → ℕ) (i c : ℕ) (hW : 12 ≤ W) (hi : i < N)
    (hc : c < r) : ent W (W - 1) ((jRows W r N Jcols g).getD i 0) c = ent 11 10 (Jcols.getD c 0) (g i) := by
  unfold jRows
  rw [x2o_getD_map_range N i _ hi, jRowOf_ent W r Jcols (g i) c hW hc]

theorem jRows_bound (W r N : ℕ) (Jcols : List ℕ) (g : ℕ → ℕ) (hW : 12 ≤ W) :
    ∀ i < N, ∀ c < r, |ent W (W - 1) ((jRows W r N Jcols g).getD i 0) c| ≤ 2 ^ 10 := by
  intro i hi c hc
  rw [jRows_ent W r N Jcols g i c hW hi hc]
  exact ent11_abs_le _ _

theorem x2Cols_length (m1 m2 n : ℕ) (col : ℕ → ℕ → ℕ → ℕ) : (x2Cols m1 m2 n col).length = n := by
  simp [x2Cols]

/-! ### The three parts of a block -/

/-- Column list of part 0 of block `b`. -/
def x2Part0Cols (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) : List ℕ :=
  x2Cols (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)
    (x2P0Col W d (x2KeyTypes 0 b 0) (x2KeyTypes 0 b 1) (x2KeyTypes 0 b 2) fibS fibA)

/-- Column list of part 1 of block `b`. -/
def x2Part1Cols (W d : ℕ) (b : x2Key 0) (fibA : ℕ → ℕ → ℕ) : List ℕ :=
  x2Cols (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)
    (x2P1Col W d (x2KeyTypes 0 b 0) (x2KeyTypes 0 b 1) (x2KeyTypes 0 b 2) fibA)

/-- Column list of part 2 of block `b`. -/
def x2Part2Cols (W d : ℕ) (b : x2Key 0) (fibA : ℕ → ℕ → ℕ) : List ℕ :=
  x2Cols (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)
    (x2P2Col W d (x2KeyTypes 0 b 0) (x2KeyTypes 0 b 1) (x2KeyTypes 0 b 2) fibA)

/-- Output numerators of block `b` (sum of the three projected parts), computed by the kernel. -/
noncomputable def x2OutNum (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ)
    (c c' : ℕ) : ℤ :=
  ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
      (x2Part0Cols W d b fibS fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)))).getD c' 0) c +
  ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
      (x2Part1Cols W d b fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)))).getD c' 0) c +
  ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
      (x2Part2Cols W d b fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (fun i => i))).getD c' 0) c

/-! ### `x2RawH` entrywise -/

theorem x2RawH_apply (Sh : Fin 282 → Fin 282 → Fin 282 → ℚ) (Ah : Fin 282 → Fin 231 → Fin 231 → ℚ)
    (b : x2Key 0) (x y : x2Amb 0 b) :
    x2RawH Sh Ah b x y =
      Sh (x2SIdx 0 (x2KeyTypes 0 b 0) x.1 y.1) (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1)
          (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) +
        x2Sgn x.2.1 y.2.1 * x2Sgn x.2.2 y.2.2 *
          Ah (x2SIdx 0 (x2KeyTypes 0 b 0) x.1 y.1) (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1)
            (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) +
        x2Sgn x.1 y.1 * x2Sgn x.2.2 y.2.2 *
          Ah (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1)
            (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) +
        x2Sgn x.1 y.1 * x2Sgn x.2.1 y.2.1 *
          Ah (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1)
            (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) := by
  first
  | rfl
  | (simp only [x2RawH, Matrix.of_apply]; rfl)

/-! ### Entries and bounds of the parts -/

section parts

variable (W d bF : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ)

theorem x2Part0_entry (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (x y : x2Amb 0 b)
    (hbS : ∀ s < x2KeyMult 0 b 0, |ent W (W - 1) (fibS (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)
      (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1)) (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + s)| ≤
        2 ^ bF)
    (hbA : (x.2.1 : ℕ) ≠ y.2.1 → (x.2.2 : ℕ) ≠ y.2.2 → ∀ s < x2KeyMult 0 b 0, |ent W (W - 1)
      (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
      (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + s)| ≤ 2 ^ bF) :
    ent W (W - 1) ((x2Part0Cols W d b fibS fibA).getD
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
        (x2Rot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) =
      ent W (W - 1) (fibS (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
          (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + x.1) +
        sgnZ x.2.1 y.2.1 * sgnZ x.2.2 y.2.2 *
          ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
            (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + x.1) := by
  unfold x2Part0Cols
  rw [x2Flat3_val _ _ _ y, x2Cols_getD _ _ _ _ _ _ _ y.1.isLt y.2.1.isLt y.2.2.isLt, x2Rot0_val]
  exact x2P0Col_ent W d bF _ _ _ fibS fibA hW hbF _ _ _ _ _ _ x.1.isLt x.2.1.isLt x.2.2.isLt hbS hbA

theorem x2Part1_entry (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (x y : x2Amb 0 b)
    (hbA : (x.1 : ℕ) ≠ y.1 → (x.2.2 : ℕ) ≠ y.2.2 → ∀ s < x2KeyMult 0 b 1, |ent W (W - 1)
      (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
      (x2UOff0 (x2KeyTypes 0 b 1) + y.2.1 * x2KeyMult 0 b 1 + s)| ≤ 2 ^ bF) :
    ent W (W - 1) ((x2Part1Cols W d b fibA).getD
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
        (x2Rot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) =
      sgnZ x.1 y.1 * sgnZ x.2.2 y.2.2 *
        ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
          (x2UOff0 (x2KeyTypes 0 b 1) + y.2.1 * x2KeyMult 0 b 1 + x.2.1) := by
  unfold x2Part1Cols
  rw [x2Flat3_val _ _ _ y, x2Cols_getD _ _ _ _ _ _ _ y.1.isLt y.2.1.isLt y.2.2.isLt, x2Rot1_val]
  exact x2P1Col_ent W d bF _ _ _ fibA hW hbF _ _ _ _ _ _ x.1.isLt x.2.1.isLt x.2.2.isLt hbA

theorem x2Part2_entry (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (x y : x2Amb 0 b)
    (hbA : (x.1 : ℕ) ≠ y.1 → (x.2.1 : ℕ) ≠ y.2.1 → ∀ s < x2KeyMult 0 b 2, |ent W (W - 1)
      (fibA (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
      (x2UOff0 (x2KeyTypes 0 b 2) + y.2.2 * x2KeyMult 0 b 2 + s)| ≤ 2 ^ bF) :
    ent W (W - 1) ((x2Part2Cols W d b fibA).getD
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) =
      sgnZ x.1 y.1 * sgnZ x.2.1 y.2.1 *
        ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
          (x2UOff0 (x2KeyTypes 0 b 2) + y.2.2 * x2KeyMult 0 b 2 + x.2.2) := by
  unfold x2Part2Cols
  rw [x2Flat3_val _ _ _ y, x2Cols_getD _ _ _ _ _ _ _ y.1.isLt y.2.1.isLt y.2.2.isLt, x2Flat3_val _ _ _ x]
  exact x2P2Col_ent W d bF _ _ _ fibA hW hbF _ _ _ _ _ _ x.1.isLt x.2.1.isLt x.2.2.isLt hbA

end parts

/-! ### Table bounds used by a block -/

/-- Slot positions of an expanded axis-0 table stay below 513. -/
theorem x2UOff0_add_le : ∀ t : Fin 8, x2UOff0 t + x2Mult 0 t * x2Mult 0 t ≤ 513 := by
  decide +kernel

theorem x2UOff0_slot_lt (t : Fin 8) (a s : ℕ) (ha : a < x2Mult 0 t) (hs : s < x2Mult 0 t) :
    x2UOff0 t + a * x2Mult 0 t + s < 513 := by
  have h1 := x2o_lt_mul a s (x2Mult 0 t) (x2Mult 0 t) ha hs
  have h2 := x2UOff0_add_le t
  omega

/-- Bounds of the tables on the reads of block `b` (checked per fiber by `slotBoundCheck` in instances). -/
structure X2BlockBounds (W bF : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) : Prop where
  s0 : ∀ a b' c d : ℕ, a < x2KeyMult 0 b 2 → b' < x2KeyMult 0 b 2 → c < x2KeyMult 0 b 1 →
    d < x2KeyMult 0 b 1 → ∀ u < 513,
      |ent W (W - 1) (fibS (x2SIdx 0 (x2KeyTypes 0 b 2) a b') (x2SIdx 0 (x2KeyTypes 0 b 1) c d)) u| ≤ 2 ^ bF
  a0 : ∀ a b' c d : ℕ, a < x2KeyMult 0 b 2 → b' < x2KeyMult 0 b 2 → c < x2KeyMult 0 b 1 →
    d < x2KeyMult 0 b 1 → a ≠ b' → c ≠ d → ∀ u < 513,
      |ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) a b') (x2AIdx 0 (x2KeyTypes 0 b 1) c d)) u| ≤ 2 ^ bF
  a1 : ∀ a b' c d : ℕ, a < x2KeyMult 0 b 2 → b' < x2KeyMult 0 b 2 → c < x2KeyMult 0 b 0 →
    d < x2KeyMult 0 b 0 → a ≠ b' → c ≠ d → ∀ u < 513,
      |ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) a b') (x2AIdx 0 (x2KeyTypes 0 b 0) c d)) u| ≤ 2 ^ bF
  a2 : ∀ a b' c d : ℕ, a < x2KeyMult 0 b 1 → b' < x2KeyMult 0 b 1 → c < x2KeyMult 0 b 0 →
    d < x2KeyMult 0 b 0 → a ≠ b' → c ≠ d → ∀ u < 513,
      |ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 1) a b') (x2AIdx 0 (x2KeyTypes 0 b 0) c d)) u| ≤ 2 ^ bF

/-! ### The block theorem -/

/-- The table interface on the reads of block `b`. -/
structure X2BlockIface (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0) (W : ℕ) (den : ℚ)
    (fibS fibA : ℕ → ℕ → ℕ) : Prop where
  s0 : ∀ x y : x2Amb 0 b,
      x2TransferS D s Nsrc (x2SIdx 0 (x2KeyTypes 0 b 0) x.1 y.1) (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1)
          (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) =
        (ent W (W - 1) (fibS (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
          (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + x.1) : ℚ) / den
  a0 : ∀ x y : x2Amb 0 b, (x.2.1 : ℕ) ≠ y.2.1 → (x.2.2 : ℕ) ≠ y.2.2 →
      x2TransferA D s Nsrc (x2SIdx 0 (x2KeyTypes 0 b 0) x.1 y.1) (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1)
          (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) =
        (ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
          (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + x.1) : ℚ) / den
  a1 : ∀ x y : x2Amb 0 b, (x.1 : ℕ) ≠ y.1 → (x.2.2 : ℕ) ≠ y.2.2 →
      x2TransferA D s Nsrc (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1)
          (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) =
        (ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
          (x2UOff0 (x2KeyTypes 0 b 1) + y.2.1 * x2KeyMult 0 b 1 + x.2.1) : ℚ) / den
  a2 : ∀ x y : x2Amb 0 b, (x.1 : ℕ) ≠ y.1 → (x.2.1 : ℕ) ≠ y.2.1 →
      x2TransferA D s Nsrc (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1)
          (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) =
        (ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
          (x2UOff0 (x2KeyTypes 0 b 2) + y.2.2 * x2KeyMult 0 b 2 + x.2.2) : ℚ) / den

/-- The image of block `b` read from packed columns (11-bit slots, offset `2^10`, flat row-major index). -/
def X2ImageCols (D : X2Data) (b : x2Key 0) (Jcols : List ℕ) : Prop :=
  ∀ x c, D.image 0 b x c = ent 11 10 (Jcols.getD c 0) (x2FlatIndex x)

theorem x2Out_eq_of_tables (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0)
    (W d bF : ℕ) (den : ℚ) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ)
    (hW : 12 ≤ W) (hbF : bF + 3 ≤ W) (hJc : Jcols.length = x2KeySize 0 b)
    (hJ : X2ImageCols D b Jcols)
    (hI : X2BlockIface D s Nsrc b W den fibS fibA)
    (hB : X2BlockBounds W bF b fibS fibA)
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) <
      2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1)) :
    x2Out D s Nsrc b = Matrix.of fun (c c' : x2Col 0 b) =>
      ((x2OutNum W d b fibS fibA Jcols c c' : ℤ) : ℚ) / den := by
  have hW2 : 2 ≤ W := by omega
  obtain ⟨hS0, hA0, hA1, hA2⟩ := hI
  -- the bounds used by each part, at an entry `(x, y)`
  have hbS0 : ∀ x y : x2Amb 0 b, ∀ s < x2KeyMult 0 b 0, |ent W (W - 1)
      (fibS (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
      (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + s)| ≤ 2 ^ bF := fun x y s hs =>
    hB.s0 _ _ _ _ x.2.2.isLt y.2.2.isLt x.2.1.isLt y.2.1.isLt _ (x2UOff0_slot_lt _ _ _ y.1.isLt hs)
  have hbA0 : ∀ x y : x2Amb 0 b, (x.2.1 : ℕ) ≠ y.2.1 → (x.2.2 : ℕ) ≠ y.2.2 → ∀ s < x2KeyMult 0 b 0,
      |ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1))
        (x2UOff0 (x2KeyTypes 0 b 0) + y.1 * x2KeyMult 0 b 0 + s)| ≤ 2 ^ bF := fun x y h1 h2 s hs =>
    hB.a0 _ _ _ _ x.2.2.isLt y.2.2.isLt x.2.1.isLt y.2.1.isLt h2 h1 _ (x2UOff0_slot_lt _ _ _ y.1.isLt hs)
  have hbA1 : ∀ x y : x2Amb 0 b, (x.1 : ℕ) ≠ y.1 → (x.2.2 : ℕ) ≠ y.2.2 → ∀ s < x2KeyMult 0 b 1,
      |ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
        (x2UOff0 (x2KeyTypes 0 b 1) + y.2.1 * x2KeyMult 0 b 1 + s)| ≤ 2 ^ bF := fun x y h1 h2 s hs =>
    hB.a1 _ _ _ _ x.2.2.isLt y.2.2.isLt x.1.isLt y.1.isLt h2 h1 _ (x2UOff0_slot_lt _ _ _ y.2.1.isLt hs)
  have hbA2 : ∀ x y : x2Amb 0 b, (x.1 : ℕ) ≠ y.1 → (x.2.1 : ℕ) ≠ y.2.1 → ∀ s < x2KeyMult 0 b 2,
      |ent W (W - 1) (fibA (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1) (x2AIdx 0 (x2KeyTypes 0 b 0) x.1 y.1))
        (x2UOff0 (x2KeyTypes 0 b 2) + y.2.2 * x2KeyMult 0 b 2 + s)| ≤ 2 ^ bF := fun x y h1 h2 s hs =>
    hB.a2 _ _ _ _ x.2.1.isLt y.2.1.isLt x.1.isLt y.1.isLt h2 h1 _ (x2UOff0_slot_lt _ _ _ y.2.2.isLt hs)
  -- entries of the parts and their bounds
  have he0 := fun x y => x2Part0_entry W d bF b fibS fibA hW2 hbF x y (hbS0 x y) (hbA0 x y)
  have he1 := fun x y => x2Part1_entry W d bF b fibA hW2 hbF x y (hbA1 x y)
  have he2 := fun x y => x2Part2_entry W d bF b fibA hW2 hbF x y (hbA2 x y)
  have hpos : (0 : ℤ) ≤ 2 ^ (bF + 1) := by positivity
  -- the image matrix
  have hJm : (D.image 0 b).map (Int.cast : ℤ → ℚ) = Matrix.of fun (x : x2Amb 0 b) (c : Fin (x2KeySize 0 b)) =>
      (ent 11 10 (Jcols.getD c 0) (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) : ℚ) := by
    ext x c
    simp only [Matrix.map_apply, Matrix.of_apply, hJ x c, x2Flat3_val, x2FlatIndex]
  -- x2RawH as the sum of the three parts
  have hRaw : x2RawH (x2TransferS D s Nsrc) (x2TransferA D s Nsrc) b =
      (Matrix.of fun (x y : x2Amb 0 b) => (ent W (W - 1) ((x2Part0Cols W d b fibS fibA).getD
          (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
          (x2Rot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) : ℚ) / den) +
      (Matrix.of fun (x y : x2Amb 0 b) => (ent W (W - 1) ((x2Part1Cols W d b fibA).getD
          (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
          (x2Rot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) : ℚ) / den) +
      (Matrix.of fun (x y : x2Amb 0 b) => (ent W (W - 1) ((x2Part2Cols W d b fibA).getD
          (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
          (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) : ℚ) / den) := by
    ext x y
    rw [x2RawH_apply]
    simp only [Matrix.add_apply, Matrix.of_apply]
    rw [he0 x y, he1 x y, he2 x y, hS0 x y,
      x2o_sgn_term _ _ _ _ _ _ den (hA0 x y), x2o_sgn_term _ _ _ _ _ _ den (hA1 x y),
      x2o_sgn_term _ _ _ _ _ _ den (hA2 x y)]
    push_cast
    ring
  -- slot bounds of the column lists, by the entry formulas at `(x, y) = (e⁻¹ k, f⁻¹ i)`
  have hX0b : ∀ i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      ∀ k < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      |ent W (W - 1) ((x2Part0Cols W d b fibS fibA).getD i 0) k| ≤ 2 ^ (bF + 1) := by
    intro i hi k hk
    obtain ⟨x, rfl⟩ : ∃ x : x2Amb 0 b,
        (x2Rot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x : ℕ) = k :=
      ⟨(x2Rot0 _ _ _).symm ⟨k, hk⟩, by simp⟩
    obtain ⟨y, rfl⟩ : ∃ y : x2Amb 0 b,
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y : ℕ) = i :=
      ⟨(x2Flat3 _ _ _).symm ⟨i, hi⟩, by simp⟩
    rw [he0 x y]
    exact (x2o_bound2 _ _ _ bF W hbF (hbS0 x y x.1 x.1.isLt) (abs_sgnZ_mul_le _ _ _ _)
      (fun h0 => hbA0 x y (x2o_ne_of_sgn _ _ _ _ h0).1 (x2o_ne_of_sgn _ _ _ _ h0).2 x.1 x.1.isLt)).1
  have hX1b : ∀ i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      ∀ k < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      |ent W (W - 1) ((x2Part1Cols W d b fibA).getD i 0) k| ≤ 2 ^ (bF + 1) := by
    intro i hi k hk
    obtain ⟨x, rfl⟩ : ∃ x : x2Amb 0 b,
        (x2Rot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x : ℕ) = k :=
      ⟨(x2Rot1 _ _ _).symm ⟨k, hk⟩, by simp⟩
    obtain ⟨y, rfl⟩ : ∃ y : x2Amb 0 b,
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y : ℕ) = i :=
      ⟨(x2Flat3 _ _ _).symm ⟨i, hi⟩, by simp⟩
    rw [he1 x y]
    exact x2o_bound1 _ _ bF (abs_sgnZ_mul_le _ _ _ _)
      (fun h0 => hbA1 x y (x2o_ne_of_sgn _ _ _ _ h0).1 (x2o_ne_of_sgn _ _ _ _ h0).2 x.2.1 x.2.1.isLt)
  have hX2b : ∀ i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      ∀ k < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      |ent W (W - 1) ((x2Part2Cols W d b fibA).getD i 0) k| ≤ 2 ^ (bF + 1) := by
    intro i hi k hk
    obtain ⟨x, rfl⟩ : ∃ x : x2Amb 0 b,
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x : ℕ) = k :=
      ⟨(x2Flat3 _ _ _).symm ⟨k, hk⟩, by simp⟩
    obtain ⟨y, rfl⟩ : ∃ y : x2Amb 0 b,
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y : ℕ) = i :=
      ⟨(x2Flat3 _ _ _).symm ⟨i, hi⟩, by simp⟩
    rw [he2 x y]
    exact x2o_bound1 _ _ bF (abs_sgnZ_mul_le _ _ _ _)
      (fun h0 => hbA2 x y (x2o_ne_of_sgn _ _ _ _ h0).1 (x2o_ne_of_sgn _ _ _ _ h0).2 x.2.2 x.2.2.isLt)
  -- ranges of the column lists
  have hX0lt : ∀ z ∈ x2Part0Cols W d b fibS fibA,
      z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)) := by
    unfold x2Part0Cols x2Cols
    exact x2o_mem_map_range _ _ (fun z => z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)))
      (fun i _ => lt_of_lt_of_eq (colOfPieces_lt _ _ _ _ _) (by congr 1; ring))
  have hX1lt : ∀ z ∈ x2Part1Cols W d b fibA,
      z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)) := by
    unfold x2Part1Cols x2Cols
    exact x2o_mem_map_range _ _ (fun z => z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)))
      (fun i _ => lt_of_lt_of_eq (colOfPieces_lt _ _ _ _ _) (by congr 1; ring))
  have hX2lt : ∀ z ∈ x2Part2Cols W d b fibA,
      z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)) := by
    unfold x2Part2Cols x2Cols
    exact x2o_mem_map_range _ _ (fun z => z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)))
      (fun i _ => lt_of_lt_of_eq (colOfPieces_lt _ _ _ _ _) (by congr 1; ring))
  -- rows of the image in each order
  have hJrow0 : ∀ (x : x2Amb 0 b) (c : ℕ), c < x2KeySize 0 b →
      ent W (W - 1) ((jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2))).getD
          (x2Rot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) 0) c =
        ent 11 10 (Jcols.getD c 0) (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) := by
    intro x c hc
    rw [jRows_ent W _ _ Jcols _ _ c hW (Fin.isLt _) hc, x2Rot0_val, x2Flat3_val,
      gRot0_val _ _ _ _ _ _ x.1.isLt x.2.2.isLt]
  have hJrow1 : ∀ (x : x2Amb 0 b) (c : ℕ), c < x2KeySize 0 b →
      ent W (W - 1) ((jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2))).getD
          (x2Rot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) 0) c =
        ent 11 10 (Jcols.getD c 0) (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) := by
    intro x c hc
    rw [jRows_ent W _ _ Jcols _ _ c hW (Fin.isLt _) hc, x2Rot1_val, x2Flat3_val,
      gRot1_val _ _ _ _ _ _ x.2.1.isLt x.2.2.isLt]
  have hJrow2 : ∀ (x : x2Amb 0 b) (c : ℕ), c < x2KeySize 0 b →
      ent W (W - 1) ((jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (fun i => i)).getD (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) 0) c =
        ent 11 10 (Jcols.getD c 0) (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) := by
    intro x c hc
    rw [jRows_ent W _ _ Jcols _ _ c hW (Fin.isLt _) hc]
  -- assemble
  unfold x2Out
  simp only []
  rw [hJm, hRaw]
  simp only [Matrix.mul_add, Matrix.add_mul]
  ext c c'
  simp only [Matrix.add_apply, Matrix.of_apply]
  have hl0 : (x2Part0Cols W d b fibS fibA).length = x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 := by
    unfold x2Part0Cols
    exact x2Cols_length _ _ _ _
  have hl1 : (x2Part1Cols W d b fibA).length = x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 := by
    unfold x2Part1Cols
    exact x2Cols_length _ _ _ _
  have hl2 : (x2Part2Cols W d b fibA).length = x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 := by
    unfold x2Part2Cols
    exact x2Cols_length _ _ _ _
  rw [x2PartProj W _ _ (x2Rot0 _ _ _) (x2Flat3 _ _ _) Jcols (x2Part0Cols W d b fibS fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)))
      den (2 ^ (bF + 1)) hW hJc hl0 (jRows_length _ _ _ _ _) hX0lt (jRows_lt _ _ _ _ _ hW) hX0b hpos hJrow0
      (jRows_bound _ _ _ _ _ hW) hb1 hb2 c c',
    x2PartProj W _ _ (x2Rot1 _ _ _) (x2Flat3 _ _ _) Jcols (x2Part1Cols W d b fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)))
      den (2 ^ (bF + 1)) hW hJc hl1 (jRows_length _ _ _ _ _) hX1lt (jRows_lt _ _ _ _ _ hW) hX1b hpos hJrow1
      (jRows_bound _ _ _ _ _ hW) hb1 hb2 c c',
    x2PartProj W _ _ (x2Flat3 _ _ _) (x2Flat3 _ _ _) Jcols (x2Part2Cols W d b fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols (fun i => i))
      den (2 ^ (bF + 1)) hW hJc hl2 (jRows_length _ _ _ _ _) hX2lt (jRows_lt _ _ _ _ _ hW) hX2b hpos hJrow2
      (jRows_bound _ _ _ _ _ hW) hb1 hb2 c c']
  unfold x2OutNum
  push_cast
  ring

/-- With a kernel check of the numerators: `x2Out D s N b = Olit / den`. -/
theorem x2Out_eq_lit (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0)
    (W d : ℕ) (den : ℚ) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ) (Olit : ℕ → ℕ → ℤ)
    (h : x2Out D s Nsrc b = Matrix.of fun (c c' : x2Col 0 b) =>
      ((x2OutNum W d b fibS fibA Jcols c c' : ℤ) : ℚ) / den)
    (hchk : ∀ c < x2KeySize 0 b, ∀ c' < x2KeySize 0 b, x2OutNum W d b fibS fibA Jcols c c' = Olit c c') :
    x2Out D s Nsrc b = Matrix.of fun (c c' : x2Col 0 b) => ((Olit c c' : ℤ) : ℚ) / den := by
  rw [h]
  ext c c'
  simp only [Matrix.of_apply]
  rw [hchk c c.isLt c' c'.isLt]

end X2
end ThreeCopyQutritWerner
