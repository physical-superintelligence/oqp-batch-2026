module

public import ThreeCopyQutritWerner.CertificateX2CoreS1g
public import ThreeCopyQutritWerner.CertificateX2Data

@[expose] public section


/-! Batched core S1g: the bridge x2TransferS at the sector-0 units, given the input stage hT0. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem rS : (x2DataConcrete.transS 1 : Matrix (Fin 282) (Fin 282) ℚ) =
    fun (k : Fin 282) (c : Fin 282) => ((((transS1Tab.getD k []).getD c 0 : ℤ) - 2 ^ 31 : ℤ) : ℚ) / 57153600 := by
  funext k c
  simp [x2DataConcrete, x2TransS, transSNum, transSRows, transDen]

theorem tl_types : ∀ l : Fin 282, tl.getD l 0 = ((x2SLabel 0 l).1 : ℕ) := by
  decide +kernel

/-- The transferred tensor at the axis-0 S-label `sel u` (expanded unit `u`), given the input stage. -/
theorem transfer_sel (N : X2Blocks 1)
    (hT0 : ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 1 N i j c =
      (ent 384 (384 - 1) (x2Tab f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000)
    (u : Fin 513) (j k : Fin 282) (hP : pOK tl tl j.val k.val = true) :
    x2TransferS x2DataConcrete 1 N ⟨sel.getD u 0, sel_lt u u.isLt⟩ j k =
      (ent 384 (384 - 1) (x2Tab t3 k j) u : ℚ) / (57153600 * (57153600 * (57153600 * 1108531032609225922165724911675932935547910848716289179910144000))) := by
  have hE : x2EmbedS x2DataConcrete 1 N = (fun (i : Fin 282) (j : Fin 282) (c : Fin 282) =>
            (ent 384 (384 - 1) (x2Tab f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000) := by
    funext i j c
    exact hT0 i j c
  rw [← chain u j k hP]
  show x2Axis0 (x2DataConcrete.transS 1) (x2Axis1 (x2DataConcrete.transS 1)
      (x2Axis2 (x2DataConcrete.transS 1) (x2EmbedS x2DataConcrete 1 N))) _ j k = _
  rw [hE, rS]
  unfold x2Axis0
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  show (((((transS1Tab.getD (sel.getD u 0) []).getD a 0 : ℤ) - 2 ^ 31 : ℤ) : ℚ) / 57153600) =
    (((((r0exp.getD u []).getD a 0 : ℤ) - 2 ^ 31 : ℤ) : ℚ) / 57153600)
  rw [r0exp_rows u u.isLt]

/-- the transferred tensor at axis-0 label `x2SIdx 0 t a b`, pairs of types
`type j ≤ type k`, given the input stage `hT0`. -/
theorem transfer_unit (N : X2Blocks 1)
    (hT0 : ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 1 N i j c =
      (ent 384 (384 - 1) (x2Tab f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000)
    (t : Fin 8) (aa b : Fin (x2Mult 0 t)) (j k : Fin 282)
    (hP : ((x2SLabel 0 j).1 : ℕ) ≤ ((x2SLabel 0 k).1 : ℕ)) :
    x2TransferS x2DataConcrete 1 N (x2SIdx 0 t aa b) j k =
      (ent 384 (384 - 1) (x2Tab t3 k j) (x2UOff0 t + aa * x2Mult 0 t + b) : ℚ) /
        (57153600 * (57153600 * (57153600 * 1108531032609225922165724911675932935547910848716289179910144000))) := by
  have hu := unit_lt t aa b
  have e : x2SIdx 0 t aa b = ⟨sel.getD (x2UOff0 t + aa * x2Mult 0 t + b) 0, sel_lt _ hu⟩ :=
    Fin.ext (sel_sidx t aa b).symm
  have hP' : pOK tl tl j.val k.val = true := by
    unfold pOK
    rw [tl_types j, tl_types k]
    exact Nat.ble_eq_true_of_le hP
  rw [e]
  exact transfer_sel N hT0 ⟨_, hu⟩ j k hP'

/-- The fibers of the expanded axis-0 table. -/
noncomputable def fib (k j : ℕ) : ℕ := x2Tab t3 k j

/-- The common denominator of the expanded axis-0 table. -/
def den : ℚ := 57153600 * (57153600 * (57153600 * 1108531032609225922165724911675932935547910848716289179910144000))

/-- global form. -/
theorem transfer_global (N : X2Blocks 1)
    (hT0 : ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 1 N i j c =
      (ent 384 (384 - 1) (x2Tab f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000) :
    ∀ (t : Fin 8) (a b : ℕ) (j k : Fin 282), a < x2Mult 0 t → b < x2Mult 0 t →
      (x2SLabel 0 j).1 ≤ (x2SLabel 0 k).1 →
      x2TransferS x2DataConcrete 1 N (x2SIdx 0 t a b) j k =
        (ent 384 (384 - 1) (fib k j) (x2UOff0 t + a * x2Mult 0 t + b) : ℚ) / den := by
  intro t a b j k ha hb hjk
  exact transfer_unit N hT0 t ⟨a, ha⟩ ⟨b, hb⟩ j k (Fin.le_iff_val_le_val.mp hjk)

end ThreeCopyQutritWerner.X2.CoreS1g
