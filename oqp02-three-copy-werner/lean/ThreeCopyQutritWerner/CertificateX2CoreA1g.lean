module

public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkF_0
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkF_1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_0
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_2
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_3
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_4
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_5
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_6
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkA_7
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_0
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_2
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_3
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_4
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_5
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_6
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkR_7
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_0
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_2
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_3
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_4
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_5
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_6
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkB_7
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkK_0
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_0
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_2
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_3
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_4
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_5
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_6
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_7
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_8
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_9
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_10
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_11
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_12
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_13
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_14
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_15
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_16
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_17
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_18
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_19
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_20
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_21
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_22
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_23
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_24
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_25
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_26
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_27
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_28
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_29
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_30
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_31
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_32
public import ThreeCopyQutritWerner.CertificateX2CoreA1gChkC_33
public import ThreeCopyQutritWerner.CertificateX2CoreA1gShape
public import ThreeCopyQutritWerner.CertificateX2CoreA1gCs

@[expose] public section


/-! Batched core A1g: the three-stage contraction chain (kernel-checked tables). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

/-- The batched contraction chain for the packed tables of this pipeline (pairs `pOK tl tl j k`). -/
theorem chain (i : Fin 513) (j : Fin 231) (k : Fin 231) (hP : pOK tl tl j.val k.val = true) :
    x2Axis0 (fun (i : Fin 513) (a : Fin 282) => ((((r0exp.getD i []).getD a 0 : ℤ) - 2 ^ 31 : ℤ) : ℚ) / 57153600)
      (x2Axis1 (fun (j : Fin 231) (b : Fin 231) => ((((transA1Tab.getD j []).getD b 0 : ℤ) - 2 ^ 31 : ℤ) : ℚ) / 57153600)
        (x2Axis2 (fun (k : Fin 231) (c : Fin 231) => ((((transA1Tab.getD k []).getD c 0 : ℤ) - 2 ^ 31 : ℤ) : ℚ) / 57153600)
          (fun (i : Fin 282) (j : Fin 231) (c : Fin 231) =>
            (ent 384 (384 - 1) (x2Tab f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000))) i j k =
      (ent 384 (384 - 1) (x2Tab t3 k j) i : ℚ) / (57153600 * (57153600 * (57153600 * 1108531032609225922165724911675932935547910848716289179910144000))) := by
  obtain ⟨hR2, hR2r, hR1, hR1r, hR0, hR0r, hF0, hF0r, hG, hGr, hH, hHr, hO, hOr, hT3, hT3r⟩ := shapes
  obtain ⟨s2, s1, s0⟩ := scal
  have hF0b := x2b_bounds_of_flat 384 228 21714 3 231 f0 (by norm_num) (fun t ht => (x2c_join _ 0 576 693 chkF_0 chkF_1) t (Nat.zero_le t) ht)
  exact x2ChainB 384 282 77 3 3 231 231 513 31 transA1Tab transA1Tab r0exp f0 g h o t3 cs
    (fun j k => pOK tl tl j k = true) 57153600 57153600 57153600 1108531032609225922165724911675932935547910848716289179910144000
    (2 ^ 31) (2 ^ 31) (2 ^ 31) (2 ^ 228) (by norm_num) (by norm_num) (by norm_num)
    hR2 (fun o ho => x2c_rows_len transA1Tab 231 hR2r o (by rw [hR2]; exact ho))
    hR1 (fun o ho => x2c_rows_len transA1Tab 231 hR1r o (by rw [hR1]; exact ho))
    (fun o ho c hc => x2c_scalar_bound transA1Tab 31 s2 o (by rw [hR2]; exact ho) c
      (by rw [x2c_rows_len transA1Tab 231 hR2r o (by rw [hR2]; exact ho)]; exact hc))
    (fun o ho c hc => x2c_scalar_bound transA1Tab 31 s1 o (by rw [hR1]; exact ho) c
      (by rw [x2c_rows_len transA1Tab 231 hR1r o (by rw [hR1]; exact ho)]; exact hc))
    (fun o ho c hc => x2c_scalar_bound r0exp 31 s0 o (by rw [hR0]; exact ho) c
      (by rw [x2c_rows_len r0exp 282 hR0r o (by rw [hR0]; exact ho)]; exact hc))
    (fun r hr => x2c_rows_len f0 231 hF0r r (by rw [hF0]; exact hr))
    (fun r hr c hc => (hF0b r hr c hc).1)
    (fun r hr c hc s hs => (hF0b r hr c hc).2 s hs)
    (fun r hr => x2c_rows_len g 231 hGr r (by rw [hG]; exact hr))
    (x2b_rows_of_flat 384 21714 31 3 231 transA1Tab f0 g hR2
      (fun r hr => x2c_rows_len g 231 hGr r (by rw [hG]; exact hr)) (fun t ht => (x2c_join _ 0 96 693 chkA_0 (x2c_join _ 96 192 693 chkA_1 (x2c_join _ 192 288 693 chkA_2 (x2c_join _ 288 384 693 chkA_3 (x2c_join _ 384 480 693 chkA_4 (x2c_join _ 480 576 693 chkA_5 (x2c_join _ 576 672 693 chkA_6 chkA_7))))))) t (Nat.zero_le t) ht))
    (fun r hr => x2c_rows_len h 231 hHr r (by rw [hH]; exact hr))
    (x2b_regroup_of_flat 384 282 77 3 231 g h (fun t ht => (x2c_join _ 0 96 693 chkR_0 (x2c_join _ 96 192 693 chkR_1 (x2c_join _ 192 288 693 chkR_2 (x2c_join _ 288 384 693 chkR_3 (x2c_join _ 384 480 693 chkR_4 (x2c_join _ 480 576 693 chkR_5 (x2c_join _ 576 672 693 chkR_6 chkR_7))))))) t (Nat.zero_le t) ht))
    (fun r hr => x2c_rows_len o 231 hOr r (by rw [hO]; exact hr))
    (x2b_rows_of_flat 384 21714 31 3 231 transA1Tab h o hR1
      (fun r hr => x2c_rows_len o 231 hOr r (by rw [hO]; exact hr)) (fun t ht => (x2c_join _ 0 96 693 chkB_0 (x2c_join _ 96 192 693 chkB_1 (x2c_join _ 192 288 693 chkB_2 (x2c_join _ 288 384 693 chkB_3 (x2c_join _ 384 480 693 chkB_4 (x2c_join _ 480 576 693 chkB_5 (x2c_join _ 576 672 693 chkB_6 chkB_7))))))) t (Nat.zero_le t) ht))
    cs_len
    (fun x hx => by
      have := List.all_eq_true.mp cs_lt x hx
      simpa using this)
    (cols_of_rows 384 31 282 513 cs r0exp cs_len
      (fun r hr => x2c_rows_len r0exp 282 hR0r r (by rw [hR0]; exact hr)) (fun t ht => chkK_0 t (Nat.zero_le t) ht))
    (x2b_slots_of_flat 384 282 513 77 231 231 cs o t3 tl tl (fun t ht => (x2c_join _ 0 1600 53361 chkC_0 (x2c_join _ 1600 3200 53361 chkC_1 (x2c_join _ 3200 4800 53361 chkC_2 (x2c_join _ 4800 6400 53361 chkC_3 (x2c_join _ 6400 8000 53361 chkC_4 (x2c_join _ 8000 9600 53361 chkC_5 (x2c_join _ 9600 11200 53361 chkC_6 (x2c_join _ 11200 12800 53361 chkC_7 (x2c_join _ 12800 14400 53361 chkC_8 (x2c_join _ 14400 16000 53361 chkC_9 (x2c_join _ 16000 17600 53361 chkC_10 (x2c_join _ 17600 19200 53361 chkC_11 (x2c_join _ 19200 20800 53361 chkC_12 (x2c_join _ 20800 22400 53361 chkC_13 (x2c_join _ 22400 24000 53361 chkC_14 (x2c_join _ 24000 25600 53361 chkC_15 (x2c_join _ 25600 27200 53361 chkC_16 (x2c_join _ 27200 28800 53361 chkC_17 (x2c_join _ 28800 30400 53361 chkC_18 (x2c_join _ 30400 32000 53361 chkC_19 (x2c_join _ 32000 33600 53361 chkC_20 (x2c_join _ 33600 35200 53361 chkC_21 (x2c_join _ 35200 36800 53361 chkC_22 (x2c_join _ 36800 38400 53361 chkC_23 (x2c_join _ 38400 40000 53361 chkC_24 (x2c_join _ 40000 41600 53361 chkC_25 (x2c_join _ 41600 43200 53361 chkC_26 (x2c_join _ 43200 44800 53361 chkC_27 (x2c_join _ 44800 46400 53361 chkC_28 (x2c_join _ 46400 48000 53361 chkC_29 (x2c_join _ 48000 49600 53361 chkC_30 (x2c_join _ 49600 51200 53361 chkC_31 (x2c_join _ 51200 52800 53361 chkC_32 chkC_33))))))))))))))))))))))))))))))))) t (Nat.zero_le t) ht))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) i j k hP

end ThreeCopyQutritWerner.X2.CoreA1g
