module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [5, 10). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col5_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 0 v) = true := by decide +kernel
theorem col5_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 1 v) = true := by decide +kernel
theorem s5_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 0 = true := by decide +kernel
theorem s5_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 1 = true := by decide +kernel
theorem s5_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 2 = true := by decide +kernel
theorem s5_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 3 = true := by decide +kernel
theorem k5_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 2 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k5_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 2 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k5_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 2 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s5_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 2 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k5_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 2 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k5_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 2 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k5_2_4_80 k h.1 (by omega)
theorem s5_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 5 = true := by decide +kernel
theorem s5_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 6 = true := by decide +kernel
theorem s5_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 2 7 = true := by decide +kernel
theorem s5_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 0 = true := by decide +kernel
theorem s5_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 1 = true := by decide +kernel
theorem s5_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 2 = true := by decide +kernel
theorem s5_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 3 = true := by decide +kernel
theorem k5_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 3 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k5_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 3 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k5_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 3 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s5_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 3 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k5_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 3 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k5_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 3 4).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k5_3_4_80 k h.1 (by omega)
theorem s5_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 5 = true := by decide +kernel
theorem s5_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 6 = true := by decide +kernel
theorem s5_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 3 7 = true := by decide +kernel
theorem s5_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 0 = true := by decide +kernel
theorem s5_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 1 = true := by decide +kernel
theorem s5_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 2 = true := by decide +kernel
theorem s5_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 3 = true := by decide +kernel
theorem s5_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 4 = true := by decide +kernel
theorem k5_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k5_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k5_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k5_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k5_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k5_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k5_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k5_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k5_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s5_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k5_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k5_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k5_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k5_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k5_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k5_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k5_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k5_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 5).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k5_4_5_40 k h.1 (by omega)
theorem k5_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k5_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k5_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k5_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k5_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k5_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k5_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k5_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k5_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k5_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k5_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s5_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k5_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k5_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k5_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k5_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k5_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k5_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k5_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k5_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k5_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k5_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 4 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k5_4_6_50 k h.1 (by omega)
theorem s5_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 4 7 = true := by decide +kernel
theorem s5_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 0 = true := by decide +kernel
theorem s5_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 1 = true := by decide +kernel
theorem s5_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 2 = true := by decide +kernel
theorem s5_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 3 = true := by decide +kernel
theorem s5_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 4 = true := by decide +kernel
theorem s5_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 5 = true := by decide +kernel
theorem k5_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k5_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k5_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k5_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k5_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k5_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s5_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k5_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k5_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k5_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k5_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k5_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 5) ((InDA2.TCasaD 1 5 6).getD (5 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k5_5_6_50 k h.1 (by omega)
theorem s5_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 5 7 = true := by decide +kernel
theorem col5_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 6 v) = true := by decide +kernel
theorem col5_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 7 v) = true := by decide +kernel
theorem col5 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 5) 5 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col5_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col5_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s5_2_0
    · exact s5_2_1
    · exact s5_2_2
    · exact s5_2_3
    · exact s5_2_4
    · exact s5_2_5
    · exact s5_2_6
    · exact s5_2_7
  · fin_cases v
    · exact s5_3_0
    · exact s5_3_1
    · exact s5_3_2
    · exact s5_3_3
    · exact s5_3_4
    · exact s5_3_5
    · exact s5_3_6
    · exact s5_3_7
  · fin_cases v
    · exact s5_4_0
    · exact s5_4_1
    · exact s5_4_2
    · exact s5_4_3
    · exact s5_4_4
    · exact s5_4_5
    · exact s5_4_6
    · exact s5_4_7
  · fin_cases v
    · exact s5_5_0
    · exact s5_5_1
    · exact s5_5_2
    · exact s5_5_3
    · exact s5_5_4
    · exact s5_5_5
    · exact s5_5_6
    · exact s5_5_7
  · exact List.all_eq_true.mp col5_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col5_7 v (List.mem_finRange v)
theorem col6_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 0 v) = true := by decide +kernel
theorem col6_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 1 v) = true := by decide +kernel
theorem s6_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 0 = true := by decide +kernel
theorem s6_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 1 = true := by decide +kernel
theorem s6_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 2 = true := by decide +kernel
theorem s6_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 3 = true := by decide +kernel
theorem k6_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 2 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k6_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 2 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k6_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 2 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s6_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 2 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k6_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 2 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k6_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 2 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k6_2_4_80 k h.1 (by omega)
theorem s6_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 5 = true := by decide +kernel
theorem s6_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 6 = true := by decide +kernel
theorem s6_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 2 7 = true := by decide +kernel
theorem s6_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 0 = true := by decide +kernel
theorem s6_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 1 = true := by decide +kernel
theorem s6_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 2 = true := by decide +kernel
theorem s6_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 3 = true := by decide +kernel
theorem k6_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 3 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k6_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 3 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k6_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 3 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s6_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 3 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k6_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 3 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k6_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 3 4).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k6_3_4_80 k h.1 (by omega)
theorem s6_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 5 = true := by decide +kernel
theorem s6_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 6 = true := by decide +kernel
theorem s6_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 3 7 = true := by decide +kernel
theorem s6_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 0 = true := by decide +kernel
theorem s6_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 1 = true := by decide +kernel
theorem s6_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 2 = true := by decide +kernel
theorem s6_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 3 = true := by decide +kernel
theorem s6_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 4 = true := by decide +kernel
theorem k6_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k6_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k6_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k6_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k6_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k6_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k6_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k6_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k6_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s6_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k6_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k6_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k6_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k6_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k6_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k6_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k6_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k6_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 5).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k6_4_5_40 k h.1 (by omega)
theorem k6_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k6_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k6_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k6_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k6_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k6_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k6_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k6_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k6_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k6_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k6_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s6_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k6_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k6_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k6_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k6_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k6_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k6_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k6_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k6_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k6_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k6_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 4 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k6_4_6_50 k h.1 (by omega)
theorem s6_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 4 7 = true := by decide +kernel
theorem s6_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 0 = true := by decide +kernel
theorem s6_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 1 = true := by decide +kernel
theorem s6_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 2 = true := by decide +kernel
theorem s6_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 3 = true := by decide +kernel
theorem s6_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 4 = true := by decide +kernel
theorem s6_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 5 = true := by decide +kernel
theorem k6_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k6_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k6_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k6_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k6_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k6_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s6_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k6_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k6_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k6_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k6_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k6_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 6) ((InDA2.TCasaD 2 5 6).getD (6 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k6_5_6_50 k h.1 (by omega)
theorem s6_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 5 7 = true := by decide +kernel
theorem col6_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 6 v) = true := by decide +kernel
theorem col6_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 7 v) = true := by decide +kernel
theorem col6 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 6) 6 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col6_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col6_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s6_2_0
    · exact s6_2_1
    · exact s6_2_2
    · exact s6_2_3
    · exact s6_2_4
    · exact s6_2_5
    · exact s6_2_6
    · exact s6_2_7
  · fin_cases v
    · exact s6_3_0
    · exact s6_3_1
    · exact s6_3_2
    · exact s6_3_3
    · exact s6_3_4
    · exact s6_3_5
    · exact s6_3_6
    · exact s6_3_7
  · fin_cases v
    · exact s6_4_0
    · exact s6_4_1
    · exact s6_4_2
    · exact s6_4_3
    · exact s6_4_4
    · exact s6_4_5
    · exact s6_4_6
    · exact s6_4_7
  · fin_cases v
    · exact s6_5_0
    · exact s6_5_1
    · exact s6_5_2
    · exact s6_5_3
    · exact s6_5_4
    · exact s6_5_5
    · exact s6_5_6
    · exact s6_5_7
  · exact List.all_eq_true.mp col6_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col6_7 v (List.mem_finRange v)
theorem col7_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 0 v) = true := by decide +kernel
theorem col7_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 1 v) = true := by decide +kernel
theorem s7_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 0 = true := by decide +kernel
theorem s7_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 1 = true := by decide +kernel
theorem s7_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 2 = true := by decide +kernel
theorem s7_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 3 = true := by decide +kernel
theorem k7_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 2 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k7_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 2 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k7_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 2 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s7_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 2 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k7_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 2 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k7_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 2 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k7_2_4_80 k h.1 (by omega)
theorem s7_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 5 = true := by decide +kernel
theorem s7_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 6 = true := by decide +kernel
theorem s7_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 2 7 = true := by decide +kernel
theorem s7_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 0 = true := by decide +kernel
theorem s7_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 1 = true := by decide +kernel
theorem s7_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 2 = true := by decide +kernel
theorem s7_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 3 = true := by decide +kernel
theorem k7_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 3 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k7_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 3 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k7_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 3 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s7_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 3 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k7_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 3 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k7_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 3 4).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k7_3_4_80 k h.1 (by omega)
theorem s7_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 5 = true := by decide +kernel
theorem s7_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 6 = true := by decide +kernel
theorem s7_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 3 7 = true := by decide +kernel
theorem s7_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 0 = true := by decide +kernel
theorem s7_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 1 = true := by decide +kernel
theorem s7_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 2 = true := by decide +kernel
theorem s7_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 3 = true := by decide +kernel
theorem s7_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 4 = true := by decide +kernel
theorem k7_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k7_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k7_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k7_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k7_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k7_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k7_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k7_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k7_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s7_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k7_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k7_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k7_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k7_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k7_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k7_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k7_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k7_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 5).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k7_4_5_40 k h.1 (by omega)
theorem k7_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k7_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k7_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k7_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k7_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k7_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k7_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k7_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k7_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k7_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k7_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s7_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k7_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k7_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k7_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k7_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k7_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k7_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k7_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k7_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k7_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k7_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 4 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k7_4_6_50 k h.1 (by omega)
theorem s7_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 4 7 = true := by decide +kernel
theorem s7_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 0 = true := by decide +kernel
theorem s7_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 1 = true := by decide +kernel
theorem s7_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 2 = true := by decide +kernel
theorem s7_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 3 = true := by decide +kernel
theorem s7_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 4 = true := by decide +kernel
theorem s7_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 5 = true := by decide +kernel
theorem k7_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k7_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k7_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k7_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k7_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k7_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s7_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k7_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k7_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k7_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k7_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k7_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 7) ((InDA2.TCasaD 2 5 6).getD (7 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k7_5_6_50 k h.1 (by omega)
theorem s7_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 5 7 = true := by decide +kernel
theorem col7_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 6 v) = true := by decide +kernel
theorem col7_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 7 v) = true := by decide +kernel
theorem col7 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 7) 7 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col7_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col7_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s7_2_0
    · exact s7_2_1
    · exact s7_2_2
    · exact s7_2_3
    · exact s7_2_4
    · exact s7_2_5
    · exact s7_2_6
    · exact s7_2_7
  · fin_cases v
    · exact s7_3_0
    · exact s7_3_1
    · exact s7_3_2
    · exact s7_3_3
    · exact s7_3_4
    · exact s7_3_5
    · exact s7_3_6
    · exact s7_3_7
  · fin_cases v
    · exact s7_4_0
    · exact s7_4_1
    · exact s7_4_2
    · exact s7_4_3
    · exact s7_4_4
    · exact s7_4_5
    · exact s7_4_6
    · exact s7_4_7
  · fin_cases v
    · exact s7_5_0
    · exact s7_5_1
    · exact s7_5_2
    · exact s7_5_3
    · exact s7_5_4
    · exact s7_5_5
    · exact s7_5_6
    · exact s7_5_7
  · exact List.all_eq_true.mp col7_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col7_7 v (List.mem_finRange v)
theorem col8_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 0 v) = true := by decide +kernel
theorem col8_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 1 v) = true := by decide +kernel
theorem s8_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 0 = true := by decide +kernel
theorem s8_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 1 = true := by decide +kernel
theorem s8_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 2 = true := by decide +kernel
theorem s8_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 3 = true := by decide +kernel
theorem k8_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 2 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k8_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 2 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k8_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 2 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s8_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 2 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k8_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 2 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k8_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 2 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k8_2_4_80 k h.1 (by omega)
theorem s8_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 5 = true := by decide +kernel
theorem s8_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 6 = true := by decide +kernel
theorem s8_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 2 7 = true := by decide +kernel
theorem s8_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 0 = true := by decide +kernel
theorem s8_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 1 = true := by decide +kernel
theorem s8_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 2 = true := by decide +kernel
theorem s8_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 3 = true := by decide +kernel
theorem k8_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 3 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k8_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 3 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k8_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 3 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s8_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 3 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k8_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 3 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k8_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 3 4).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k8_3_4_80 k h.1 (by omega)
theorem s8_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 5 = true := by decide +kernel
theorem s8_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 6 = true := by decide +kernel
theorem s8_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 3 7 = true := by decide +kernel
theorem s8_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 0 = true := by decide +kernel
theorem s8_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 1 = true := by decide +kernel
theorem s8_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 2 = true := by decide +kernel
theorem s8_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 3 = true := by decide +kernel
theorem s8_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 4 = true := by decide +kernel
theorem k8_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k8_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k8_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k8_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k8_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k8_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k8_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k8_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k8_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s8_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k8_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k8_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k8_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k8_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k8_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k8_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k8_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k8_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 5).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k8_4_5_40 k h.1 (by omega)
theorem k8_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k8_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k8_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k8_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k8_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k8_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k8_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k8_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k8_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k8_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k8_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s8_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k8_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k8_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k8_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k8_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k8_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k8_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k8_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k8_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k8_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k8_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 4 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k8_4_6_50 k h.1 (by omega)
theorem s8_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 4 7 = true := by decide +kernel
theorem s8_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 0 = true := by decide +kernel
theorem s8_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 1 = true := by decide +kernel
theorem s8_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 2 = true := by decide +kernel
theorem s8_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 3 = true := by decide +kernel
theorem s8_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 4 = true := by decide +kernel
theorem s8_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 5 = true := by decide +kernel
theorem k8_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k8_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k8_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k8_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k8_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k8_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s8_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k8_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k8_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k8_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k8_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k8_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 8) ((InDA2.TCasaD 2 5 6).getD (8 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k8_5_6_50 k h.1 (by omega)
theorem s8_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 5 7 = true := by decide +kernel
theorem col8_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 6 v) = true := by decide +kernel
theorem col8_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 7 v) = true := by decide +kernel
theorem col8 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 8) 8 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col8_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col8_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s8_2_0
    · exact s8_2_1
    · exact s8_2_2
    · exact s8_2_3
    · exact s8_2_4
    · exact s8_2_5
    · exact s8_2_6
    · exact s8_2_7
  · fin_cases v
    · exact s8_3_0
    · exact s8_3_1
    · exact s8_3_2
    · exact s8_3_3
    · exact s8_3_4
    · exact s8_3_5
    · exact s8_3_6
    · exact s8_3_7
  · fin_cases v
    · exact s8_4_0
    · exact s8_4_1
    · exact s8_4_2
    · exact s8_4_3
    · exact s8_4_4
    · exact s8_4_5
    · exact s8_4_6
    · exact s8_4_7
  · fin_cases v
    · exact s8_5_0
    · exact s8_5_1
    · exact s8_5_2
    · exact s8_5_3
    · exact s8_5_4
    · exact s8_5_5
    · exact s8_5_6
    · exact s8_5_7
  · exact List.all_eq_true.mp col8_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col8_7 v (List.mem_finRange v)
theorem col9_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 0 v) = true := by decide +kernel
theorem col9_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 1 v) = true := by decide +kernel
theorem s9_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 0 = true := by decide +kernel
theorem s9_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 1 = true := by decide +kernel
theorem s9_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 2 = true := by decide +kernel
theorem s9_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 3 = true := by decide +kernel
theorem k9_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 2 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k9_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 2 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k9_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 2 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s9_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 2 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k9_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 2 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k9_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 2 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k9_2_4_80 k h.1 (by omega)
theorem s9_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 5 = true := by decide +kernel
theorem s9_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 6 = true := by decide +kernel
theorem s9_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 2 7 = true := by decide +kernel
theorem s9_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 0 = true := by decide +kernel
theorem s9_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 1 = true := by decide +kernel
theorem s9_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 2 = true := by decide +kernel
theorem s9_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 3 = true := by decide +kernel
theorem k9_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 3 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k9_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 3 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k9_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 3 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s9_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 3 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k9_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 3 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k9_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 3 4).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k9_3_4_80 k h.1 (by omega)
theorem s9_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 5 = true := by decide +kernel
theorem s9_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 6 = true := by decide +kernel
theorem s9_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 3 7 = true := by decide +kernel
theorem s9_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 0 = true := by decide +kernel
theorem s9_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 1 = true := by decide +kernel
theorem s9_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 2 = true := by decide +kernel
theorem s9_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 3 = true := by decide +kernel
theorem s9_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 4 = true := by decide +kernel
theorem k9_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k9_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k9_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k9_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k9_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k9_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k9_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k9_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k9_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s9_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k9_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k9_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k9_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k9_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k9_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k9_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k9_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k9_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 5).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k9_4_5_40 k h.1 (by omega)
theorem k9_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k9_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k9_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k9_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k9_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k9_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k9_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k9_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k9_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k9_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k9_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s9_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k9_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k9_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k9_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k9_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k9_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k9_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k9_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k9_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k9_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k9_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 4 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k9_4_6_50 k h.1 (by omega)
theorem s9_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 4 7 = true := by decide +kernel
theorem s9_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 0 = true := by decide +kernel
theorem s9_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 1 = true := by decide +kernel
theorem s9_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 2 = true := by decide +kernel
theorem s9_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 3 = true := by decide +kernel
theorem s9_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 4 = true := by decide +kernel
theorem s9_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 5 = true := by decide +kernel
theorem k9_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k9_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k9_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k9_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k9_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k9_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s9_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k9_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k9_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k9_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k9_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k9_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 9) ((InDA2.TCasaD 2 5 6).getD (9 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k9_5_6_50 k h.1 (by omega)
theorem s9_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 5 7 = true := by decide +kernel
theorem col9_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 6 v) = true := by decide +kernel
theorem col9_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 7 v) = true := by decide +kernel
theorem col9 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 9) 9 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col9_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col9_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s9_2_0
    · exact s9_2_1
    · exact s9_2_2
    · exact s9_2_3
    · exact s9_2_4
    · exact s9_2_5
    · exact s9_2_6
    · exact s9_2_7
  · fin_cases v
    · exact s9_3_0
    · exact s9_3_1
    · exact s9_3_2
    · exact s9_3_3
    · exact s9_3_4
    · exact s9_3_5
    · exact s9_3_6
    · exact s9_3_7
  · fin_cases v
    · exact s9_4_0
    · exact s9_4_1
    · exact s9_4_2
    · exact s9_4_3
    · exact s9_4_4
    · exact s9_4_5
    · exact s9_4_6
    · exact s9_4_7
  · fin_cases v
    · exact s9_5_0
    · exact s9_5_1
    · exact s9_5_2
    · exact s9_5_3
    · exact s9_5_4
    · exact s9_5_5
    · exact s9_5_6
    · exact s9_5_7
  · exact List.all_eq_true.mp col9_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col9_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
