module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [10, 15). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col10_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 0 v) = true := by decide +kernel
theorem col10_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 1 v) = true := by decide +kernel
theorem s10_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 0 = true := by decide +kernel
theorem s10_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 1 = true := by decide +kernel
theorem s10_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 2 = true := by decide +kernel
theorem s10_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 3 = true := by decide +kernel
theorem k10_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 2 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k10_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 2 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k10_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 2 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s10_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 2 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k10_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 2 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k10_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 2 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k10_2_4_80 k h.1 (by omega)
theorem s10_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 5 = true := by decide +kernel
theorem s10_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 6 = true := by decide +kernel
theorem s10_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 2 7 = true := by decide +kernel
theorem s10_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 0 = true := by decide +kernel
theorem s10_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 1 = true := by decide +kernel
theorem s10_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 2 = true := by decide +kernel
theorem s10_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 3 = true := by decide +kernel
theorem k10_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 3 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k10_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 3 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k10_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 3 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s10_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 3 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k10_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 3 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k10_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 3 4).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k10_3_4_80 k h.1 (by omega)
theorem s10_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 5 = true := by decide +kernel
theorem s10_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 6 = true := by decide +kernel
theorem s10_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 3 7 = true := by decide +kernel
theorem s10_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 0 = true := by decide +kernel
theorem s10_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 1 = true := by decide +kernel
theorem s10_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 2 = true := by decide +kernel
theorem s10_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 3 = true := by decide +kernel
theorem s10_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 4 = true := by decide +kernel
theorem k10_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k10_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k10_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k10_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k10_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k10_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k10_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k10_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k10_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s10_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k10_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k10_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k10_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k10_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k10_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k10_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k10_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k10_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 5).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k10_4_5_40 k h.1 (by omega)
theorem k10_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k10_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k10_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k10_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k10_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k10_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k10_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k10_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k10_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k10_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k10_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s10_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k10_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k10_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k10_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k10_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k10_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k10_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k10_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k10_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k10_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k10_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 4 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k10_4_6_50 k h.1 (by omega)
theorem s10_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 4 7 = true := by decide +kernel
theorem s10_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 0 = true := by decide +kernel
theorem s10_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 1 = true := by decide +kernel
theorem s10_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 2 = true := by decide +kernel
theorem s10_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 3 = true := by decide +kernel
theorem s10_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 4 = true := by decide +kernel
theorem s10_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 5 = true := by decide +kernel
theorem k10_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k10_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k10_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k10_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k10_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k10_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s10_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k10_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k10_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k10_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k10_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k10_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 10) ((InDA2.TCasaD 2 5 6).getD (10 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k10_5_6_50 k h.1 (by omega)
theorem s10_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 5 7 = true := by decide +kernel
theorem col10_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 6 v) = true := by decide +kernel
theorem col10_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 7 v) = true := by decide +kernel
theorem col10 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 10) 10 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col10_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col10_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s10_2_0
    · exact s10_2_1
    · exact s10_2_2
    · exact s10_2_3
    · exact s10_2_4
    · exact s10_2_5
    · exact s10_2_6
    · exact s10_2_7
  · fin_cases v
    · exact s10_3_0
    · exact s10_3_1
    · exact s10_3_2
    · exact s10_3_3
    · exact s10_3_4
    · exact s10_3_5
    · exact s10_3_6
    · exact s10_3_7
  · fin_cases v
    · exact s10_4_0
    · exact s10_4_1
    · exact s10_4_2
    · exact s10_4_3
    · exact s10_4_4
    · exact s10_4_5
    · exact s10_4_6
    · exact s10_4_7
  · fin_cases v
    · exact s10_5_0
    · exact s10_5_1
    · exact s10_5_2
    · exact s10_5_3
    · exact s10_5_4
    · exact s10_5_5
    · exact s10_5_6
    · exact s10_5_7
  · exact List.all_eq_true.mp col10_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col10_7 v (List.mem_finRange v)
theorem col11_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 0 v) = true := by decide +kernel
theorem col11_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 1 v) = true := by decide +kernel
theorem s11_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 0 = true := by decide +kernel
theorem s11_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 1 = true := by decide +kernel
theorem s11_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 2 = true := by decide +kernel
theorem s11_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 3 = true := by decide +kernel
theorem k11_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 2 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k11_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 2 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k11_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 2 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s11_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 2 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k11_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 2 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k11_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 2 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k11_2_4_80 k h.1 (by omega)
theorem s11_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 5 = true := by decide +kernel
theorem s11_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 6 = true := by decide +kernel
theorem s11_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 2 7 = true := by decide +kernel
theorem s11_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 0 = true := by decide +kernel
theorem s11_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 1 = true := by decide +kernel
theorem s11_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 2 = true := by decide +kernel
theorem s11_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 3 = true := by decide +kernel
theorem k11_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 3 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k11_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 3 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k11_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 3 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s11_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 3 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k11_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 3 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k11_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 3 4).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k11_3_4_80 k h.1 (by omega)
theorem s11_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 5 = true := by decide +kernel
theorem s11_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 6 = true := by decide +kernel
theorem s11_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 3 7 = true := by decide +kernel
theorem s11_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 0 = true := by decide +kernel
theorem s11_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 1 = true := by decide +kernel
theorem s11_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 2 = true := by decide +kernel
theorem s11_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 3 = true := by decide +kernel
theorem s11_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 4 = true := by decide +kernel
theorem k11_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k11_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k11_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k11_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k11_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k11_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k11_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k11_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k11_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s11_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k11_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k11_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k11_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k11_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k11_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k11_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k11_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k11_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 5).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k11_4_5_40 k h.1 (by omega)
theorem k11_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k11_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k11_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k11_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k11_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k11_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k11_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k11_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k11_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k11_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k11_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s11_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k11_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k11_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k11_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k11_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k11_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k11_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k11_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k11_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k11_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k11_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 4 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k11_4_6_50 k h.1 (by omega)
theorem s11_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 4 7 = true := by decide +kernel
theorem s11_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 0 = true := by decide +kernel
theorem s11_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 1 = true := by decide +kernel
theorem s11_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 2 = true := by decide +kernel
theorem s11_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 3 = true := by decide +kernel
theorem s11_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 4 = true := by decide +kernel
theorem s11_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 5 = true := by decide +kernel
theorem k11_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k11_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k11_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k11_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k11_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k11_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s11_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k11_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k11_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k11_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k11_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k11_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 11) ((InDA2.TCasaD 2 5 6).getD (11 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k11_5_6_50 k h.1 (by omega)
theorem s11_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 5 7 = true := by decide +kernel
theorem col11_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 6 v) = true := by decide +kernel
theorem col11_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 7 v) = true := by decide +kernel
theorem col11 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 11) 11 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col11_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col11_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s11_2_0
    · exact s11_2_1
    · exact s11_2_2
    · exact s11_2_3
    · exact s11_2_4
    · exact s11_2_5
    · exact s11_2_6
    · exact s11_2_7
  · fin_cases v
    · exact s11_3_0
    · exact s11_3_1
    · exact s11_3_2
    · exact s11_3_3
    · exact s11_3_4
    · exact s11_3_5
    · exact s11_3_6
    · exact s11_3_7
  · fin_cases v
    · exact s11_4_0
    · exact s11_4_1
    · exact s11_4_2
    · exact s11_4_3
    · exact s11_4_4
    · exact s11_4_5
    · exact s11_4_6
    · exact s11_4_7
  · fin_cases v
    · exact s11_5_0
    · exact s11_5_1
    · exact s11_5_2
    · exact s11_5_3
    · exact s11_5_4
    · exact s11_5_5
    · exact s11_5_6
    · exact s11_5_7
  · exact List.all_eq_true.mp col11_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col11_7 v (List.mem_finRange v)
theorem col12_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 0 v) = true := by decide +kernel
theorem col12_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 1 v) = true := by decide +kernel
theorem s12_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 0 = true := by decide +kernel
theorem s12_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 1 = true := by decide +kernel
theorem s12_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 2 = true := by decide +kernel
theorem s12_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 3 = true := by decide +kernel
theorem k12_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 2 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k12_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 2 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k12_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 2 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s12_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 2 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k12_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 2 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k12_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 2 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k12_2_4_80 k h.1 (by omega)
theorem s12_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 5 = true := by decide +kernel
theorem s12_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 6 = true := by decide +kernel
theorem s12_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 2 7 = true := by decide +kernel
theorem s12_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 0 = true := by decide +kernel
theorem s12_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 1 = true := by decide +kernel
theorem s12_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 2 = true := by decide +kernel
theorem s12_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 3 = true := by decide +kernel
theorem k12_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 3 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k12_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 3 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k12_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 3 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s12_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 3 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k12_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 3 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k12_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 3 4).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k12_3_4_80 k h.1 (by omega)
theorem s12_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 5 = true := by decide +kernel
theorem s12_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 6 = true := by decide +kernel
theorem s12_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 3 7 = true := by decide +kernel
theorem s12_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 0 = true := by decide +kernel
theorem s12_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 1 = true := by decide +kernel
theorem s12_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 2 = true := by decide +kernel
theorem s12_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 3 = true := by decide +kernel
theorem s12_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 4 = true := by decide +kernel
theorem k12_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k12_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k12_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k12_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k12_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k12_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k12_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k12_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k12_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s12_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k12_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k12_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k12_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k12_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k12_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k12_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k12_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k12_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 5).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k12_4_5_40 k h.1 (by omega)
theorem k12_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k12_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k12_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k12_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k12_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k12_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k12_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k12_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k12_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k12_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k12_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s12_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k12_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k12_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k12_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k12_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k12_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k12_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k12_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k12_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k12_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k12_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 4 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k12_4_6_50 k h.1 (by omega)
theorem s12_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 4 7 = true := by decide +kernel
theorem s12_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 0 = true := by decide +kernel
theorem s12_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 1 = true := by decide +kernel
theorem s12_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 2 = true := by decide +kernel
theorem s12_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 3 = true := by decide +kernel
theorem s12_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 4 = true := by decide +kernel
theorem s12_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 5 = true := by decide +kernel
theorem k12_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k12_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k12_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k12_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k12_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k12_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s12_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k12_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k12_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k12_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k12_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k12_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 12) ((InDA2.TCasaD 2 5 6).getD (12 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k12_5_6_50 k h.1 (by omega)
theorem s12_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 5 7 = true := by decide +kernel
theorem col12_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 6 v) = true := by decide +kernel
theorem col12_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 7 v) = true := by decide +kernel
theorem col12 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 12) 12 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col12_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col12_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s12_2_0
    · exact s12_2_1
    · exact s12_2_2
    · exact s12_2_3
    · exact s12_2_4
    · exact s12_2_5
    · exact s12_2_6
    · exact s12_2_7
  · fin_cases v
    · exact s12_3_0
    · exact s12_3_1
    · exact s12_3_2
    · exact s12_3_3
    · exact s12_3_4
    · exact s12_3_5
    · exact s12_3_6
    · exact s12_3_7
  · fin_cases v
    · exact s12_4_0
    · exact s12_4_1
    · exact s12_4_2
    · exact s12_4_3
    · exact s12_4_4
    · exact s12_4_5
    · exact s12_4_6
    · exact s12_4_7
  · fin_cases v
    · exact s12_5_0
    · exact s12_5_1
    · exact s12_5_2
    · exact s12_5_3
    · exact s12_5_4
    · exact s12_5_5
    · exact s12_5_6
    · exact s12_5_7
  · exact List.all_eq_true.mp col12_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col12_7 v (List.mem_finRange v)
theorem col13_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 0 v) = true := by decide +kernel
theorem col13_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 1 v) = true := by decide +kernel
theorem s13_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 0 = true := by decide +kernel
theorem s13_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 1 = true := by decide +kernel
theorem s13_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 2 = true := by decide +kernel
theorem s13_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 3 = true := by decide +kernel
theorem k13_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 2 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k13_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 2 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k13_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 2 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s13_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 2 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k13_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 2 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k13_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 2 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k13_2_4_80 k h.1 (by omega)
theorem s13_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 5 = true := by decide +kernel
theorem s13_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 6 = true := by decide +kernel
theorem s13_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 2 7 = true := by decide +kernel
theorem s13_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 0 = true := by decide +kernel
theorem s13_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 1 = true := by decide +kernel
theorem s13_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 2 = true := by decide +kernel
theorem s13_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 3 = true := by decide +kernel
theorem k13_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 3 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k13_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 3 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k13_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 3 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s13_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 3 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k13_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 3 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k13_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 3 4).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k13_3_4_80 k h.1 (by omega)
theorem s13_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 5 = true := by decide +kernel
theorem s13_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 6 = true := by decide +kernel
theorem s13_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 3 7 = true := by decide +kernel
theorem s13_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 0 = true := by decide +kernel
theorem s13_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 1 = true := by decide +kernel
theorem s13_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 2 = true := by decide +kernel
theorem s13_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 3 = true := by decide +kernel
theorem s13_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 4 = true := by decide +kernel
theorem k13_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k13_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k13_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k13_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k13_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k13_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k13_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k13_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k13_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s13_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k13_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k13_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k13_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k13_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k13_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k13_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k13_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k13_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 5).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k13_4_5_40 k h.1 (by omega)
theorem k13_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k13_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k13_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k13_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k13_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k13_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k13_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k13_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k13_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k13_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k13_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s13_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k13_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k13_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k13_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k13_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k13_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k13_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k13_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k13_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k13_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k13_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 4 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k13_4_6_50 k h.1 (by omega)
theorem s13_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 4 7 = true := by decide +kernel
theorem s13_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 0 = true := by decide +kernel
theorem s13_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 1 = true := by decide +kernel
theorem s13_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 2 = true := by decide +kernel
theorem s13_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 3 = true := by decide +kernel
theorem s13_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 4 = true := by decide +kernel
theorem s13_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 5 = true := by decide +kernel
theorem k13_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k13_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k13_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k13_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k13_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k13_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s13_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k13_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k13_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k13_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k13_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k13_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 13) ((InDA2.TCasaD 2 5 6).getD (13 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k13_5_6_50 k h.1 (by omega)
theorem s13_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 5 7 = true := by decide +kernel
theorem col13_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 6 v) = true := by decide +kernel
theorem col13_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 7 v) = true := by decide +kernel
theorem col13 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 13) 13 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col13_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col13_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s13_2_0
    · exact s13_2_1
    · exact s13_2_2
    · exact s13_2_3
    · exact s13_2_4
    · exact s13_2_5
    · exact s13_2_6
    · exact s13_2_7
  · fin_cases v
    · exact s13_3_0
    · exact s13_3_1
    · exact s13_3_2
    · exact s13_3_3
    · exact s13_3_4
    · exact s13_3_5
    · exact s13_3_6
    · exact s13_3_7
  · fin_cases v
    · exact s13_4_0
    · exact s13_4_1
    · exact s13_4_2
    · exact s13_4_3
    · exact s13_4_4
    · exact s13_4_5
    · exact s13_4_6
    · exact s13_4_7
  · fin_cases v
    · exact s13_5_0
    · exact s13_5_1
    · exact s13_5_2
    · exact s13_5_3
    · exact s13_5_4
    · exact s13_5_5
    · exact s13_5_6
    · exact s13_5_7
  · exact List.all_eq_true.mp col13_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col13_7 v (List.mem_finRange v)
theorem col14_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 0 v) = true := by decide +kernel
theorem col14_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 1 v) = true := by decide +kernel
theorem s14_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 0 = true := by decide +kernel
theorem s14_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 1 = true := by decide +kernel
theorem s14_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 2 = true := by decide +kernel
theorem s14_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 3 = true := by decide +kernel
theorem k14_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 2 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k14_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 2 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k14_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 2 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s14_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 2 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k14_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 2 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k14_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 2 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k14_2_4_80 k h.1 (by omega)
theorem s14_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 5 = true := by decide +kernel
theorem s14_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 6 = true := by decide +kernel
theorem s14_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 2 7 = true := by decide +kernel
theorem s14_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 0 = true := by decide +kernel
theorem s14_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 1 = true := by decide +kernel
theorem s14_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 2 = true := by decide +kernel
theorem s14_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 3 = true := by decide +kernel
theorem k14_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 3 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k14_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 3 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k14_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 3 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s14_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 3 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k14_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 3 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k14_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 3 4).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k14_3_4_80 k h.1 (by omega)
theorem s14_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 5 = true := by decide +kernel
theorem s14_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 6 = true := by decide +kernel
theorem s14_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 3 7 = true := by decide +kernel
theorem s14_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 0 = true := by decide +kernel
theorem s14_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 1 = true := by decide +kernel
theorem s14_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 2 = true := by decide +kernel
theorem s14_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 3 = true := by decide +kernel
theorem s14_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 4 = true := by decide +kernel
theorem k14_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k14_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k14_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k14_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k14_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k14_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k14_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k14_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k14_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s14_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k14_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k14_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k14_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k14_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k14_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k14_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k14_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k14_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 5).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k14_4_5_40 k h.1 (by omega)
theorem k14_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k14_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k14_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k14_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k14_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k14_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k14_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k14_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k14_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k14_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k14_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s14_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k14_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k14_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k14_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k14_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k14_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k14_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k14_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k14_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k14_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k14_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 4 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k14_4_6_50 k h.1 (by omega)
theorem s14_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 4 7 = true := by decide +kernel
theorem s14_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 0 = true := by decide +kernel
theorem s14_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 1 = true := by decide +kernel
theorem s14_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 2 = true := by decide +kernel
theorem s14_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 3 = true := by decide +kernel
theorem s14_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 4 = true := by decide +kernel
theorem s14_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 5 = true := by decide +kernel
theorem k14_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k14_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k14_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k14_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k14_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k14_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s14_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k14_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k14_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k14_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k14_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k14_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 14) ((InDA2.TCasaD 2 5 6).getD (14 - x2AOff 2 2) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k14_5_6_50 k h.1 (by omega)
theorem s14_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 5 7 = true := by decide +kernel
theorem col14_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 6 v) = true := by decide +kernel
theorem col14_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 7 v) = true := by decide +kernel
theorem col14 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 14) 14 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col14_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col14_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s14_2_0
    · exact s14_2_1
    · exact s14_2_2
    · exact s14_2_3
    · exact s14_2_4
    · exact s14_2_5
    · exact s14_2_6
    · exact s14_2_7
  · fin_cases v
    · exact s14_3_0
    · exact s14_3_1
    · exact s14_3_2
    · exact s14_3_3
    · exact s14_3_4
    · exact s14_3_5
    · exact s14_3_6
    · exact s14_3_7
  · fin_cases v
    · exact s14_4_0
    · exact s14_4_1
    · exact s14_4_2
    · exact s14_4_3
    · exact s14_4_4
    · exact s14_4_5
    · exact s14_4_6
    · exact s14_4_7
  · fin_cases v
    · exact s14_5_0
    · exact s14_5_1
    · exact s14_5_2
    · exact s14_5_3
    · exact s14_5_4
    · exact s14_5_5
    · exact s14_5_6
    · exact s14_5_7
  · exact List.all_eq_true.mp col14_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col14_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
