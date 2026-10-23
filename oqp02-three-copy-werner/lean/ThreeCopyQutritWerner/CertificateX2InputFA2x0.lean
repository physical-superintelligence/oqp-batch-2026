module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [0, 5). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col0_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 0 v) = true := by decide +kernel
theorem col0_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 1 v) = true := by decide +kernel
theorem s0_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 0 = true := by decide +kernel
theorem s0_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 1 = true := by decide +kernel
theorem s0_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 2 = true := by decide +kernel
theorem s0_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 3 = true := by decide +kernel
theorem k0_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 2 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k0_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 2 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k0_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 2 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s0_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 2 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k0_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 2 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k0_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 2 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k0_2_4_80 k h.1 (by omega)
theorem s0_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 5 = true := by decide +kernel
theorem s0_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 6 = true := by decide +kernel
theorem s0_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 2 7 = true := by decide +kernel
theorem s0_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 0 = true := by decide +kernel
theorem s0_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 1 = true := by decide +kernel
theorem s0_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 2 = true := by decide +kernel
theorem s0_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 3 = true := by decide +kernel
theorem k0_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 3 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k0_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 3 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k0_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 3 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s0_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 3 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k0_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 3 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k0_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 3 4).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k0_3_4_80 k h.1 (by omega)
theorem s0_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 5 = true := by decide +kernel
theorem s0_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 6 = true := by decide +kernel
theorem s0_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 3 7 = true := by decide +kernel
theorem s0_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 0 = true := by decide +kernel
theorem s0_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 1 = true := by decide +kernel
theorem s0_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 2 = true := by decide +kernel
theorem s0_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 3 = true := by decide +kernel
theorem s0_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 4 = true := by decide +kernel
theorem k0_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k0_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k0_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k0_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k0_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k0_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k0_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k0_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k0_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s0_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k0_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k0_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k0_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k0_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k0_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k0_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k0_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k0_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 5).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k0_4_5_40 k h.1 (by omega)
theorem k0_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k0_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k0_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k0_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k0_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k0_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k0_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k0_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k0_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k0_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k0_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s0_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k0_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k0_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k0_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k0_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k0_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k0_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k0_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k0_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k0_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k0_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 4 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k0_4_6_50 k h.1 (by omega)
theorem s0_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 4 7 = true := by decide +kernel
theorem s0_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 0 = true := by decide +kernel
theorem s0_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 1 = true := by decide +kernel
theorem s0_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 2 = true := by decide +kernel
theorem s0_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 3 = true := by decide +kernel
theorem s0_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 4 = true := by decide +kernel
theorem s0_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 5 = true := by decide +kernel
theorem k0_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k0_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k0_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k0_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k0_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k0_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s0_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k0_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k0_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k0_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k0_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k0_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 0) ((InDA2.TCasaD 1 5 6).getD (0 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k0_5_6_50 k h.1 (by omega)
theorem s0_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 5 7 = true := by decide +kernel
theorem col0_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 6 v) = true := by decide +kernel
theorem col0_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 7 v) = true := by decide +kernel
theorem col0 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 0) 0 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col0_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col0_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s0_2_0
    · exact s0_2_1
    · exact s0_2_2
    · exact s0_2_3
    · exact s0_2_4
    · exact s0_2_5
    · exact s0_2_6
    · exact s0_2_7
  · fin_cases v
    · exact s0_3_0
    · exact s0_3_1
    · exact s0_3_2
    · exact s0_3_3
    · exact s0_3_4
    · exact s0_3_5
    · exact s0_3_6
    · exact s0_3_7
  · fin_cases v
    · exact s0_4_0
    · exact s0_4_1
    · exact s0_4_2
    · exact s0_4_3
    · exact s0_4_4
    · exact s0_4_5
    · exact s0_4_6
    · exact s0_4_7
  · fin_cases v
    · exact s0_5_0
    · exact s0_5_1
    · exact s0_5_2
    · exact s0_5_3
    · exact s0_5_4
    · exact s0_5_5
    · exact s0_5_6
    · exact s0_5_7
  · exact List.all_eq_true.mp col0_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col0_7 v (List.mem_finRange v)
theorem col1_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 0 v) = true := by decide +kernel
theorem col1_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 1 v) = true := by decide +kernel
theorem s1_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 0 = true := by decide +kernel
theorem s1_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 1 = true := by decide +kernel
theorem s1_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 2 = true := by decide +kernel
theorem s1_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 3 = true := by decide +kernel
theorem k1_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 2 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k1_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 2 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k1_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 2 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s1_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 2 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k1_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 2 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k1_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 2 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k1_2_4_80 k h.1 (by omega)
theorem s1_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 5 = true := by decide +kernel
theorem s1_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 6 = true := by decide +kernel
theorem s1_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 2 7 = true := by decide +kernel
theorem s1_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 0 = true := by decide +kernel
theorem s1_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 1 = true := by decide +kernel
theorem s1_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 2 = true := by decide +kernel
theorem s1_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 3 = true := by decide +kernel
theorem k1_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 3 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k1_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 3 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k1_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 3 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s1_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 3 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k1_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 3 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k1_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 3 4).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k1_3_4_80 k h.1 (by omega)
theorem s1_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 5 = true := by decide +kernel
theorem s1_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 6 = true := by decide +kernel
theorem s1_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 3 7 = true := by decide +kernel
theorem s1_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 0 = true := by decide +kernel
theorem s1_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 1 = true := by decide +kernel
theorem s1_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 2 = true := by decide +kernel
theorem s1_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 3 = true := by decide +kernel
theorem s1_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 4 = true := by decide +kernel
theorem k1_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k1_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k1_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k1_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k1_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k1_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k1_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k1_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k1_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s1_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k1_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k1_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k1_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k1_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k1_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k1_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k1_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k1_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 5).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k1_4_5_40 k h.1 (by omega)
theorem k1_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k1_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k1_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k1_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k1_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k1_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k1_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k1_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k1_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k1_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k1_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s1_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k1_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k1_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k1_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k1_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k1_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k1_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k1_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k1_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k1_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k1_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 4 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k1_4_6_50 k h.1 (by omega)
theorem s1_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 4 7 = true := by decide +kernel
theorem s1_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 0 = true := by decide +kernel
theorem s1_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 1 = true := by decide +kernel
theorem s1_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 2 = true := by decide +kernel
theorem s1_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 3 = true := by decide +kernel
theorem s1_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 4 = true := by decide +kernel
theorem s1_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 5 = true := by decide +kernel
theorem k1_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k1_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k1_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k1_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k1_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k1_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s1_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k1_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k1_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k1_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k1_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k1_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 1) ((InDA2.TCasaD 1 5 6).getD (1 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k1_5_6_50 k h.1 (by omega)
theorem s1_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 5 7 = true := by decide +kernel
theorem col1_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 6 v) = true := by decide +kernel
theorem col1_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 7 v) = true := by decide +kernel
theorem col1 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 1) 1 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col1_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col1_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s1_2_0
    · exact s1_2_1
    · exact s1_2_2
    · exact s1_2_3
    · exact s1_2_4
    · exact s1_2_5
    · exact s1_2_6
    · exact s1_2_7
  · fin_cases v
    · exact s1_3_0
    · exact s1_3_1
    · exact s1_3_2
    · exact s1_3_3
    · exact s1_3_4
    · exact s1_3_5
    · exact s1_3_6
    · exact s1_3_7
  · fin_cases v
    · exact s1_4_0
    · exact s1_4_1
    · exact s1_4_2
    · exact s1_4_3
    · exact s1_4_4
    · exact s1_4_5
    · exact s1_4_6
    · exact s1_4_7
  · fin_cases v
    · exact s1_5_0
    · exact s1_5_1
    · exact s1_5_2
    · exact s1_5_3
    · exact s1_5_4
    · exact s1_5_5
    · exact s1_5_6
    · exact s1_5_7
  · exact List.all_eq_true.mp col1_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col1_7 v (List.mem_finRange v)
theorem col2_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 0 v) = true := by decide +kernel
theorem col2_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 1 v) = true := by decide +kernel
theorem s2_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 0 = true := by decide +kernel
theorem s2_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 1 = true := by decide +kernel
theorem s2_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 2 = true := by decide +kernel
theorem s2_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 3 = true := by decide +kernel
theorem k2_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 2 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k2_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 2 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k2_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 2 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s2_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 2 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k2_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 2 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k2_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 2 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k2_2_4_80 k h.1 (by omega)
theorem s2_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 5 = true := by decide +kernel
theorem s2_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 6 = true := by decide +kernel
theorem s2_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 2 7 = true := by decide +kernel
theorem s2_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 0 = true := by decide +kernel
theorem s2_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 1 = true := by decide +kernel
theorem s2_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 2 = true := by decide +kernel
theorem s2_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 3 = true := by decide +kernel
theorem k2_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 3 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k2_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 3 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k2_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 3 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s2_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 3 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k2_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 3 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k2_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 3 4).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k2_3_4_80 k h.1 (by omega)
theorem s2_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 5 = true := by decide +kernel
theorem s2_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 6 = true := by decide +kernel
theorem s2_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 3 7 = true := by decide +kernel
theorem s2_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 0 = true := by decide +kernel
theorem s2_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 1 = true := by decide +kernel
theorem s2_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 2 = true := by decide +kernel
theorem s2_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 3 = true := by decide +kernel
theorem s2_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 4 = true := by decide +kernel
theorem k2_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k2_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k2_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k2_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k2_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k2_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k2_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k2_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k2_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s2_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k2_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k2_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k2_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k2_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k2_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k2_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k2_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k2_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 5).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k2_4_5_40 k h.1 (by omega)
theorem k2_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k2_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k2_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k2_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k2_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k2_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k2_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k2_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k2_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k2_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k2_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s2_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k2_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k2_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k2_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k2_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k2_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k2_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k2_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k2_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k2_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k2_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 4 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k2_4_6_50 k h.1 (by omega)
theorem s2_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 4 7 = true := by decide +kernel
theorem s2_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 0 = true := by decide +kernel
theorem s2_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 1 = true := by decide +kernel
theorem s2_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 2 = true := by decide +kernel
theorem s2_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 3 = true := by decide +kernel
theorem s2_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 4 = true := by decide +kernel
theorem s2_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 5 = true := by decide +kernel
theorem k2_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k2_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k2_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k2_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k2_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k2_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s2_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k2_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k2_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k2_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k2_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k2_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 2) ((InDA2.TCasaD 1 5 6).getD (2 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k2_5_6_50 k h.1 (by omega)
theorem s2_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 5 7 = true := by decide +kernel
theorem col2_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 6 v) = true := by decide +kernel
theorem col2_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 7 v) = true := by decide +kernel
theorem col2 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 2) 2 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col2_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col2_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s2_2_0
    · exact s2_2_1
    · exact s2_2_2
    · exact s2_2_3
    · exact s2_2_4
    · exact s2_2_5
    · exact s2_2_6
    · exact s2_2_7
  · fin_cases v
    · exact s2_3_0
    · exact s2_3_1
    · exact s2_3_2
    · exact s2_3_3
    · exact s2_3_4
    · exact s2_3_5
    · exact s2_3_6
    · exact s2_3_7
  · fin_cases v
    · exact s2_4_0
    · exact s2_4_1
    · exact s2_4_2
    · exact s2_4_3
    · exact s2_4_4
    · exact s2_4_5
    · exact s2_4_6
    · exact s2_4_7
  · fin_cases v
    · exact s2_5_0
    · exact s2_5_1
    · exact s2_5_2
    · exact s2_5_3
    · exact s2_5_4
    · exact s2_5_5
    · exact s2_5_6
    · exact s2_5_7
  · exact List.all_eq_true.mp col2_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col2_7 v (List.mem_finRange v)
theorem col3_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 0 v) = true := by decide +kernel
theorem col3_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 1 v) = true := by decide +kernel
theorem s3_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 0 = true := by decide +kernel
theorem s3_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 1 = true := by decide +kernel
theorem s3_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 2 = true := by decide +kernel
theorem s3_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 3 = true := by decide +kernel
theorem k3_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 2 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k3_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 2 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k3_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 2 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s3_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 2 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k3_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 2 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k3_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 2 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k3_2_4_80 k h.1 (by omega)
theorem s3_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 5 = true := by decide +kernel
theorem s3_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 6 = true := by decide +kernel
theorem s3_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 2 7 = true := by decide +kernel
theorem s3_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 0 = true := by decide +kernel
theorem s3_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 1 = true := by decide +kernel
theorem s3_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 2 = true := by decide +kernel
theorem s3_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 3 = true := by decide +kernel
theorem k3_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 3 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k3_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 3 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k3_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 3 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s3_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 3 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k3_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 3 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k3_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 3 4).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k3_3_4_80 k h.1 (by omega)
theorem s3_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 5 = true := by decide +kernel
theorem s3_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 6 = true := by decide +kernel
theorem s3_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 3 7 = true := by decide +kernel
theorem s3_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 0 = true := by decide +kernel
theorem s3_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 1 = true := by decide +kernel
theorem s3_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 2 = true := by decide +kernel
theorem s3_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 3 = true := by decide +kernel
theorem s3_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 4 = true := by decide +kernel
theorem k3_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k3_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k3_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k3_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k3_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k3_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k3_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k3_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k3_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s3_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k3_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k3_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k3_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k3_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k3_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k3_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k3_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k3_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 5).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k3_4_5_40 k h.1 (by omega)
theorem k3_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k3_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k3_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k3_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k3_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k3_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k3_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k3_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k3_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k3_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k3_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s3_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k3_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k3_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k3_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k3_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k3_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k3_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k3_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k3_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k3_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k3_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 4 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k3_4_6_50 k h.1 (by omega)
theorem s3_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 4 7 = true := by decide +kernel
theorem s3_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 0 = true := by decide +kernel
theorem s3_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 1 = true := by decide +kernel
theorem s3_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 2 = true := by decide +kernel
theorem s3_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 3 = true := by decide +kernel
theorem s3_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 4 = true := by decide +kernel
theorem s3_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 5 = true := by decide +kernel
theorem k3_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k3_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k3_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k3_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k3_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k3_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s3_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k3_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k3_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k3_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k3_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k3_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 3) ((InDA2.TCasaD 1 5 6).getD (3 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k3_5_6_50 k h.1 (by omega)
theorem s3_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 5 7 = true := by decide +kernel
theorem col3_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 6 v) = true := by decide +kernel
theorem col3_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 7 v) = true := by decide +kernel
theorem col3 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 3) 3 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col3_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col3_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s3_2_0
    · exact s3_2_1
    · exact s3_2_2
    · exact s3_2_3
    · exact s3_2_4
    · exact s3_2_5
    · exact s3_2_6
    · exact s3_2_7
  · fin_cases v
    · exact s3_3_0
    · exact s3_3_1
    · exact s3_3_2
    · exact s3_3_3
    · exact s3_3_4
    · exact s3_3_5
    · exact s3_3_6
    · exact s3_3_7
  · fin_cases v
    · exact s3_4_0
    · exact s3_4_1
    · exact s3_4_2
    · exact s3_4_3
    · exact s3_4_4
    · exact s3_4_5
    · exact s3_4_6
    · exact s3_4_7
  · fin_cases v
    · exact s3_5_0
    · exact s3_5_1
    · exact s3_5_2
    · exact s3_5_3
    · exact s3_5_4
    · exact s3_5_5
    · exact s3_5_6
    · exact s3_5_7
  · exact List.all_eq_true.mp col3_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col3_7 v (List.mem_finRange v)
theorem col4_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 0 v) = true := by decide +kernel
theorem col4_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 1 v) = true := by decide +kernel
theorem s4_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 0 = true := by decide +kernel
theorem s4_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 1 = true := by decide +kernel
theorem s4_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 2 = true := by decide +kernel
theorem s4_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 3 = true := by decide +kernel
theorem k4_2_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 2 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k4_2_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 2 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k4_2_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 2 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s4_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 2 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k4_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 2 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k4_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 2 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k4_2_4_80 k h.1 (by omega)
theorem s4_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 5 = true := by decide +kernel
theorem s4_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 6 = true := by decide +kernel
theorem s4_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 2 7 = true := by decide +kernel
theorem s4_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 0 = true := by decide +kernel
theorem s4_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 1 = true := by decide +kernel
theorem s4_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 2 = true := by decide +kernel
theorem s4_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 3 = true := by decide +kernel
theorem k4_3_4_0 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 3 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k4_3_4_40 : (List.range 40).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 3 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k4_3_4_80 : (List.range 25).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 3 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s4_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 4 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 3 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k4_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 3 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k4_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 3 4).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k4_3_4_80 k h.1 (by omega)
theorem s4_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 5 = true := by decide +kernel
theorem s4_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 6 = true := by decide +kernel
theorem s4_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 3 7 = true := by decide +kernel
theorem s4_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 0 = true := by decide +kernel
theorem s4_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 1 = true := by decide +kernel
theorem s4_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 2 = true := by decide +kernel
theorem s4_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 3 = true := by decide +kernel
theorem s4_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 4 = true := by decide +kernel
theorem k4_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k4_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k4_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k4_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k4_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k4_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k4_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k4_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k4_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s4_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k4_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k4_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k4_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k4_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k4_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k4_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k4_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k4_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 5).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k4_4_5_40 k h.1 (by omega)
theorem k4_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k4_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k4_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k4_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k4_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k4_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k4_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k4_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k4_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k4_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k4_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s4_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k4_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k4_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k4_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k4_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k4_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k4_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k4_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k4_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k4_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k4_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 4 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k4_4_6_50 k h.1 (by omega)
theorem s4_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 4 7 = true := by decide +kernel
theorem s4_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 0 = true := by decide +kernel
theorem s4_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 1 = true := by decide +kernel
theorem s4_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 2 = true := by decide +kernel
theorem s4_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 3 = true := by decide +kernel
theorem s4_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 4 = true := by decide +kernel
theorem s4_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 5 = true := by decide +kernel
theorem k4_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k4_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k4_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k4_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k4_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k4_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s4_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k4_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k4_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k4_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k4_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k4_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 4) ((InDA2.TCasaD 1 5 6).getD (4 - x2AOff 2 1) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k4_5_6_50 k h.1 (by omega)
theorem s4_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 5 7 = true := by decide +kernel
theorem col4_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 6 v) = true := by decide +kernel
theorem col4_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 7 v) = true := by decide +kernel
theorem col4 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 4) 4 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col4_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col4_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s4_2_0
    · exact s4_2_1
    · exact s4_2_2
    · exact s4_2_3
    · exact s4_2_4
    · exact s4_2_5
    · exact s4_2_6
    · exact s4_2_7
  · fin_cases v
    · exact s4_3_0
    · exact s4_3_1
    · exact s4_3_2
    · exact s4_3_3
    · exact s4_3_4
    · exact s4_3_5
    · exact s4_3_6
    · exact s4_3_7
  · fin_cases v
    · exact s4_4_0
    · exact s4_4_1
    · exact s4_4_2
    · exact s4_4_3
    · exact s4_4_4
    · exact s4_4_5
    · exact s4_4_6
    · exact s4_4_7
  · fin_cases v
    · exact s4_5_0
    · exact s4_5_1
    · exact s4_5_2
    · exact s4_5_3
    · exact s4_5_4
    · exact s4_5_5
    · exact s4_5_6
    · exact s4_5_7
  · exact List.all_eq_true.mp col4_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col4_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
