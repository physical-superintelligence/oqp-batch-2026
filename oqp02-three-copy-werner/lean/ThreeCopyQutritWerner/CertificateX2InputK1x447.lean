module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x447
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k136 : x2Key 1 := ⟨136, by decide⟩
x2_gj_cols gj258 258 1 4 4 7 256
theorem gjc136_0 : (List.range 28).all (fun d => gjCheck 256 1 4 4 7 7 7 6 (x2JCols 258 (0 + d)) (gj258.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok136 : ∀ d < x2KeySize 1 k136, gjCheck 256 1 (x2KeyTypes 1 k136 0) (x2KeyTypes 1 k136 1) (x2KeyTypes 1 k136 2) (x2KeyMult 1 k136 0) (x2KeyMult 1 k136 1) (x2KeyMult 1 k136 2) (x2JCols (x2KeyGlobal 1 k136) d) (gj258.getD d 0) = true := by
  have hr : x2KeySize 1 k136 = 28 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 7 7 7 6 (x2JCols 258 d) (gj258.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 7 7 7 6 (x2JCols 258 d) (gj258.getD d 0)) 0 28 gjc136_0 d (Nat.zero_le d) (by omega)
x2_v_cols v258 gj258 258 256 294
theorem vc136_0 : (List.range 13).all (fun c => vCheck 256 294 28 gj258 (x2Trial_258.getD (0 + c) 0) (v258.getD (0 + c) 0)) = true := by decide +kernel
theorem vok136 : ∀ c < 13, vCheck 256 (x2KeyMult 1 k136 0 * x2KeyMult 1 k136 1 * x2KeyMult 1 k136 2) (x2KeySize 1 k136) gj258 (x2Trial_258.getD c 0) (v258.getD c 0) = true := by
  intro c hc
  show vCheck 256 294 28 gj258 (x2Trial_258.getD c 0) (v258.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 294 28 gj258 (x2Trial_258.getD c 0) (v258.getD c 0)) 0 13 vc136_0 c (Nat.zero_le c) (by omega)
theorem small136 : x2KeyDegree 1 k136 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k136 0 ∧ 1 ≤ x2KeyMult 1 k136 1 ∧ 1 ≤ x2KeyMult 1 k136 2 ∧ glRowOK 1 (x2KeyTypes 1 k136 0) (x2KeyMult 1 k136 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k136 1) (x2KeyMult 1 k136 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k136 2) (x2KeyMult 1 k136 2) 512 = true ∧ gj258.length = x2KeySize 1 k136 ∧ x2KeySize 1 k136 ≤ 512 ∧ v258.length = 13 := by decide +kernel
theorem chk136 : trialKeyChk 1 k136 13 gj258 x2Trial_258 v258 :=
  trialKeyChk_intro 1 k136 13 gj258 x2Trial_258 v258 small136 gjok136 vok136
def k137 : x2Key 1 := ⟨137, by decide⟩
x2_gj_cols gj259 259 1 4 4 7 256
theorem gjc137_0 : (List.range 21).all (fun d => gjCheck 256 1 4 4 7 7 7 6 (x2JCols 259 (0 + d)) (gj259.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok137 : ∀ d < x2KeySize 1 k137, gjCheck 256 1 (x2KeyTypes 1 k137 0) (x2KeyTypes 1 k137 1) (x2KeyTypes 1 k137 2) (x2KeyMult 1 k137 0) (x2KeyMult 1 k137 1) (x2KeyMult 1 k137 2) (x2JCols (x2KeyGlobal 1 k137) d) (gj259.getD d 0) = true := by
  have hr : x2KeySize 1 k137 = 21 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 7 7 7 6 (x2JCols 259 d) (gj259.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 7 7 7 6 (x2JCols 259 d) (gj259.getD d 0)) 0 21 gjc137_0 d (Nat.zero_le d) (by omega)
x2_v_cols v259 gj259 259 256 294
theorem vc137_0 : (List.range 12).all (fun c => vCheck 256 294 21 gj259 (x2Trial_259.getD (0 + c) 0) (v259.getD (0 + c) 0)) = true := by decide +kernel
theorem vok137 : ∀ c < 12, vCheck 256 (x2KeyMult 1 k137 0 * x2KeyMult 1 k137 1 * x2KeyMult 1 k137 2) (x2KeySize 1 k137) gj259 (x2Trial_259.getD c 0) (v259.getD c 0) = true := by
  intro c hc
  show vCheck 256 294 21 gj259 (x2Trial_259.getD c 0) (v259.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 294 21 gj259 (x2Trial_259.getD c 0) (v259.getD c 0)) 0 12 vc137_0 c (Nat.zero_le c) (by omega)
theorem small137 : x2KeyDegree 1 k137 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k137 0 ∧ 1 ≤ x2KeyMult 1 k137 1 ∧ 1 ≤ x2KeyMult 1 k137 2 ∧ glRowOK 1 (x2KeyTypes 1 k137 0) (x2KeyMult 1 k137 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k137 1) (x2KeyMult 1 k137 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k137 2) (x2KeyMult 1 k137 2) 512 = true ∧ gj259.length = x2KeySize 1 k137 ∧ x2KeySize 1 k137 ≤ 512 ∧ v259.length = 12 := by decide +kernel
theorem chk137 : trialKeyChk 1 k137 12 gj259 x2Trial_259 v259 :=
  trialKeyChk_intro 1 k137 12 gj259 x2Trial_259 v259 small137 gjok137 vok137

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k136, ibFS [(v258, v258, 94810963968000)]), (k137, ibFS [(v259, v259, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 4, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN136 : N k136 = x2TrialForm 1 k136) (hN137 : N k137 = x2TrialForm 1 k137) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 4 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k136 13 _ gj258 x2Trial_258 v258 (by decide) (by rw [hN136]; exact trialForm_eq 1 k136 13 x2Trial_258 (by decide) rfl) chk136
  · exact keyOK_of_trialChk 1 N k137 12 _ gj259 x2Trial_259 v259 (by decide) (by rw [hN137]; exact trialForm_eq 1 k137 12 x2Trial_259 (by decide) rfl) chk137

end ThreeCopyQutritWerner.X2.InK1x447
