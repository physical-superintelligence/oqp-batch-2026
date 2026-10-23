module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 5, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x557
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k152 : x2Key 1 := ⟨152, by decide⟩
x2_gj_cols gj274 274 1 5 5 7 256
theorem gjc152_0 : (List.range 28).all (fun d => gjCheck 256 1 5 5 7 7 7 6 (x2JCols 274 (0 + d)) (gj274.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok152 : ∀ d < x2KeySize 1 k152, gjCheck 256 1 (x2KeyTypes 1 k152 0) (x2KeyTypes 1 k152 1) (x2KeyTypes 1 k152 2) (x2KeyMult 1 k152 0) (x2KeyMult 1 k152 1) (x2KeyMult 1 k152 2) (x2JCols (x2KeyGlobal 1 k152) d) (gj274.getD d 0) = true := by
  have hr : x2KeySize 1 k152 = 28 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 7 7 7 6 (x2JCols 274 d) (gj274.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 7 7 7 6 (x2JCols 274 d) (gj274.getD d 0)) 0 28 gjc152_0 d (Nat.zero_le d) (by omega)
x2_v_cols v274 gj274 274 256 294
theorem vc152_0 : (List.range 15).all (fun c => vCheck 256 294 28 gj274 (x2Trial_274.getD (0 + c) 0) (v274.getD (0 + c) 0)) = true := by decide +kernel
theorem vok152 : ∀ c < 15, vCheck 256 (x2KeyMult 1 k152 0 * x2KeyMult 1 k152 1 * x2KeyMult 1 k152 2) (x2KeySize 1 k152) gj274 (x2Trial_274.getD c 0) (v274.getD c 0) = true := by
  intro c hc
  show vCheck 256 294 28 gj274 (x2Trial_274.getD c 0) (v274.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 294 28 gj274 (x2Trial_274.getD c 0) (v274.getD c 0)) 0 15 vc152_0 c (Nat.zero_le c) (by omega)
theorem small152 : x2KeyDegree 1 k152 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k152 0 ∧ 1 ≤ x2KeyMult 1 k152 1 ∧ 1 ≤ x2KeyMult 1 k152 2 ∧ glRowOK 1 (x2KeyTypes 1 k152 0) (x2KeyMult 1 k152 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k152 1) (x2KeyMult 1 k152 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k152 2) (x2KeyMult 1 k152 2) 512 = true ∧ gj274.length = x2KeySize 1 k152 ∧ x2KeySize 1 k152 ≤ 512 ∧ v274.length = 15 := by decide +kernel
theorem chk152 : trialKeyChk 1 k152 15 gj274 x2Trial_274 v274 :=
  trialKeyChk_intro 1 k152 15 gj274 x2Trial_274 v274 small152 gjok152 vok152
def k153 : x2Key 1 := ⟨153, by decide⟩
x2_gj_cols gj275 275 1 5 5 7 256
theorem gjc153_0 : (List.range 21).all (fun d => gjCheck 256 1 5 5 7 7 7 6 (x2JCols 275 (0 + d)) (gj275.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok153 : ∀ d < x2KeySize 1 k153, gjCheck 256 1 (x2KeyTypes 1 k153 0) (x2KeyTypes 1 k153 1) (x2KeyTypes 1 k153 2) (x2KeyMult 1 k153 0) (x2KeyMult 1 k153 1) (x2KeyMult 1 k153 2) (x2JCols (x2KeyGlobal 1 k153) d) (gj275.getD d 0) = true := by
  have hr : x2KeySize 1 k153 = 21 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 7 7 7 6 (x2JCols 275 d) (gj275.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 7 7 7 6 (x2JCols 275 d) (gj275.getD d 0)) 0 21 gjc153_0 d (Nat.zero_le d) (by omega)
x2_v_cols v275 gj275 275 256 294
theorem vc153_0 : (List.range 14).all (fun c => vCheck 256 294 21 gj275 (x2Trial_275.getD (0 + c) 0) (v275.getD (0 + c) 0)) = true := by decide +kernel
theorem vok153 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k153 0 * x2KeyMult 1 k153 1 * x2KeyMult 1 k153 2) (x2KeySize 1 k153) gj275 (x2Trial_275.getD c 0) (v275.getD c 0) = true := by
  intro c hc
  show vCheck 256 294 21 gj275 (x2Trial_275.getD c 0) (v275.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 294 21 gj275 (x2Trial_275.getD c 0) (v275.getD c 0)) 0 14 vc153_0 c (Nat.zero_le c) (by omega)
theorem small153 : x2KeyDegree 1 k153 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k153 0 ∧ 1 ≤ x2KeyMult 1 k153 1 ∧ 1 ≤ x2KeyMult 1 k153 2 ∧ glRowOK 1 (x2KeyTypes 1 k153 0) (x2KeyMult 1 k153 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k153 1) (x2KeyMult 1 k153 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k153 2) (x2KeyMult 1 k153 2) 512 = true ∧ gj275.length = x2KeySize 1 k153 ∧ x2KeySize 1 k153 ≤ 512 ∧ v275.length = 14 := by decide +kernel
theorem chk153 : trialKeyChk 1 k153 14 gj275 x2Trial_275 v275 :=
  trialKeyChk_intro 1 k153 14 gj275 x2Trial_275 v275 small153 gjok153 vok153

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k152, ibFS [(v274, v274, 94810963968000)]), (k153, ibFS [(v275, v275, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![5, 5, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN152 : N k152 = x2TrialForm 1 k152) (hN153 : N k153 = x2TrialForm 1 k153) :
    ∀ e ∈ ks, keyOK (x2Mult 1 5 * x2Mult 1 5 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k152 15 _ gj274 x2Trial_274 v274 (by decide) (by rw [hN152]; exact trialForm_eq 1 k152 15 x2Trial_274 (by decide) rfl) chk152
  · exact keyOK_of_trialChk 1 N k153 14 _ gj275 x2Trial_275 v275 (by decide) (by rw [hN153]; exact trialForm_eq 1 k153 14 x2Trial_275 (by decide) rfl) chk153

end ThreeCopyQutritWerner.X2.InK1x557
