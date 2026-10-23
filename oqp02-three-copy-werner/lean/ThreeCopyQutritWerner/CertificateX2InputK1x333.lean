module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 3) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x333
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k104 : x2Key 1 := ⟨104, by decide⟩
x2_gj_cols gj226 226 1 3 3 3 256
theorem gjc104_0 : (List.range 24).all (fun d => gjCheck 256 1 3 3 3 9 9 9 (x2JCols 226 (0 + d)) (gj226.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok104 : ∀ d < x2KeySize 1 k104, gjCheck 256 1 (x2KeyTypes 1 k104 0) (x2KeyTypes 1 k104 1) (x2KeyTypes 1 k104 2) (x2KeyMult 1 k104 0) (x2KeyMult 1 k104 1) (x2KeyMult 1 k104 2) (x2JCols (x2KeyGlobal 1 k104) d) (gj226.getD d 0) = true := by
  have hr : x2KeySize 1 k104 = 24 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 3 9 9 9 (x2JCols 226 d) (gj226.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 3 9 9 9 (x2JCols 226 d) (gj226.getD d 0)) 0 24 gjc104_0 d (Nat.zero_le d) (by omega)
x2_v_cols v226 gj226 226 256 729
theorem vc104_0 : (List.range 2).all (fun c => vCheck 256 729 24 gj226 (x2Trial_226.getD (0 + c) 0) (v226.getD (0 + c) 0)) = true := by decide +kernel
theorem vok104 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k104 0 * x2KeyMult 1 k104 1 * x2KeyMult 1 k104 2) (x2KeySize 1 k104) gj226 (x2Trial_226.getD c 0) (v226.getD c 0) = true := by
  intro c hc
  show vCheck 256 729 24 gj226 (x2Trial_226.getD c 0) (v226.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 729 24 gj226 (x2Trial_226.getD c 0) (v226.getD c 0)) 0 2 vc104_0 c (Nat.zero_le c) (by omega)
theorem small104 : x2KeyDegree 1 k104 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k104 0 ∧ 1 ≤ x2KeyMult 1 k104 1 ∧ 1 ≤ x2KeyMult 1 k104 2 ∧ glRowOK 1 (x2KeyTypes 1 k104 0) (x2KeyMult 1 k104 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k104 1) (x2KeyMult 1 k104 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k104 2) (x2KeyMult 1 k104 2) 512 = true ∧ gj226.length = x2KeySize 1 k104 ∧ x2KeySize 1 k104 ≤ 512 ∧ v226.length = 2 := by decide +kernel
theorem chk104 : trialKeyChk 1 k104 2 gj226 x2Trial_226 v226 :=
  trialKeyChk_intro 1 k104 2 gj226 x2Trial_226 v226 small104 gjok104 vok104
def k105 : x2Key 1 := ⟨105, by decide⟩
x2_gj_cols gj227 227 1 3 3 3 256
theorem gjc105_0 : (List.range 15).all (fun d => gjCheck 256 1 3 3 3 9 9 9 (x2JCols 227 (0 + d)) (gj227.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok105 : ∀ d < x2KeySize 1 k105, gjCheck 256 1 (x2KeyTypes 1 k105 0) (x2KeyTypes 1 k105 1) (x2KeyTypes 1 k105 2) (x2KeyMult 1 k105 0) (x2KeyMult 1 k105 1) (x2KeyMult 1 k105 2) (x2JCols (x2KeyGlobal 1 k105) d) (gj227.getD d 0) = true := by
  have hr : x2KeySize 1 k105 = 15 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 3 9 9 9 (x2JCols 227 d) (gj227.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 3 9 9 9 (x2JCols 227 d) (gj227.getD d 0)) 0 15 gjc105_0 d (Nat.zero_le d) (by omega)
x2_v_cols v227 gj227 227 256 729
theorem vc105_0 : (List.range 2).all (fun c => vCheck 256 729 15 gj227 (x2Trial_227.getD (0 + c) 0) (v227.getD (0 + c) 0)) = true := by decide +kernel
theorem vok105 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k105 0 * x2KeyMult 1 k105 1 * x2KeyMult 1 k105 2) (x2KeySize 1 k105) gj227 (x2Trial_227.getD c 0) (v227.getD c 0) = true := by
  intro c hc
  show vCheck 256 729 15 gj227 (x2Trial_227.getD c 0) (v227.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 729 15 gj227 (x2Trial_227.getD c 0) (v227.getD c 0)) 0 2 vc105_0 c (Nat.zero_le c) (by omega)
theorem small105 : x2KeyDegree 1 k105 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k105 0 ∧ 1 ≤ x2KeyMult 1 k105 1 ∧ 1 ≤ x2KeyMult 1 k105 2 ∧ glRowOK 1 (x2KeyTypes 1 k105 0) (x2KeyMult 1 k105 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k105 1) (x2KeyMult 1 k105 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k105 2) (x2KeyMult 1 k105 2) 512 = true ∧ gj227.length = x2KeySize 1 k105 ∧ x2KeySize 1 k105 ≤ 512 ∧ v227.length = 2 := by decide +kernel
theorem chk105 : trialKeyChk 1 k105 2 gj227 x2Trial_227 v227 :=
  trialKeyChk_intro 1 k105 2 gj227 x2Trial_227 v227 small105 gjok105 vok105
def k106 : x2Key 1 := ⟨106, by decide⟩
x2_gj_cols gj228 228 1 3 3 3 256
theorem gjc106_0 : (List.range 39).all (fun d => gjCheck 256 1 3 3 3 9 9 9 (x2JCols 228 (0 + d)) (gj228.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok106 : ∀ d < x2KeySize 1 k106, gjCheck 256 1 (x2KeyTypes 1 k106 0) (x2KeyTypes 1 k106 1) (x2KeyTypes 1 k106 2) (x2KeyMult 1 k106 0) (x2KeyMult 1 k106 1) (x2KeyMult 1 k106 2) (x2JCols (x2KeyGlobal 1 k106) d) (gj228.getD d 0) = true := by
  have hr : x2KeySize 1 k106 = 39 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 3 9 9 9 (x2JCols 228 d) (gj228.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 3 9 9 9 (x2JCols 228 d) (gj228.getD d 0)) 0 39 gjc106_0 d (Nat.zero_le d) (by omega)
x2_v_cols v228 gj228 228 256 729
theorem vc106_0 : (List.range 4).all (fun c => vCheck 256 729 39 gj228 (x2Trial_228.getD (0 + c) 0) (v228.getD (0 + c) 0)) = true := by decide +kernel
theorem vok106 : ∀ c < 4, vCheck 256 (x2KeyMult 1 k106 0 * x2KeyMult 1 k106 1 * x2KeyMult 1 k106 2) (x2KeySize 1 k106) gj228 (x2Trial_228.getD c 0) (v228.getD c 0) = true := by
  intro c hc
  show vCheck 256 729 39 gj228 (x2Trial_228.getD c 0) (v228.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 729 39 gj228 (x2Trial_228.getD c 0) (v228.getD c 0)) 0 4 vc106_0 c (Nat.zero_le c) (by omega)
x2_p_cols p228 v228 9
theorem pok106 : ∀ c < 4, partnerCheck (x2KeyMult 1 k106 0) (v228.getD c 0) (p228.getD c 0) = true := by
  intro c hc
  show partnerCheck 9 (v228.getD c 0) (p228.getD c 0) = true
  have h : (List.range 4).all (fun c => partnerCheck 9 (v228.getD c 0) (p228.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small106 : x2KeyDegree 1 k106 = 2 ∧ x2KeyMult 1 k106 0 = x2KeyMult 1 k106 1 ∧ x2KeyMult 1 k106 1 = x2KeyMult 1 k106 2 ∧ 1 ≤ x2KeyMult 1 k106 0 ∧ glRowOK 1 (x2KeyTypes 1 k106 0) (x2KeyMult 1 k106 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k106 1) (x2KeyMult 1 k106 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k106 2) (x2KeyMult 1 k106 2) 512 = true ∧ gj228.length = x2KeySize 1 k106 ∧ x2KeySize 1 k106 ≤ 512 ∧ v228.length = 4 ∧ p228.length = 4 := by decide +kernel
theorem chk106 : trial2KeyChk 1 k106 4 gj228 x2Trial_228 v228 p228 :=
  trial2KeyChk_intro 1 k106 4 gj228 x2Trial_228 v228 p228 small106 gjok106 vok106 pok106

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k104, ibFS [(v226, v226, 94810963968000)]), (k105, ibFS [(v227, v227, 94810963968000)]), (k106, ibFS [(v228, v228, 94810963968000), (p228, p228, 31603654656000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 3, 3] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN104 : N k104 = x2TrialForm 1 k104) (hN105 : N k105 = x2TrialForm 1 k105) (hN106 : N k106 = x2TrialForm 1 k106) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 3 * x2Mult 1 3) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_trialChk 1 N k104 2 _ gj226 x2Trial_226 v226 (by decide) (by rw [hN104]; exact trialForm_eq 1 k104 2 x2Trial_226 (by decide) rfl) chk104
  · exact keyOK_of_trialChk 1 N k105 2 _ gj227 x2Trial_227 v227 (by decide) (by rw [hN105]; exact trialForm_eq 1 k105 2 x2Trial_227 (by decide) rfl) chk105
  · exact keyOK_of_trial2Chk 1 N k106 4 _ gj228 x2Trial_228 v228 p228 (by decide) (by rw [hN106]; exact trialForm_eq 1 k106 4 x2Trial_228 (by decide) rfl) chk106

end ThreeCopyQutritWerner.X2.InK1x333
