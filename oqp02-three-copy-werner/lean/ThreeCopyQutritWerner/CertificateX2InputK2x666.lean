module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (6, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x666
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k120 : x2Key 2 := ⟨120, by decide⟩
x2_gj_cols gj411 411 2 6 6 6 256
theorem gjc120_0 : (List.range 21).all (fun d => gjCheck 256 2 6 6 6 11 11 11 (x2JCols 411 (0 + d)) (gj411.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok120 : ∀ d < x2KeySize 2 k120, gjCheck 256 2 (x2KeyTypes 2 k120 0) (x2KeyTypes 2 k120 1) (x2KeyTypes 2 k120 2) (x2KeyMult 2 k120 0) (x2KeyMult 2 k120 1) (x2KeyMult 2 k120 2) (x2JCols (x2KeyGlobal 2 k120) d) (gj411.getD d 0) = true := by
  have hr : x2KeySize 2 k120 = 21 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 6 6 6 11 11 11 (x2JCols 411 d) (gj411.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 6 6 6 11 11 11 (x2JCols 411 d) (gj411.getD d 0)) 0 21 gjc120_0 d (Nat.zero_le d) (by omega)
x2_v_cols v411 gj411 411 256 1331
theorem vc120_0 : (List.range 21).all (fun c => vCheck 256 1331 21 gj411 (x2Trial_411.getD (0 + c) 0) (v411.getD (0 + c) 0)) = true := by decide +kernel
theorem vok120 : ∀ c < 21, vCheck 256 (x2KeyMult 2 k120 0 * x2KeyMult 2 k120 1 * x2KeyMult 2 k120 2) (x2KeySize 2 k120) gj411 (x2Trial_411.getD c 0) (v411.getD c 0) = true := by
  intro c hc
  show vCheck 256 1331 21 gj411 (x2Trial_411.getD c 0) (v411.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1331 21 gj411 (x2Trial_411.getD c 0) (v411.getD c 0)) 0 21 vc120_0 c (Nat.zero_le c) (by omega)
theorem small120 : x2KeyDegree 2 k120 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k120 0 ∧ 1 ≤ x2KeyMult 2 k120 1 ∧ 1 ≤ x2KeyMult 2 k120 2 ∧ glRowOK 2 (x2KeyTypes 2 k120 0) (x2KeyMult 2 k120 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k120 1) (x2KeyMult 2 k120 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k120 2) (x2KeyMult 2 k120 2) 512 = true ∧ gj411.length = x2KeySize 2 k120 ∧ x2KeySize 2 k120 ≤ 512 ∧ v411.length = 21 := by decide +kernel
theorem chk120 : trialKeyChk 2 k120 21 gj411 x2Trial_411 v411 :=
  trialKeyChk_intro 2 k120 21 gj411 x2Trial_411 v411 small120 gjok120 vok120
def k121 : x2Key 2 := ⟨121, by decide⟩
x2_gj_cols gj412 412 2 6 6 6 256
theorem gjc121_0 : (List.range 14).all (fun d => gjCheck 256 2 6 6 6 11 11 11 (x2JCols 412 (0 + d)) (gj412.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok121 : ∀ d < x2KeySize 2 k121, gjCheck 256 2 (x2KeyTypes 2 k121 0) (x2KeyTypes 2 k121 1) (x2KeyTypes 2 k121 2) (x2KeyMult 2 k121 0) (x2KeyMult 2 k121 1) (x2KeyMult 2 k121 2) (x2JCols (x2KeyGlobal 2 k121) d) (gj412.getD d 0) = true := by
  have hr : x2KeySize 2 k121 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 6 6 6 11 11 11 (x2JCols 412 d) (gj412.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 6 6 6 11 11 11 (x2JCols 412 d) (gj412.getD d 0)) 0 14 gjc121_0 d (Nat.zero_le d) (by omega)
x2_v_cols v412 gj412 412 256 1331
theorem vc121_0 : (List.range 14).all (fun c => vCheck 256 1331 14 gj412 (x2Trial_412.getD (0 + c) 0) (v412.getD (0 + c) 0)) = true := by decide +kernel
theorem vok121 : ∀ c < 14, vCheck 256 (x2KeyMult 2 k121 0 * x2KeyMult 2 k121 1 * x2KeyMult 2 k121 2) (x2KeySize 2 k121) gj412 (x2Trial_412.getD c 0) (v412.getD c 0) = true := by
  intro c hc
  show vCheck 256 1331 14 gj412 (x2Trial_412.getD c 0) (v412.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1331 14 gj412 (x2Trial_412.getD c 0) (v412.getD c 0)) 0 14 vc121_0 c (Nat.zero_le c) (by omega)
theorem small121 : x2KeyDegree 2 k121 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k121 0 ∧ 1 ≤ x2KeyMult 2 k121 1 ∧ 1 ≤ x2KeyMult 2 k121 2 ∧ glRowOK 2 (x2KeyTypes 2 k121 0) (x2KeyMult 2 k121 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k121 1) (x2KeyMult 2 k121 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k121 2) (x2KeyMult 2 k121 2) 512 = true ∧ gj412.length = x2KeySize 2 k121 ∧ x2KeySize 2 k121 ≤ 512 ∧ v412.length = 14 := by decide +kernel
theorem chk121 : trialKeyChk 2 k121 14 gj412 x2Trial_412 v412 :=
  trialKeyChk_intro 2 k121 14 gj412 x2Trial_412 v412 small121 gjok121 vok121
def k122 : x2Key 2 := ⟨122, by decide⟩
x2_gj_cols gj413 413 2 6 6 6 256
theorem gjc122_0 : (List.range 38).all (fun d => gjCheck 256 2 6 6 6 11 11 11 (x2JCols 413 (0 + d)) (gj413.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok122 : ∀ d < x2KeySize 2 k122, gjCheck 256 2 (x2KeyTypes 2 k122 0) (x2KeyTypes 2 k122 1) (x2KeyTypes 2 k122 2) (x2KeyMult 2 k122 0) (x2KeyMult 2 k122 1) (x2KeyMult 2 k122 2) (x2JCols (x2KeyGlobal 2 k122) d) (gj413.getD d 0) = true := by
  have hr : x2KeySize 2 k122 = 38 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 6 6 6 11 11 11 (x2JCols 413 d) (gj413.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 6 6 6 11 11 11 (x2JCols 413 d) (gj413.getD d 0)) 0 38 gjc122_0 d (Nat.zero_le d) (by omega)
x2_v_cols v413 gj413 413 256 1331
theorem vc122_0 : (List.range 38).all (fun c => vCheck 256 1331 38 gj413 (x2Trial_413.getD (0 + c) 0) (v413.getD (0 + c) 0)) = true := by decide +kernel
theorem vok122 : ∀ c < 38, vCheck 256 (x2KeyMult 2 k122 0 * x2KeyMult 2 k122 1 * x2KeyMult 2 k122 2) (x2KeySize 2 k122) gj413 (x2Trial_413.getD c 0) (v413.getD c 0) = true := by
  intro c hc
  show vCheck 256 1331 38 gj413 (x2Trial_413.getD c 0) (v413.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1331 38 gj413 (x2Trial_413.getD c 0) (v413.getD c 0)) 0 38 vc122_0 c (Nat.zero_le c) (by omega)
x2_p_cols p413 v413 11
theorem pok122 : ∀ c < 38, partnerCheck (x2KeyMult 2 k122 0) (v413.getD c 0) (p413.getD c 0) = true := by
  intro c hc
  show partnerCheck 11 (v413.getD c 0) (p413.getD c 0) = true
  have h : (List.range 38).all (fun c => partnerCheck 11 (v413.getD c 0) (p413.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small122 : x2KeyDegree 2 k122 = 2 ∧ x2KeyMult 2 k122 0 = x2KeyMult 2 k122 1 ∧ x2KeyMult 2 k122 1 = x2KeyMult 2 k122 2 ∧ 1 ≤ x2KeyMult 2 k122 0 ∧ glRowOK 2 (x2KeyTypes 2 k122 0) (x2KeyMult 2 k122 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k122 1) (x2KeyMult 2 k122 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k122 2) (x2KeyMult 2 k122 2) 512 = true ∧ gj413.length = x2KeySize 2 k122 ∧ x2KeySize 2 k122 ≤ 512 ∧ v413.length = 38 ∧ p413.length = 38 := by decide +kernel
theorem chk122 : trial2KeyChk 2 k122 38 gj413 x2Trial_413 v413 p413 :=
  trial2KeyChk_intro 2 k122 38 gj413 x2Trial_413 v413 p413 small122 gjok122 vok122 pok122

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k120, ibFS [(v411, v411, 94810963968000)]), (k121, ibFS [(v412, v412, 94810963968000)]), (k122, ibFS [(v413, v413, 94810963968000), (p413, p413, 31603654656000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![6, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN120 : N k120 = x2TrialForm 2 k120) (hN121 : N k121 = x2TrialForm 2 k121) (hN122 : N k122 = x2TrialForm 2 k122) :
    ∀ e ∈ ks, keyOK (x2Mult 2 6 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_trialChk 2 N k120 21 _ gj411 x2Trial_411 v411 (by decide) (by rw [hN120]; exact trialForm_eq 2 k120 21 x2Trial_411 (by decide) rfl) chk120
  · exact keyOK_of_trialChk 2 N k121 14 _ gj412 x2Trial_412 v412 (by decide) (by rw [hN121]; exact trialForm_eq 2 k121 14 x2Trial_412 (by decide) rfl) chk121
  · exact keyOK_of_trial2Chk 2 N k122 38 _ gj413 x2Trial_413 v413 p413 (by decide) (by rw [hN122]; exact trialForm_eq 2 k122 38 x2Trial_413 (by decide) rfl) chk122

end ThreeCopyQutritWerner.X2.InK2x666
