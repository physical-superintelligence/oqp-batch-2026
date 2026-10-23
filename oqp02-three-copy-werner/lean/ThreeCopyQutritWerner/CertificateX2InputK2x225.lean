module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x225
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k66 : x2Key 2 := ⟨66, by decide⟩
x2_gj_cols gj357 357 2 2 2 5 256
theorem gjc66_0 : (List.range 16).all (fun d => gjCheck 256 2 2 2 5 5 5 10 (x2JCols 357 (0 + d)) (gj357.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok66 : ∀ d < x2KeySize 2 k66, gjCheck 256 2 (x2KeyTypes 2 k66 0) (x2KeyTypes 2 k66 1) (x2KeyTypes 2 k66 2) (x2KeyMult 2 k66 0) (x2KeyMult 2 k66 1) (x2KeyMult 2 k66 2) (x2JCols (x2KeyGlobal 2 k66) d) (gj357.getD d 0) = true := by
  have hr : x2KeySize 2 k66 = 16 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 5 5 5 10 (x2JCols 357 d) (gj357.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 5 5 5 10 (x2JCols 357 d) (gj357.getD d 0)) 0 16 gjc66_0 d (Nat.zero_le d) (by omega)
x2_v_cols v357 gj357 357 256 250
theorem vc66_0 : (List.range 10).all (fun c => vCheck 256 250 16 gj357 (x2Trial_357.getD (0 + c) 0) (v357.getD (0 + c) 0)) = true := by decide +kernel
theorem vok66 : ∀ c < 10, vCheck 256 (x2KeyMult 2 k66 0 * x2KeyMult 2 k66 1 * x2KeyMult 2 k66 2) (x2KeySize 2 k66) gj357 (x2Trial_357.getD c 0) (v357.getD c 0) = true := by
  intro c hc
  show vCheck 256 250 16 gj357 (x2Trial_357.getD c 0) (v357.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 250 16 gj357 (x2Trial_357.getD c 0) (v357.getD c 0)) 0 10 vc66_0 c (Nat.zero_le c) (by omega)
theorem small66 : x2KeyDegree 2 k66 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k66 0 ∧ 1 ≤ x2KeyMult 2 k66 1 ∧ 1 ≤ x2KeyMult 2 k66 2 ∧ glRowOK 2 (x2KeyTypes 2 k66 0) (x2KeyMult 2 k66 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k66 1) (x2KeyMult 2 k66 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k66 2) (x2KeyMult 2 k66 2) 512 = true ∧ gj357.length = x2KeySize 2 k66 ∧ x2KeySize 2 k66 ≤ 512 ∧ v357.length = 10 := by decide +kernel
theorem chk66 : trialKeyChk 2 k66 10 gj357 x2Trial_357 v357 :=
  trialKeyChk_intro 2 k66 10 gj357 x2Trial_357 v357 small66 gjok66 vok66
def k67 : x2Key 2 := ⟨67, by decide⟩
x2_gj_cols gj358 358 2 2 2 5 256
theorem gjc67_0 : (List.range 8).all (fun d => gjCheck 256 2 2 2 5 5 5 10 (x2JCols 358 (0 + d)) (gj358.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok67 : ∀ d < x2KeySize 2 k67, gjCheck 256 2 (x2KeyTypes 2 k67 0) (x2KeyTypes 2 k67 1) (x2KeyTypes 2 k67 2) (x2KeyMult 2 k67 0) (x2KeyMult 2 k67 1) (x2KeyMult 2 k67 2) (x2JCols (x2KeyGlobal 2 k67) d) (gj358.getD d 0) = true := by
  have hr : x2KeySize 2 k67 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 5 5 5 10 (x2JCols 358 d) (gj358.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 5 5 5 10 (x2JCols 358 d) (gj358.getD d 0)) 0 8 gjc67_0 d (Nat.zero_le d) (by omega)
x2_v_cols v358 gj358 358 256 250
theorem vc67_0 : (List.range 6).all (fun c => vCheck 256 250 8 gj358 (x2Trial_358.getD (0 + c) 0) (v358.getD (0 + c) 0)) = true := by decide +kernel
theorem vok67 : ∀ c < 6, vCheck 256 (x2KeyMult 2 k67 0 * x2KeyMult 2 k67 1 * x2KeyMult 2 k67 2) (x2KeySize 2 k67) gj358 (x2Trial_358.getD c 0) (v358.getD c 0) = true := by
  intro c hc
  show vCheck 256 250 8 gj358 (x2Trial_358.getD c 0) (v358.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 250 8 gj358 (x2Trial_358.getD c 0) (v358.getD c 0)) 0 6 vc67_0 c (Nat.zero_le c) (by omega)
theorem small67 : x2KeyDegree 2 k67 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k67 0 ∧ 1 ≤ x2KeyMult 2 k67 1 ∧ 1 ≤ x2KeyMult 2 k67 2 ∧ glRowOK 2 (x2KeyTypes 2 k67 0) (x2KeyMult 2 k67 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k67 1) (x2KeyMult 2 k67 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k67 2) (x2KeyMult 2 k67 2) 512 = true ∧ gj358.length = x2KeySize 2 k67 ∧ x2KeySize 2 k67 ≤ 512 ∧ v358.length = 6 := by decide +kernel
theorem chk67 : trialKeyChk 2 k67 6 gj358 x2Trial_358 v358 :=
  trialKeyChk_intro 2 k67 6 gj358 x2Trial_358 v358 small67 gjok67 vok67

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k66, ibFS [(v357, v357, 94810963968000)]), (k67, ibFS [(v358, v358, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 2, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN66 : N k66 = x2TrialForm 2 k66) (hN67 : N k67 = x2TrialForm 2 k67) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 2 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k66 10 _ gj357 x2Trial_357 v357 (by decide) (by rw [hN66]; exact trialForm_eq 2 k66 10 x2Trial_357 (by decide) rfl) chk66
  · exact keyOK_of_trialChk 2 N k67 6 _ gj358 x2Trial_358 v358 (by decide) (by rw [hN67]; exact trialForm_eq 2 k67 6 x2Trial_358 (by decide) rfl) chk67

end ThreeCopyQutritWerner.X2.InK2x225
