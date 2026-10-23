module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x466
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k111 : x2Key 2 := ⟨111, by decide⟩
x2_gj_cols gj402 402 2 4 6 6 256
theorem gjc111_0 : (List.range 81).all (fun d => gjCheck 256 2 4 6 6 15 11 11 (x2JCols 402 (0 + d)) (gj402.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok111 : ∀ d < x2KeySize 2 k111, gjCheck 256 2 (x2KeyTypes 2 k111 0) (x2KeyTypes 2 k111 1) (x2KeyTypes 2 k111 2) (x2KeyMult 2 k111 0) (x2KeyMult 2 k111 1) (x2KeyMult 2 k111 2) (x2JCols (x2KeyGlobal 2 k111) d) (gj402.getD d 0) = true := by
  have hr : x2KeySize 2 k111 = 81 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 6 6 15 11 11 (x2JCols 402 d) (gj402.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 6 6 15 11 11 (x2JCols 402 d) (gj402.getD d 0)) 0 81 gjc111_0 d (Nat.zero_le d) (by omega)
x2_v_cols v402 gj402 402 256 1815
theorem vc111_0 : (List.range 81).all (fun c => vCheck 256 1815 81 gj402 (x2Trial_402.getD (0 + c) 0) (v402.getD (0 + c) 0)) = true := by decide +kernel
theorem vok111 : ∀ c < 81, vCheck 256 (x2KeyMult 2 k111 0 * x2KeyMult 2 k111 1 * x2KeyMult 2 k111 2) (x2KeySize 2 k111) gj402 (x2Trial_402.getD c 0) (v402.getD c 0) = true := by
  intro c hc
  show vCheck 256 1815 81 gj402 (x2Trial_402.getD c 0) (v402.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1815 81 gj402 (x2Trial_402.getD c 0) (v402.getD c 0)) 0 81 vc111_0 c (Nat.zero_le c) (by omega)
theorem small111 : x2KeyDegree 2 k111 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k111 0 ∧ 1 ≤ x2KeyMult 2 k111 1 ∧ 1 ≤ x2KeyMult 2 k111 2 ∧ glRowOK 2 (x2KeyTypes 2 k111 0) (x2KeyMult 2 k111 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k111 1) (x2KeyMult 2 k111 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k111 2) (x2KeyMult 2 k111 2) 512 = true ∧ gj402.length = x2KeySize 2 k111 ∧ x2KeySize 2 k111 ≤ 512 ∧ v402.length = 81 := by decide +kernel
theorem chk111 : trialKeyChk 2 k111 81 gj402 x2Trial_402 v402 :=
  trialKeyChk_intro 2 k111 81 gj402 x2Trial_402 v402 small111 gjok111 vok111
def k112 : x2Key 2 := ⟨112, by decide⟩
x2_gj_cols gj403 403 2 4 6 6 256
theorem gjc112_0 : (List.range 70).all (fun d => gjCheck 256 2 4 6 6 15 11 11 (x2JCols 403 (0 + d)) (gj403.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok112 : ∀ d < x2KeySize 2 k112, gjCheck 256 2 (x2KeyTypes 2 k112 0) (x2KeyTypes 2 k112 1) (x2KeyTypes 2 k112 2) (x2KeyMult 2 k112 0) (x2KeyMult 2 k112 1) (x2KeyMult 2 k112 2) (x2JCols (x2KeyGlobal 2 k112) d) (gj403.getD d 0) = true := by
  have hr : x2KeySize 2 k112 = 70 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 6 6 15 11 11 (x2JCols 403 d) (gj403.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 6 6 15 11 11 (x2JCols 403 d) (gj403.getD d 0)) 0 70 gjc112_0 d (Nat.zero_le d) (by omega)
x2_v_cols v403 gj403 403 256 1815
theorem vc112_0 : (List.range 70).all (fun c => vCheck 256 1815 70 gj403 (x2Trial_403.getD (0 + c) 0) (v403.getD (0 + c) 0)) = true := by decide +kernel
theorem vok112 : ∀ c < 70, vCheck 256 (x2KeyMult 2 k112 0 * x2KeyMult 2 k112 1 * x2KeyMult 2 k112 2) (x2KeySize 2 k112) gj403 (x2Trial_403.getD c 0) (v403.getD c 0) = true := by
  intro c hc
  show vCheck 256 1815 70 gj403 (x2Trial_403.getD c 0) (v403.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1815 70 gj403 (x2Trial_403.getD c 0) (v403.getD c 0)) 0 70 vc112_0 c (Nat.zero_le c) (by omega)
theorem small112 : x2KeyDegree 2 k112 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k112 0 ∧ 1 ≤ x2KeyMult 2 k112 1 ∧ 1 ≤ x2KeyMult 2 k112 2 ∧ glRowOK 2 (x2KeyTypes 2 k112 0) (x2KeyMult 2 k112 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k112 1) (x2KeyMult 2 k112 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k112 2) (x2KeyMult 2 k112 2) 512 = true ∧ gj403.length = x2KeySize 2 k112 ∧ x2KeySize 2 k112 ≤ 512 ∧ v403.length = 70 := by decide +kernel
theorem chk112 : trialKeyChk 2 k112 70 gj403 x2Trial_403 v403 :=
  trialKeyChk_intro 2 k112 70 gj403 x2Trial_403 v403 small112 gjok112 vok112

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k111, ibFS [(v402, v402, 94810963968000)]), (k112, ibFS [(v403, v403, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![4, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN111 : N k111 = x2TrialForm 2 k111) (hN112 : N k112 = x2TrialForm 2 k112) :
    ∀ e ∈ ks, keyOK (x2Mult 2 4 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k111 81 _ gj402 x2Trial_402 v402 (by decide) (by rw [hN111]; exact trialForm_eq 2 k111 81 x2Trial_402 (by decide) rfl) chk111
  · exact keyOK_of_trialChk 2 N k112 70 _ gj403 x2Trial_403 v403 (by decide) (by rw [hN112]; exact trialForm_eq 2 k112 70 x2Trial_403 (by decide) rfl) chk112

end ThreeCopyQutritWerner.X2.InK2x466
