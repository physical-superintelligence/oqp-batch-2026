module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x266
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k82 : x2Key 2 := ⟨82, by decide⟩
x2_gj_cols gj373 373 2 2 6 6 256
theorem gjc82_0 : (List.range 29).all (fun d => gjCheck 256 2 2 6 6 5 11 11 (x2JCols 373 (0 + d)) (gj373.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok82 : ∀ d < x2KeySize 2 k82, gjCheck 256 2 (x2KeyTypes 2 k82 0) (x2KeyTypes 2 k82 1) (x2KeyTypes 2 k82 2) (x2KeyMult 2 k82 0) (x2KeyMult 2 k82 1) (x2KeyMult 2 k82 2) (x2JCols (x2KeyGlobal 2 k82) d) (gj373.getD d 0) = true := by
  have hr : x2KeySize 2 k82 = 29 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 6 6 5 11 11 (x2JCols 373 d) (gj373.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 6 6 5 11 11 (x2JCols 373 d) (gj373.getD d 0)) 0 29 gjc82_0 d (Nat.zero_le d) (by omega)
x2_v_cols v373 gj373 373 256 605
theorem vc82_0 : (List.range 29).all (fun c => vCheck 256 605 29 gj373 (x2Trial_373.getD (0 + c) 0) (v373.getD (0 + c) 0)) = true := by decide +kernel
theorem vok82 : ∀ c < 29, vCheck 256 (x2KeyMult 2 k82 0 * x2KeyMult 2 k82 1 * x2KeyMult 2 k82 2) (x2KeySize 2 k82) gj373 (x2Trial_373.getD c 0) (v373.getD c 0) = true := by
  intro c hc
  show vCheck 256 605 29 gj373 (x2Trial_373.getD c 0) (v373.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 605 29 gj373 (x2Trial_373.getD c 0) (v373.getD c 0)) 0 29 vc82_0 c (Nat.zero_le c) (by omega)
theorem small82 : x2KeyDegree 2 k82 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k82 0 ∧ 1 ≤ x2KeyMult 2 k82 1 ∧ 1 ≤ x2KeyMult 2 k82 2 ∧ glRowOK 2 (x2KeyTypes 2 k82 0) (x2KeyMult 2 k82 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k82 1) (x2KeyMult 2 k82 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k82 2) (x2KeyMult 2 k82 2) 512 = true ∧ gj373.length = x2KeySize 2 k82 ∧ x2KeySize 2 k82 ≤ 512 ∧ v373.length = 29 := by decide +kernel
theorem chk82 : trialKeyChk 2 k82 29 gj373 x2Trial_373 v373 :=
  trialKeyChk_intro 2 k82 29 gj373 x2Trial_373 v373 small82 gjok82 vok82
def k83 : x2Key 2 := ⟨83, by decide⟩
x2_gj_cols gj374 374 2 2 6 6 256
theorem gjc83_0 : (List.range 21).all (fun d => gjCheck 256 2 2 6 6 5 11 11 (x2JCols 374 (0 + d)) (gj374.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok83 : ∀ d < x2KeySize 2 k83, gjCheck 256 2 (x2KeyTypes 2 k83 0) (x2KeyTypes 2 k83 1) (x2KeyTypes 2 k83 2) (x2KeyMult 2 k83 0) (x2KeyMult 2 k83 1) (x2KeyMult 2 k83 2) (x2JCols (x2KeyGlobal 2 k83) d) (gj374.getD d 0) = true := by
  have hr : x2KeySize 2 k83 = 21 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 6 6 5 11 11 (x2JCols 374 d) (gj374.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 6 6 5 11 11 (x2JCols 374 d) (gj374.getD d 0)) 0 21 gjc83_0 d (Nat.zero_le d) (by omega)
x2_v_cols v374 gj374 374 256 605
theorem vc83_0 : (List.range 21).all (fun c => vCheck 256 605 21 gj374 (x2Trial_374.getD (0 + c) 0) (v374.getD (0 + c) 0)) = true := by decide +kernel
theorem vok83 : ∀ c < 21, vCheck 256 (x2KeyMult 2 k83 0 * x2KeyMult 2 k83 1 * x2KeyMult 2 k83 2) (x2KeySize 2 k83) gj374 (x2Trial_374.getD c 0) (v374.getD c 0) = true := by
  intro c hc
  show vCheck 256 605 21 gj374 (x2Trial_374.getD c 0) (v374.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 605 21 gj374 (x2Trial_374.getD c 0) (v374.getD c 0)) 0 21 vc83_0 c (Nat.zero_le c) (by omega)
theorem small83 : x2KeyDegree 2 k83 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k83 0 ∧ 1 ≤ x2KeyMult 2 k83 1 ∧ 1 ≤ x2KeyMult 2 k83 2 ∧ glRowOK 2 (x2KeyTypes 2 k83 0) (x2KeyMult 2 k83 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k83 1) (x2KeyMult 2 k83 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k83 2) (x2KeyMult 2 k83 2) 512 = true ∧ gj374.length = x2KeySize 2 k83 ∧ x2KeySize 2 k83 ≤ 512 ∧ v374.length = 21 := by decide +kernel
theorem chk83 : trialKeyChk 2 k83 21 gj374 x2Trial_374 v374 :=
  trialKeyChk_intro 2 k83 21 gj374 x2Trial_374 v374 small83 gjok83 vok83

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k82, ibFS [(v373, v373, 94810963968000)]), (k83, ibFS [(v374, v374, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN82 : N k82 = x2TrialForm 2 k82) (hN83 : N k83 = x2TrialForm 2 k83) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k82 29 _ gj373 x2Trial_373 v373 (by decide) (by rw [hN82]; exact trialForm_eq 2 k82 29 x2Trial_373 (by decide) rfl) chk82
  · exact keyOK_of_trialChk 2 N k83 21 _ gj374 x2Trial_374 v374 (by decide) (by rw [hN83]; exact trialForm_eq 2 k83 21 x2Trial_374 (by decide) rfl) chk83

end ThreeCopyQutritWerner.X2.InK2x266
