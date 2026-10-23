module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 5, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x556
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k150 : x2Key 1 := ⟨150, by decide⟩
x2_gj_cols gj272 272 1 5 5 6 256
theorem gjc150_0 : (List.range 78).all (fun d => gjCheck 256 1 5 5 6 7 7 17 (x2JCols 272 (0 + d)) (gj272.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok150 : ∀ d < x2KeySize 1 k150, gjCheck 256 1 (x2KeyTypes 1 k150 0) (x2KeyTypes 1 k150 1) (x2KeyTypes 1 k150 2) (x2KeyMult 1 k150 0) (x2KeyMult 1 k150 1) (x2KeyMult 1 k150 2) (x2JCols (x2KeyGlobal 1 k150) d) (gj272.getD d 0) = true := by
  have hr : x2KeySize 1 k150 = 78 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 6 7 7 17 (x2JCols 272 d) (gj272.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 6 7 7 17 (x2JCols 272 d) (gj272.getD d 0)) 0 78 gjc150_0 d (Nat.zero_le d) (by omega)
x2_v_cols v272 gj272 272 256 833
theorem vc150_0 : (List.range 54).all (fun c => vCheck 256 833 78 gj272 (x2Trial_272.getD (0 + c) 0) (v272.getD (0 + c) 0)) = true := by decide +kernel
theorem vok150 : ∀ c < 54, vCheck 256 (x2KeyMult 1 k150 0 * x2KeyMult 1 k150 1 * x2KeyMult 1 k150 2) (x2KeySize 1 k150) gj272 (x2Trial_272.getD c 0) (v272.getD c 0) = true := by
  intro c hc
  show vCheck 256 833 78 gj272 (x2Trial_272.getD c 0) (v272.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 833 78 gj272 (x2Trial_272.getD c 0) (v272.getD c 0)) 0 54 vc150_0 c (Nat.zero_le c) (by omega)
theorem small150 : x2KeyDegree 1 k150 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k150 0 ∧ 1 ≤ x2KeyMult 1 k150 1 ∧ 1 ≤ x2KeyMult 1 k150 2 ∧ glRowOK 1 (x2KeyTypes 1 k150 0) (x2KeyMult 1 k150 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k150 1) (x2KeyMult 1 k150 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k150 2) (x2KeyMult 1 k150 2) 512 = true ∧ gj272.length = x2KeySize 1 k150 ∧ x2KeySize 1 k150 ≤ 512 ∧ v272.length = 54 := by decide +kernel
theorem chk150 : trialKeyChk 1 k150 54 gj272 x2Trial_272 v272 :=
  trialKeyChk_intro 1 k150 54 gj272 x2Trial_272 v272 small150 gjok150 vok150
def k151 : x2Key 1 := ⟨151, by decide⟩
x2_gj_cols gj273 273 1 5 5 6 256
theorem gjc151_0 : (List.range 60).all (fun d => gjCheck 256 1 5 5 6 7 7 17 (x2JCols 273 (0 + d)) (gj273.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok151 : ∀ d < x2KeySize 1 k151, gjCheck 256 1 (x2KeyTypes 1 k151 0) (x2KeyTypes 1 k151 1) (x2KeyTypes 1 k151 2) (x2KeyMult 1 k151 0) (x2KeyMult 1 k151 1) (x2KeyMult 1 k151 2) (x2JCols (x2KeyGlobal 1 k151) d) (gj273.getD d 0) = true := by
  have hr : x2KeySize 1 k151 = 60 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 5 6 7 7 17 (x2JCols 273 d) (gj273.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 5 6 7 7 17 (x2JCols 273 d) (gj273.getD d 0)) 0 60 gjc151_0 d (Nat.zero_le d) (by omega)
x2_v_cols v273 gj273 273 256 833
theorem vc151_0 : (List.range 42).all (fun c => vCheck 256 833 60 gj273 (x2Trial_273.getD (0 + c) 0) (v273.getD (0 + c) 0)) = true := by decide +kernel
theorem vok151 : ∀ c < 42, vCheck 256 (x2KeyMult 1 k151 0 * x2KeyMult 1 k151 1 * x2KeyMult 1 k151 2) (x2KeySize 1 k151) gj273 (x2Trial_273.getD c 0) (v273.getD c 0) = true := by
  intro c hc
  show vCheck 256 833 60 gj273 (x2Trial_273.getD c 0) (v273.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 833 60 gj273 (x2Trial_273.getD c 0) (v273.getD c 0)) 0 42 vc151_0 c (Nat.zero_le c) (by omega)
theorem small151 : x2KeyDegree 1 k151 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k151 0 ∧ 1 ≤ x2KeyMult 1 k151 1 ∧ 1 ≤ x2KeyMult 1 k151 2 ∧ glRowOK 1 (x2KeyTypes 1 k151 0) (x2KeyMult 1 k151 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k151 1) (x2KeyMult 1 k151 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k151 2) (x2KeyMult 1 k151 2) 512 = true ∧ gj273.length = x2KeySize 1 k151 ∧ x2KeySize 1 k151 ≤ 512 ∧ v273.length = 42 := by decide +kernel
theorem chk151 : trialKeyChk 1 k151 42 gj273 x2Trial_273 v273 :=
  trialKeyChk_intro 1 k151 42 gj273 x2Trial_273 v273 small151 gjok151 vok151

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k150, ibFS [(v272, v272, 94810963968000)]), (k151, ibFS [(v273, v273, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![5, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN150 : N k150 = x2TrialForm 1 k150) (hN151 : N k151 = x2TrialForm 1 k151) :
    ∀ e ∈ ks, keyOK (x2Mult 1 5 * x2Mult 1 5 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k150 54 _ gj272 x2Trial_272 v272 (by decide) (by rw [hN150]; exact trialForm_eq 1 k150 54 x2Trial_272 (by decide) rfl) chk150
  · exact keyOK_of_trialChk 1 N k151 42 _ gj273 x2Trial_273 v273 (by decide) (by rw [hN151]; exact trialForm_eq 1 k151 42 x2Trial_273 (by decide) rfl) chk151

end ThreeCopyQutritWerner.X2.InK1x556
