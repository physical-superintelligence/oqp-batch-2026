module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 5, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x257
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k98 : x2Key 1 := ⟨98, by decide⟩
x2_gj_cols gj220 220 1 2 5 7 256
theorem gjc98_0 : (List.range 14).all (fun d => gjCheck 256 1 2 5 7 2 7 6 (x2JCols 220 (0 + d)) (gj220.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok98 : ∀ d < x2KeySize 1 k98, gjCheck 256 1 (x2KeyTypes 1 k98 0) (x2KeyTypes 1 k98 1) (x2KeyTypes 1 k98 2) (x2KeyMult 1 k98 0) (x2KeyMult 1 k98 1) (x2KeyMult 1 k98 2) (x2JCols (x2KeyGlobal 1 k98) d) (gj220.getD d 0) = true := by
  have hr : x2KeySize 1 k98 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 5 7 2 7 6 (x2JCols 220 d) (gj220.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 5 7 2 7 6 (x2JCols 220 d) (gj220.getD d 0)) 0 14 gjc98_0 d (Nat.zero_le d) (by omega)
x2_v_cols v220 gj220 220 256 84
theorem vc98_0 : (List.range 5).all (fun c => vCheck 256 84 14 gj220 (x2Trial_220.getD (0 + c) 0) (v220.getD (0 + c) 0)) = true := by decide +kernel
theorem vok98 : ∀ c < 5, vCheck 256 (x2KeyMult 1 k98 0 * x2KeyMult 1 k98 1 * x2KeyMult 1 k98 2) (x2KeySize 1 k98) gj220 (x2Trial_220.getD c 0) (v220.getD c 0) = true := by
  intro c hc
  show vCheck 256 84 14 gj220 (x2Trial_220.getD c 0) (v220.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 84 14 gj220 (x2Trial_220.getD c 0) (v220.getD c 0)) 0 5 vc98_0 c (Nat.zero_le c) (by omega)
theorem small98 : x2KeyDegree 1 k98 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k98 0 ∧ 1 ≤ x2KeyMult 1 k98 1 ∧ 1 ≤ x2KeyMult 1 k98 2 ∧ glRowOK 1 (x2KeyTypes 1 k98 0) (x2KeyMult 1 k98 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k98 1) (x2KeyMult 1 k98 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k98 2) (x2KeyMult 1 k98 2) 512 = true ∧ gj220.length = x2KeySize 1 k98 ∧ x2KeySize 1 k98 ≤ 512 ∧ v220.length = 5 := by decide +kernel
theorem chk98 : trialKeyChk 1 k98 5 gj220 x2Trial_220 v220 :=
  trialKeyChk_intro 1 k98 5 gj220 x2Trial_220 v220 small98 gjok98 vok98

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k98, ibFS [(v220, v220, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 5, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN98 : N k98 = x2TrialForm 1 k98) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 5 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k98 5 _ gj220 x2Trial_220 v220 (by decide) (by rw [hN98]; exact trialForm_eq 1 k98 5 x2Trial_220 (by decide) rfl) chk98

end ThreeCopyQutritWerner.X2.InK1x257
