module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x066
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k31 : x2Key 1 := ⟨31, by decide⟩
x2_gj_cols gj153 153 1 0 6 6 256
theorem gjc31_0 : (List.range 24).all (fun d => gjCheck 256 1 0 6 6 1 17 17 (x2JCols 153 (0 + d)) (gj153.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok31 : ∀ d < x2KeySize 1 k31, gjCheck 256 1 (x2KeyTypes 1 k31 0) (x2KeyTypes 1 k31 1) (x2KeyTypes 1 k31 2) (x2KeyMult 1 k31 0) (x2KeyMult 1 k31 1) (x2KeyMult 1 k31 2) (x2JCols (x2KeyGlobal 1 k31) d) (gj153.getD d 0) = true := by
  have hr : x2KeySize 1 k31 = 24 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 6 6 1 17 17 (x2JCols 153 d) (gj153.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 6 6 1 17 17 (x2JCols 153 d) (gj153.getD d 0)) 0 24 gjc31_0 d (Nat.zero_le d) (by omega)
x2_v_cols v153 gj153 153 256 289
theorem vc31_0 : (List.range 11).all (fun c => vCheck 256 289 24 gj153 (x2Trial_153.getD (0 + c) 0) (v153.getD (0 + c) 0)) = true := by decide +kernel
theorem vok31 : ∀ c < 11, vCheck 256 (x2KeyMult 1 k31 0 * x2KeyMult 1 k31 1 * x2KeyMult 1 k31 2) (x2KeySize 1 k31) gj153 (x2Trial_153.getD c 0) (v153.getD c 0) = true := by
  intro c hc
  show vCheck 256 289 24 gj153 (x2Trial_153.getD c 0) (v153.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 289 24 gj153 (x2Trial_153.getD c 0) (v153.getD c 0)) 0 11 vc31_0 c (Nat.zero_le c) (by omega)
theorem small31 : x2KeyDegree 1 k31 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k31 0 ∧ 1 ≤ x2KeyMult 1 k31 1 ∧ 1 ≤ x2KeyMult 1 k31 2 ∧ glRowOK 1 (x2KeyTypes 1 k31 0) (x2KeyMult 1 k31 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k31 1) (x2KeyMult 1 k31 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k31 2) (x2KeyMult 1 k31 2) 512 = true ∧ gj153.length = x2KeySize 1 k31 ∧ x2KeySize 1 k31 ≤ 512 ∧ v153.length = 11 := by decide +kernel
theorem chk31 : trialKeyChk 1 k31 11 gj153 x2Trial_153 v153 :=
  trialKeyChk_intro 1 k31 11 gj153 x2Trial_153 v153 small31 gjok31 vok31
def k32 : x2Key 1 := ⟨32, by decide⟩
x2_gj_cols gj154 154 1 0 6 6 256
theorem gjc32_0 : (List.range 24).all (fun d => gjCheck 256 1 0 6 6 1 17 17 (x2JCols 154 (0 + d)) (gj154.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok32 : ∀ d < x2KeySize 1 k32, gjCheck 256 1 (x2KeyTypes 1 k32 0) (x2KeyTypes 1 k32 1) (x2KeyTypes 1 k32 2) (x2KeyMult 1 k32 0) (x2KeyMult 1 k32 1) (x2KeyMult 1 k32 2) (x2JCols (x2KeyGlobal 1 k32) d) (gj154.getD d 0) = true := by
  have hr : x2KeySize 1 k32 = 24 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 6 6 1 17 17 (x2JCols 154 d) (gj154.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 6 6 1 17 17 (x2JCols 154 d) (gj154.getD d 0)) 0 24 gjc32_0 d (Nat.zero_le d) (by omega)
x2_v_cols v154 gj154 154 256 289
theorem vc32_0 : (List.range 11).all (fun c => vCheck 256 289 24 gj154 (x2Trial_154.getD (0 + c) 0) (v154.getD (0 + c) 0)) = true := by decide +kernel
theorem vok32 : ∀ c < 11, vCheck 256 (x2KeyMult 1 k32 0 * x2KeyMult 1 k32 1 * x2KeyMult 1 k32 2) (x2KeySize 1 k32) gj154 (x2Trial_154.getD c 0) (v154.getD c 0) = true := by
  intro c hc
  show vCheck 256 289 24 gj154 (x2Trial_154.getD c 0) (v154.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 289 24 gj154 (x2Trial_154.getD c 0) (v154.getD c 0)) 0 11 vc32_0 c (Nat.zero_le c) (by omega)
theorem small32 : x2KeyDegree 1 k32 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k32 0 ∧ 1 ≤ x2KeyMult 1 k32 1 ∧ 1 ≤ x2KeyMult 1 k32 2 ∧ glRowOK 1 (x2KeyTypes 1 k32 0) (x2KeyMult 1 k32 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k32 1) (x2KeyMult 1 k32 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k32 2) (x2KeyMult 1 k32 2) 512 = true ∧ gj154.length = x2KeySize 1 k32 ∧ x2KeySize 1 k32 ≤ 512 ∧ v154.length = 11 := by decide +kernel
theorem chk32 : trialKeyChk 1 k32 11 gj154 x2Trial_154 v154 :=
  trialKeyChk_intro 1 k32 11 gj154 x2Trial_154 v154 small32 gjok32 vok32

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k31, ibFS [(v153, v153, 94810963968000)]), (k32, ibFS [(v154, v154, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN31 : N k31 = x2TrialForm 1 k31) (hN32 : N k32 = x2TrialForm 1 k32) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k31 11 _ gj153 x2Trial_153 v153 (by decide) (by rw [hN31]; exact trialForm_eq 1 k31 11 x2Trial_153 (by decide) rfl) chk31
  · exact keyOK_of_trialChk 1 N k32 11 _ gj154 x2Trial_154 v154 (by decide) (by rw [hN32]; exact trialForm_eq 1 k32 11 x2Trial_154 (by decide) rfl) chk32

end ThreeCopyQutritWerner.X2.InK1x066
