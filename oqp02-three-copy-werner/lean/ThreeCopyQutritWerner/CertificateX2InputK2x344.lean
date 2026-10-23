module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x344
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k92 : x2Key 2 := ⟨92, by decide⟩
x2_gj_cols gj383 383 2 3 4 4 256
theorem gjc92_0 : (List.range 52).all (fun d => gjCheck 256 2 3 4 4 5 15 15 (x2JCols 383 (0 + d)) (gj383.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok92 : ∀ d < x2KeySize 2 k92, gjCheck 256 2 (x2KeyTypes 2 k92 0) (x2KeyTypes 2 k92 1) (x2KeyTypes 2 k92 2) (x2KeyMult 2 k92 0) (x2KeyMult 2 k92 1) (x2KeyMult 2 k92 2) (x2JCols (x2KeyGlobal 2 k92) d) (gj383.getD d 0) = true := by
  have hr : x2KeySize 2 k92 = 52 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 4 4 5 15 15 (x2JCols 383 d) (gj383.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 4 4 5 15 15 (x2JCols 383 d) (gj383.getD d 0)) 0 52 gjc92_0 d (Nat.zero_le d) (by omega)
x2_v_cols v383 gj383 383 256 1125
theorem vc92_0 : (List.range 28).all (fun c => vCheck 256 1125 52 gj383 (x2Trial_383.getD (0 + c) 0) (v383.getD (0 + c) 0)) = true := by decide +kernel
theorem vok92 : ∀ c < 28, vCheck 256 (x2KeyMult 2 k92 0 * x2KeyMult 2 k92 1 * x2KeyMult 2 k92 2) (x2KeySize 2 k92) gj383 (x2Trial_383.getD c 0) (v383.getD c 0) = true := by
  intro c hc
  show vCheck 256 1125 52 gj383 (x2Trial_383.getD c 0) (v383.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1125 52 gj383 (x2Trial_383.getD c 0) (v383.getD c 0)) 0 28 vc92_0 c (Nat.zero_le c) (by omega)
theorem small92 : x2KeyDegree 2 k92 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k92 0 ∧ 1 ≤ x2KeyMult 2 k92 1 ∧ 1 ≤ x2KeyMult 2 k92 2 ∧ glRowOK 2 (x2KeyTypes 2 k92 0) (x2KeyMult 2 k92 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k92 1) (x2KeyMult 2 k92 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k92 2) (x2KeyMult 2 k92 2) 512 = true ∧ gj383.length = x2KeySize 2 k92 ∧ x2KeySize 2 k92 ≤ 512 ∧ v383.length = 28 := by decide +kernel
theorem chk92 : trialKeyChk 2 k92 28 gj383 x2Trial_383 v383 :=
  trialKeyChk_intro 2 k92 28 gj383 x2Trial_383 v383 small92 gjok92 vok92
def k93 : x2Key 2 := ⟨93, by decide⟩
x2_gj_cols gj384 384 2 3 4 4 256
theorem gjc93_0 : (List.range 42).all (fun d => gjCheck 256 2 3 4 4 5 15 15 (x2JCols 384 (0 + d)) (gj384.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok93 : ∀ d < x2KeySize 2 k93, gjCheck 256 2 (x2KeyTypes 2 k93 0) (x2KeyTypes 2 k93 1) (x2KeyTypes 2 k93 2) (x2KeyMult 2 k93 0) (x2KeyMult 2 k93 1) (x2KeyMult 2 k93 2) (x2JCols (x2KeyGlobal 2 k93) d) (gj384.getD d 0) = true := by
  have hr : x2KeySize 2 k93 = 42 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 4 4 5 15 15 (x2JCols 384 d) (gj384.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 4 4 5 15 15 (x2JCols 384 d) (gj384.getD d 0)) 0 42 gjc93_0 d (Nat.zero_le d) (by omega)
x2_v_cols v384 gj384 384 256 1125
theorem vc93_0 : (List.range 26).all (fun c => vCheck 256 1125 42 gj384 (x2Trial_384.getD (0 + c) 0) (v384.getD (0 + c) 0)) = true := by decide +kernel
theorem vok93 : ∀ c < 26, vCheck 256 (x2KeyMult 2 k93 0 * x2KeyMult 2 k93 1 * x2KeyMult 2 k93 2) (x2KeySize 2 k93) gj384 (x2Trial_384.getD c 0) (v384.getD c 0) = true := by
  intro c hc
  show vCheck 256 1125 42 gj384 (x2Trial_384.getD c 0) (v384.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1125 42 gj384 (x2Trial_384.getD c 0) (v384.getD c 0)) 0 26 vc93_0 c (Nat.zero_le c) (by omega)
theorem small93 : x2KeyDegree 2 k93 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k93 0 ∧ 1 ≤ x2KeyMult 2 k93 1 ∧ 1 ≤ x2KeyMult 2 k93 2 ∧ glRowOK 2 (x2KeyTypes 2 k93 0) (x2KeyMult 2 k93 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k93 1) (x2KeyMult 2 k93 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k93 2) (x2KeyMult 2 k93 2) 512 = true ∧ gj384.length = x2KeySize 2 k93 ∧ x2KeySize 2 k93 ≤ 512 ∧ v384.length = 26 := by decide +kernel
theorem chk93 : trialKeyChk 2 k93 26 gj384 x2Trial_384 v384 :=
  trialKeyChk_intro 2 k93 26 gj384 x2Trial_384 v384 small93 gjok93 vok93

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k92, ibFS [(v383, v383, 94810963968000)]), (k93, ibFS [(v384, v384, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN92 : N k92 = x2TrialForm 2 k92) (hN93 : N k93 = x2TrialForm 2 k93) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 4 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k92 28 _ gj383 x2Trial_383 v383 (by decide) (by rw [hN92]; exact trialForm_eq 2 k92 28 x2Trial_383 (by decide) rfl) chk92
  · exact keyOK_of_trialChk 2 N k93 26 _ gj384 x2Trial_384 v384 (by decide) (by rw [hN93]; exact trialForm_eq 2 k93 26 x2Trial_384 (by decide) rfl) chk93

end ThreeCopyQutritWerner.X2.InK2x344
