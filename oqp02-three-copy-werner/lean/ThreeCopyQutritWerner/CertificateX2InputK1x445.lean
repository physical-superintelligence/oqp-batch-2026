module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x445
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k132 : x2Key 1 := ⟨132, by decide⟩
x2_gj_cols gj254 254 1 4 4 5 256
theorem gjc132_0 : (List.range 31).all (fun d => gjCheck 256 1 4 4 5 7 7 7 (x2JCols 254 (0 + d)) (gj254.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok132 : ∀ d < x2KeySize 1 k132, gjCheck 256 1 (x2KeyTypes 1 k132 0) (x2KeyTypes 1 k132 1) (x2KeyTypes 1 k132 2) (x2KeyMult 1 k132 0) (x2KeyMult 1 k132 1) (x2KeyMult 1 k132 2) (x2JCols (x2KeyGlobal 1 k132) d) (gj254.getD d 0) = true := by
  have hr : x2KeySize 1 k132 = 31 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 5 7 7 7 (x2JCols 254 d) (gj254.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 5 7 7 7 (x2JCols 254 d) (gj254.getD d 0)) 0 31 gjc132_0 d (Nat.zero_le d) (by omega)
x2_v_cols v254 gj254 254 256 343
theorem vc132_0 : (List.range 20).all (fun c => vCheck 256 343 31 gj254 (x2Trial_254.getD (0 + c) 0) (v254.getD (0 + c) 0)) = true := by decide +kernel
theorem vok132 : ∀ c < 20, vCheck 256 (x2KeyMult 1 k132 0 * x2KeyMult 1 k132 1 * x2KeyMult 1 k132 2) (x2KeySize 1 k132) gj254 (x2Trial_254.getD c 0) (v254.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 31 gj254 (x2Trial_254.getD c 0) (v254.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 31 gj254 (x2Trial_254.getD c 0) (v254.getD c 0)) 0 20 vc132_0 c (Nat.zero_le c) (by omega)
theorem small132 : x2KeyDegree 1 k132 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k132 0 ∧ 1 ≤ x2KeyMult 1 k132 1 ∧ 1 ≤ x2KeyMult 1 k132 2 ∧ glRowOK 1 (x2KeyTypes 1 k132 0) (x2KeyMult 1 k132 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k132 1) (x2KeyMult 1 k132 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k132 2) (x2KeyMult 1 k132 2) 512 = true ∧ gj254.length = x2KeySize 1 k132 ∧ x2KeySize 1 k132 ≤ 512 ∧ v254.length = 20 := by decide +kernel
theorem chk132 : trialKeyChk 1 k132 20 gj254 x2Trial_254 v254 :=
  trialKeyChk_intro 1 k132 20 gj254 x2Trial_254 v254 small132 gjok132 vok132
def k133 : x2Key 1 := ⟨133, by decide⟩
x2_gj_cols gj255 255 1 4 4 5 256
theorem gjc133_0 : (List.range 26).all (fun d => gjCheck 256 1 4 4 5 7 7 7 (x2JCols 255 (0 + d)) (gj255.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok133 : ∀ d < x2KeySize 1 k133, gjCheck 256 1 (x2KeyTypes 1 k133 0) (x2KeyTypes 1 k133 1) (x2KeyTypes 1 k133 2) (x2KeyMult 1 k133 0) (x2KeyMult 1 k133 1) (x2KeyMult 1 k133 2) (x2JCols (x2KeyGlobal 1 k133) d) (gj255.getD d 0) = true := by
  have hr : x2KeySize 1 k133 = 26 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 4 5 7 7 7 (x2JCols 255 d) (gj255.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 4 5 7 7 7 (x2JCols 255 d) (gj255.getD d 0)) 0 26 gjc133_0 d (Nat.zero_le d) (by omega)
x2_v_cols v255 gj255 255 256 343
theorem vc133_0 : (List.range 16).all (fun c => vCheck 256 343 26 gj255 (x2Trial_255.getD (0 + c) 0) (v255.getD (0 + c) 0)) = true := by decide +kernel
theorem vok133 : ∀ c < 16, vCheck 256 (x2KeyMult 1 k133 0 * x2KeyMult 1 k133 1 * x2KeyMult 1 k133 2) (x2KeySize 1 k133) gj255 (x2Trial_255.getD c 0) (v255.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 26 gj255 (x2Trial_255.getD c 0) (v255.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 26 gj255 (x2Trial_255.getD c 0) (v255.getD c 0)) 0 16 vc133_0 c (Nat.zero_le c) (by omega)
theorem small133 : x2KeyDegree 1 k133 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k133 0 ∧ 1 ≤ x2KeyMult 1 k133 1 ∧ 1 ≤ x2KeyMult 1 k133 2 ∧ glRowOK 1 (x2KeyTypes 1 k133 0) (x2KeyMult 1 k133 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k133 1) (x2KeyMult 1 k133 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k133 2) (x2KeyMult 1 k133 2) 512 = true ∧ gj255.length = x2KeySize 1 k133 ∧ x2KeySize 1 k133 ≤ 512 ∧ v255.length = 16 := by decide +kernel
theorem chk133 : trialKeyChk 1 k133 16 gj255 x2Trial_255 v255 :=
  trialKeyChk_intro 1 k133 16 gj255 x2Trial_255 v255 small133 gjok133 vok133

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k132, ibFS [(v254, v254, 94810963968000)]), (k133, ibFS [(v255, v255, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN132 : N k132 = x2TrialForm 1 k132) (hN133 : N k133 = x2TrialForm 1 k133) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 4 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k132 20 _ gj254 x2Trial_254 v254 (by decide) (by rw [hN132]; exact trialForm_eq 1 k132 20 x2Trial_254 (by decide) rfl) chk132
  · exact keyOK_of_trialChk 1 N k133 16 _ gj255 x2Trial_255 v255 (by decide) (by rw [hN133]; exact trialForm_eq 1 k133 16 x2Trial_255 (by decide) rfl) chk133

end ThreeCopyQutritWerner.X2.InK1x445
