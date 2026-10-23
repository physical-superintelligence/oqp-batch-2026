module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x445
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k104 : x2Key 2 := ⟨104, by decide⟩
x2_gj_cols gj395 395 2 4 4 5 256
theorem gjc104_0 : (List.range 104).all (fun d => gjCheck 256 2 4 4 5 15 15 10 (x2JCols 395 (0 + d)) (gj395.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok104 : ∀ d < x2KeySize 2 k104, gjCheck 256 2 (x2KeyTypes 2 k104 0) (x2KeyTypes 2 k104 1) (x2KeyTypes 2 k104 2) (x2KeyMult 2 k104 0) (x2KeyMult 2 k104 1) (x2KeyMult 2 k104 2) (x2JCols (x2KeyGlobal 2 k104) d) (gj395.getD d 0) = true := by
  have hr : x2KeySize 2 k104 = 104 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 5 15 15 10 (x2JCols 395 d) (gj395.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 5 15 15 10 (x2JCols 395 d) (gj395.getD d 0)) 0 104 gjc104_0 d (Nat.zero_le d) (by omega)
x2_v_cols v395 gj395 395 256 2250
theorem vc104_0 : (List.range 86).all (fun c => vCheck 256 2250 104 gj395 (x2Trial_395.getD (0 + c) 0) (v395.getD (0 + c) 0)) = true := by decide +kernel
theorem vok104 : ∀ c < 86, vCheck 256 (x2KeyMult 2 k104 0 * x2KeyMult 2 k104 1 * x2KeyMult 2 k104 2) (x2KeySize 2 k104) gj395 (x2Trial_395.getD c 0) (v395.getD c 0) = true := by
  intro c hc
  show vCheck 256 2250 104 gj395 (x2Trial_395.getD c 0) (v395.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 2250 104 gj395 (x2Trial_395.getD c 0) (v395.getD c 0)) 0 86 vc104_0 c (Nat.zero_le c) (by omega)
theorem small104 : x2KeyDegree 2 k104 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k104 0 ∧ 1 ≤ x2KeyMult 2 k104 1 ∧ 1 ≤ x2KeyMult 2 k104 2 ∧ glRowOK 2 (x2KeyTypes 2 k104 0) (x2KeyMult 2 k104 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k104 1) (x2KeyMult 2 k104 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k104 2) (x2KeyMult 2 k104 2) 512 = true ∧ gj395.length = x2KeySize 2 k104 ∧ x2KeySize 2 k104 ≤ 512 ∧ v395.length = 86 := by decide +kernel
theorem chk104 : trialKeyChk 2 k104 86 gj395 x2Trial_395 v395 :=
  trialKeyChk_intro 2 k104 86 gj395 x2Trial_395 v395 small104 gjok104 vok104
def k105 : x2Key 2 := ⟨105, by decide⟩
x2_gj_cols gj396 396 2 4 4 5 256
theorem gjc105_0 : (List.range 84).all (fun d => gjCheck 256 2 4 4 5 15 15 10 (x2JCols 396 (0 + d)) (gj396.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok105 : ∀ d < x2KeySize 2 k105, gjCheck 256 2 (x2KeyTypes 2 k105 0) (x2KeyTypes 2 k105 1) (x2KeyTypes 2 k105 2) (x2KeyMult 2 k105 0) (x2KeyMult 2 k105 1) (x2KeyMult 2 k105 2) (x2JCols (x2KeyGlobal 2 k105) d) (gj396.getD d 0) = true := by
  have hr : x2KeySize 2 k105 = 84 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 5 15 15 10 (x2JCols 396 d) (gj396.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 5 15 15 10 (x2JCols 396 d) (gj396.getD d 0)) 0 84 gjc105_0 d (Nat.zero_le d) (by omega)
x2_v_cols v396 gj396 396 256 2250
theorem vc105_0 : (List.range 74).all (fun c => vCheck 256 2250 84 gj396 (x2Trial_396.getD (0 + c) 0) (v396.getD (0 + c) 0)) = true := by decide +kernel
theorem vok105 : ∀ c < 74, vCheck 256 (x2KeyMult 2 k105 0 * x2KeyMult 2 k105 1 * x2KeyMult 2 k105 2) (x2KeySize 2 k105) gj396 (x2Trial_396.getD c 0) (v396.getD c 0) = true := by
  intro c hc
  show vCheck 256 2250 84 gj396 (x2Trial_396.getD c 0) (v396.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 2250 84 gj396 (x2Trial_396.getD c 0) (v396.getD c 0)) 0 74 vc105_0 c (Nat.zero_le c) (by omega)
theorem small105 : x2KeyDegree 2 k105 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k105 0 ∧ 1 ≤ x2KeyMult 2 k105 1 ∧ 1 ≤ x2KeyMult 2 k105 2 ∧ glRowOK 2 (x2KeyTypes 2 k105 0) (x2KeyMult 2 k105 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k105 1) (x2KeyMult 2 k105 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k105 2) (x2KeyMult 2 k105 2) 512 = true ∧ gj396.length = x2KeySize 2 k105 ∧ x2KeySize 2 k105 ≤ 512 ∧ v396.length = 74 := by decide +kernel
theorem chk105 : trialKeyChk 2 k105 74 gj396 x2Trial_396 v396 :=
  trialKeyChk_intro 2 k105 74 gj396 x2Trial_396 v396 small105 gjok105 vok105

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k104, ibFS [(v395, v395, 94810963968000)]), (k105, ibFS [(v396, v396, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![4, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN104 : N k104 = x2TrialForm 2 k104) (hN105 : N k105 = x2TrialForm 2 k105) :
    ∀ e ∈ ks, keyOK (x2Mult 2 4 * x2Mult 2 4 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k104 86 _ gj395 x2Trial_395 v395 (by decide) (by rw [hN104]; exact trialForm_eq 2 k104 86 x2Trial_395 (by decide) rfl) chk104
  · exact keyOK_of_trialChk 2 N k105 74 _ gj396 x2Trial_396 v396 (by decide) (by rw [hN105]; exact trialForm_eq 2 k105 74 x2Trial_396 (by decide) rfl) chk105

end ThreeCopyQutritWerner.X2.InK2x445
