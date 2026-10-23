module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x336
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k111 : x2Key 1 := ⟨111, by decide⟩
x2_gj_cols gj233 233 1 3 3 6 256
theorem gjc111_0 : (List.range 74).all (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 233 (0 + d)) (gj233.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc111_74 : (List.range 52).all (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 233 (74 + d)) (gj233.getD (74 + d) 0)) = true := by decide +kernel
theorem gjok111 : ∀ d < x2KeySize 1 k111, gjCheck 256 1 (x2KeyTypes 1 k111 0) (x2KeyTypes 1 k111 1) (x2KeyTypes 1 k111 2) (x2KeyMult 1 k111 0) (x2KeyMult 1 k111 1) (x2KeyMult 1 k111 2) (x2JCols (x2KeyGlobal 1 k111) d) (gj233.getD d 0) = true := by
  have hr : x2KeySize 1 k111 = 126 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 6 9 9 17 (x2JCols 233 d) (gj233.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 74) ∨ (74 ≤ d ∧ d < 126)) with h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 233 d) (gj233.getD d 0)) 0 74 gjc111_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 233 d) (gj233.getD d 0)) 74 52 gjc111_74 d h.1 (by omega)
x2_v_cols v233 gj233 233 256 1377
theorem vc111_0 : (List.range 45).all (fun c => vCheck 256 1377 126 gj233 (x2Trial_233.getD (0 + c) 0) (v233.getD (0 + c) 0)) = true := by decide +kernel
theorem vc111_45 : (List.range 7).all (fun c => vCheck 256 1377 126 gj233 (x2Trial_233.getD (45 + c) 0) (v233.getD (45 + c) 0)) = true := by decide +kernel
theorem vok111 : ∀ c < 52, vCheck 256 (x2KeyMult 1 k111 0 * x2KeyMult 1 k111 1 * x2KeyMult 1 k111 2) (x2KeySize 1 k111) gj233 (x2Trial_233.getD c 0) (v233.getD c 0) = true := by
  intro c hc
  show vCheck 256 1377 126 gj233 (x2Trial_233.getD c 0) (v233.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 45) ∨ (45 ≤ c ∧ c < 52)) with h | h
  · exact rangeAll_sound (fun c => vCheck 256 1377 126 gj233 (x2Trial_233.getD c 0) (v233.getD c 0)) 0 45 vc111_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1377 126 gj233 (x2Trial_233.getD c 0) (v233.getD c 0)) 45 7 vc111_45 c h.1 (by omega)
theorem small111 : x2KeyDegree 1 k111 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k111 0 ∧ 1 ≤ x2KeyMult 1 k111 1 ∧ 1 ≤ x2KeyMult 1 k111 2 ∧ glRowOK 1 (x2KeyTypes 1 k111 0) (x2KeyMult 1 k111 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k111 1) (x2KeyMult 1 k111 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k111 2) (x2KeyMult 1 k111 2) 512 = true ∧ gj233.length = x2KeySize 1 k111 ∧ x2KeySize 1 k111 ≤ 512 ∧ v233.length = 52 := by decide +kernel
theorem chk111 : trialKeyChk 1 k111 52 gj233 x2Trial_233 v233 :=
  trialKeyChk_intro 1 k111 52 gj233 x2Trial_233 v233 small111 gjok111 vok111
def k112 : x2Key 1 := ⟨112, by decide⟩
x2_gj_cols gj234 234 1 3 3 6 256
theorem gjc112_0 : (List.range 74).all (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 234 (0 + d)) (gj234.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc112_74 : (List.range 28).all (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 234 (74 + d)) (gj234.getD (74 + d) 0)) = true := by decide +kernel
theorem gjok112 : ∀ d < x2KeySize 1 k112, gjCheck 256 1 (x2KeyTypes 1 k112 0) (x2KeyTypes 1 k112 1) (x2KeyTypes 1 k112 2) (x2KeyMult 1 k112 0) (x2KeyMult 1 k112 1) (x2KeyMult 1 k112 2) (x2JCols (x2KeyGlobal 1 k112) d) (gj234.getD d 0) = true := by
  have hr : x2KeySize 1 k112 = 102 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 6 9 9 17 (x2JCols 234 d) (gj234.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 74) ∨ (74 ≤ d ∧ d < 102)) with h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 234 d) (gj234.getD d 0)) 0 74 gjc112_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 3 6 9 9 17 (x2JCols 234 d) (gj234.getD d 0)) 74 28 gjc112_74 d h.1 (by omega)
x2_v_cols v234 gj234 234 256 1377
theorem vc112_0 : (List.range 38).all (fun c => vCheck 256 1377 102 gj234 (x2Trial_234.getD (0 + c) 0) (v234.getD (0 + c) 0)) = true := by decide +kernel
theorem vok112 : ∀ c < 38, vCheck 256 (x2KeyMult 1 k112 0 * x2KeyMult 1 k112 1 * x2KeyMult 1 k112 2) (x2KeySize 1 k112) gj234 (x2Trial_234.getD c 0) (v234.getD c 0) = true := by
  intro c hc
  show vCheck 256 1377 102 gj234 (x2Trial_234.getD c 0) (v234.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1377 102 gj234 (x2Trial_234.getD c 0) (v234.getD c 0)) 0 38 vc112_0 c (Nat.zero_le c) (by omega)
theorem small112 : x2KeyDegree 1 k112 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k112 0 ∧ 1 ≤ x2KeyMult 1 k112 1 ∧ 1 ≤ x2KeyMult 1 k112 2 ∧ glRowOK 1 (x2KeyTypes 1 k112 0) (x2KeyMult 1 k112 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k112 1) (x2KeyMult 1 k112 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k112 2) (x2KeyMult 1 k112 2) 512 = true ∧ gj234.length = x2KeySize 1 k112 ∧ x2KeySize 1 k112 ≤ 512 ∧ v234.length = 38 := by decide +kernel
theorem chk112 : trialKeyChk 1 k112 38 gj234 x2Trial_234 v234 :=
  trialKeyChk_intro 1 k112 38 gj234 x2Trial_234 v234 small112 gjok112 vok112

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k111, ibFS [(v233, v233, 94810963968000)]), (k112, ibFS [(v234, v234, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN111 : N k111 = x2TrialForm 1 k111) (hN112 : N k112 = x2TrialForm 1 k112) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 3 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k111 52 _ gj233 x2Trial_233 v233 (by decide) (by rw [hN111]; exact trialForm_eq 1 k111 52 x2Trial_233 (by decide) rfl) chk111
  · exact keyOK_of_trialChk 1 N k112 38 _ gj234 x2Trial_234 v234 (by decide) (by rw [hN112]; exact trialForm_eq 1 k112 38 x2Trial_234 (by decide) rfl) chk112

end ThreeCopyQutritWerner.X2.InK1x336
