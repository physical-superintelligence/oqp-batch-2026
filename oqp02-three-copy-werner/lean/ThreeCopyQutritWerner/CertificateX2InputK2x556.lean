module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 5, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x556
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k116 : x2Key 2 := ⟨116, by decide⟩
x2_gj_cols gj407 407 2 5 5 6 256
theorem gjc116_0 : (List.range 49).all (fun d => gjCheck 256 2 5 5 6 10 10 11 (x2JCols 407 (0 + d)) (gj407.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok116 : ∀ d < x2KeySize 2 k116, gjCheck 256 2 (x2KeyTypes 2 k116 0) (x2KeyTypes 2 k116 1) (x2KeyTypes 2 k116 2) (x2KeyMult 2 k116 0) (x2KeyMult 2 k116 1) (x2KeyMult 2 k116 2) (x2JCols (x2KeyGlobal 2 k116) d) (gj407.getD d 0) = true := by
  have hr : x2KeySize 2 k116 = 49 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 5 6 10 10 11 (x2JCols 407 d) (gj407.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 5 6 10 10 11 (x2JCols 407 d) (gj407.getD d 0)) 0 49 gjc116_0 d (Nat.zero_le d) (by omega)
x2_v_cols v407 gj407 407 256 1100
theorem vc116_0 : (List.range 44).all (fun c => vCheck 256 1100 49 gj407 (x2Trial_407.getD (0 + c) 0) (v407.getD (0 + c) 0)) = true := by decide +kernel
theorem vok116 : ∀ c < 44, vCheck 256 (x2KeyMult 2 k116 0 * x2KeyMult 2 k116 1 * x2KeyMult 2 k116 2) (x2KeySize 2 k116) gj407 (x2Trial_407.getD c 0) (v407.getD c 0) = true := by
  intro c hc
  show vCheck 256 1100 49 gj407 (x2Trial_407.getD c 0) (v407.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1100 49 gj407 (x2Trial_407.getD c 0) (v407.getD c 0)) 0 44 vc116_0 c (Nat.zero_le c) (by omega)
theorem small116 : x2KeyDegree 2 k116 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k116 0 ∧ 1 ≤ x2KeyMult 2 k116 1 ∧ 1 ≤ x2KeyMult 2 k116 2 ∧ glRowOK 2 (x2KeyTypes 2 k116 0) (x2KeyMult 2 k116 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k116 1) (x2KeyMult 2 k116 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k116 2) (x2KeyMult 2 k116 2) 512 = true ∧ gj407.length = x2KeySize 2 k116 ∧ x2KeySize 2 k116 ≤ 512 ∧ v407.length = 44 := by decide +kernel
theorem chk116 : trialKeyChk 2 k116 44 gj407 x2Trial_407 v407 :=
  trialKeyChk_intro 2 k116 44 gj407 x2Trial_407 v407 small116 gjok116 vok116
def k117 : x2Key 2 := ⟨117, by decide⟩
x2_gj_cols gj408 408 2 5 5 6 256
theorem gjc117_0 : (List.range 43).all (fun d => gjCheck 256 2 5 5 6 10 10 11 (x2JCols 408 (0 + d)) (gj408.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok117 : ∀ d < x2KeySize 2 k117, gjCheck 256 2 (x2KeyTypes 2 k117 0) (x2KeyTypes 2 k117 1) (x2KeyTypes 2 k117 2) (x2KeyMult 2 k117 0) (x2KeyMult 2 k117 1) (x2KeyMult 2 k117 2) (x2JCols (x2KeyGlobal 2 k117) d) (gj408.getD d 0) = true := by
  have hr : x2KeySize 2 k117 = 43 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 5 6 10 10 11 (x2JCols 408 d) (gj408.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 5 6 10 10 11 (x2JCols 408 d) (gj408.getD d 0)) 0 43 gjc117_0 d (Nat.zero_le d) (by omega)
x2_v_cols v408 gj408 408 256 1100
theorem vc117_0 : (List.range 38).all (fun c => vCheck 256 1100 43 gj408 (x2Trial_408.getD (0 + c) 0) (v408.getD (0 + c) 0)) = true := by decide +kernel
theorem vok117 : ∀ c < 38, vCheck 256 (x2KeyMult 2 k117 0 * x2KeyMult 2 k117 1 * x2KeyMult 2 k117 2) (x2KeySize 2 k117) gj408 (x2Trial_408.getD c 0) (v408.getD c 0) = true := by
  intro c hc
  show vCheck 256 1100 43 gj408 (x2Trial_408.getD c 0) (v408.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1100 43 gj408 (x2Trial_408.getD c 0) (v408.getD c 0)) 0 38 vc117_0 c (Nat.zero_le c) (by omega)
theorem small117 : x2KeyDegree 2 k117 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k117 0 ∧ 1 ≤ x2KeyMult 2 k117 1 ∧ 1 ≤ x2KeyMult 2 k117 2 ∧ glRowOK 2 (x2KeyTypes 2 k117 0) (x2KeyMult 2 k117 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k117 1) (x2KeyMult 2 k117 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k117 2) (x2KeyMult 2 k117 2) 512 = true ∧ gj408.length = x2KeySize 2 k117 ∧ x2KeySize 2 k117 ≤ 512 ∧ v408.length = 38 := by decide +kernel
theorem chk117 : trialKeyChk 2 k117 38 gj408 x2Trial_408 v408 :=
  trialKeyChk_intro 2 k117 38 gj408 x2Trial_408 v408 small117 gjok117 vok117

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k116, ibFS [(v407, v407, 94810963968000)]), (k117, ibFS [(v408, v408, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![5, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN116 : N k116 = x2TrialForm 2 k116) (hN117 : N k117 = x2TrialForm 2 k117) :
    ∀ e ∈ ks, keyOK (x2Mult 2 5 * x2Mult 2 5 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k116 44 _ gj407 x2Trial_407 v407 (by decide) (by rw [hN116]; exact trialForm_eq 2 k116 44 x2Trial_407 (by decide) rfl) chk116
  · exact keyOK_of_trialChk 2 N k117 38 _ gj408 x2Trial_408 v408 (by decide) (by rw [hN117]; exact trialForm_eq 2 k117 38 x2Trial_408 (by decide) rfl) chk117

end ThreeCopyQutritWerner.X2.InK2x556
