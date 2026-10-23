module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 5, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x355
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k96 : x2Key 2 := ⟨96, by decide⟩
x2_gj_cols gj387 387 2 3 5 5 256
theorem gjc96_0 : (List.range 25).all (fun d => gjCheck 256 2 3 5 5 5 10 10 (x2JCols 387 (0 + d)) (gj387.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok96 : ∀ d < x2KeySize 2 k96, gjCheck 256 2 (x2KeyTypes 2 k96 0) (x2KeyTypes 2 k96 1) (x2KeyTypes 2 k96 2) (x2KeyMult 2 k96 0) (x2KeyMult 2 k96 1) (x2KeyMult 2 k96 2) (x2JCols (x2KeyGlobal 2 k96) d) (gj387.getD d 0) = true := by
  have hr : x2KeySize 2 k96 = 25 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 5 5 5 10 10 (x2JCols 387 d) (gj387.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 5 5 5 10 10 (x2JCols 387 d) (gj387.getD d 0)) 0 25 gjc96_0 d (Nat.zero_le d) (by omega)
x2_v_cols v387 gj387 387 256 500
theorem vc96_0 : (List.range 14).all (fun c => vCheck 256 500 25 gj387 (x2Trial_387.getD (0 + c) 0) (v387.getD (0 + c) 0)) = true := by decide +kernel
theorem vok96 : ∀ c < 14, vCheck 256 (x2KeyMult 2 k96 0 * x2KeyMult 2 k96 1 * x2KeyMult 2 k96 2) (x2KeySize 2 k96) gj387 (x2Trial_387.getD c 0) (v387.getD c 0) = true := by
  intro c hc
  show vCheck 256 500 25 gj387 (x2Trial_387.getD c 0) (v387.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 500 25 gj387 (x2Trial_387.getD c 0) (v387.getD c 0)) 0 14 vc96_0 c (Nat.zero_le c) (by omega)
theorem small96 : x2KeyDegree 2 k96 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k96 0 ∧ 1 ≤ x2KeyMult 2 k96 1 ∧ 1 ≤ x2KeyMult 2 k96 2 ∧ glRowOK 2 (x2KeyTypes 2 k96 0) (x2KeyMult 2 k96 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k96 1) (x2KeyMult 2 k96 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k96 2) (x2KeyMult 2 k96 2) 512 = true ∧ gj387.length = x2KeySize 2 k96 ∧ x2KeySize 2 k96 ≤ 512 ∧ v387.length = 14 := by decide +kernel
theorem chk96 : trialKeyChk 2 k96 14 gj387 x2Trial_387 v387 :=
  trialKeyChk_intro 2 k96 14 gj387 x2Trial_387 v387 small96 gjok96 vok96
def k97 : x2Key 2 := ⟨97, by decide⟩
x2_gj_cols gj388 388 2 3 5 5 256
theorem gjc97_0 : (List.range 19).all (fun d => gjCheck 256 2 3 5 5 5 10 10 (x2JCols 388 (0 + d)) (gj388.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok97 : ∀ d < x2KeySize 2 k97, gjCheck 256 2 (x2KeyTypes 2 k97 0) (x2KeyTypes 2 k97 1) (x2KeyTypes 2 k97 2) (x2KeyMult 2 k97 0) (x2KeyMult 2 k97 1) (x2KeyMult 2 k97 2) (x2JCols (x2KeyGlobal 2 k97) d) (gj388.getD d 0) = true := by
  have hr : x2KeySize 2 k97 = 19 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 5 5 5 10 10 (x2JCols 388 d) (gj388.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 5 5 5 10 10 (x2JCols 388 d) (gj388.getD d 0)) 0 19 gjc97_0 d (Nat.zero_le d) (by omega)
x2_v_cols v388 gj388 388 256 500
theorem vc97_0 : (List.range 13).all (fun c => vCheck 256 500 19 gj388 (x2Trial_388.getD (0 + c) 0) (v388.getD (0 + c) 0)) = true := by decide +kernel
theorem vok97 : ∀ c < 13, vCheck 256 (x2KeyMult 2 k97 0 * x2KeyMult 2 k97 1 * x2KeyMult 2 k97 2) (x2KeySize 2 k97) gj388 (x2Trial_388.getD c 0) (v388.getD c 0) = true := by
  intro c hc
  show vCheck 256 500 19 gj388 (x2Trial_388.getD c 0) (v388.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 500 19 gj388 (x2Trial_388.getD c 0) (v388.getD c 0)) 0 13 vc97_0 c (Nat.zero_le c) (by omega)
theorem small97 : x2KeyDegree 2 k97 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k97 0 ∧ 1 ≤ x2KeyMult 2 k97 1 ∧ 1 ≤ x2KeyMult 2 k97 2 ∧ glRowOK 2 (x2KeyTypes 2 k97 0) (x2KeyMult 2 k97 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k97 1) (x2KeyMult 2 k97 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k97 2) (x2KeyMult 2 k97 2) 512 = true ∧ gj388.length = x2KeySize 2 k97 ∧ x2KeySize 2 k97 ≤ 512 ∧ v388.length = 13 := by decide +kernel
theorem chk97 : trialKeyChk 2 k97 13 gj388 x2Trial_388 v388 :=
  trialKeyChk_intro 2 k97 13 gj388 x2Trial_388 v388 small97 gjok97 vok97

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k96, ibFS [(v387, v387, 94810963968000)]), (k97, ibFS [(v388, v388, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN96 : N k96 = x2TrialForm 2 k96) (hN97 : N k97 = x2TrialForm 2 k97) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 5 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k96 14 _ gj387 x2Trial_387 v387 (by decide) (by rw [hN96]; exact trialForm_eq 2 k96 14 x2Trial_387 (by decide) rfl) chk96
  · exact keyOK_of_trialChk 2 N k97 13 _ gj388 x2Trial_388 v388 (by decide) (by rw [hN97]; exact trialForm_eq 2 k97 13 x2Trial_388 (by decide) rfl) chk97

end ThreeCopyQutritWerner.X2.InK2x355
