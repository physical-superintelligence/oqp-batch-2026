module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x566
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k118 : x2Key 2 := ⟨118, by decide⟩
x2_gj_cols gj409 409 2 5 6 6 256
theorem gjc118_0 : (List.range 58).all (fun d => gjCheck 256 2 5 6 6 10 11 11 (x2JCols 409 (0 + d)) (gj409.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok118 : ∀ d < x2KeySize 2 k118, gjCheck 256 2 (x2KeyTypes 2 k118 0) (x2KeyTypes 2 k118 1) (x2KeyTypes 2 k118 2) (x2KeyMult 2 k118 0) (x2KeyMult 2 k118 1) (x2KeyMult 2 k118 2) (x2JCols (x2KeyGlobal 2 k118) d) (gj409.getD d 0) = true := by
  have hr : x2KeySize 2 k118 = 58 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 6 6 10 11 11 (x2JCols 409 d) (gj409.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 6 6 10 11 11 (x2JCols 409 d) (gj409.getD d 0)) 0 58 gjc118_0 d (Nat.zero_le d) (by omega)
x2_v_cols v409 gj409 409 256 1210
theorem vc118_0 : (List.range 53).all (fun c => vCheck 256 1210 58 gj409 (x2Trial_409.getD (0 + c) 0) (v409.getD (0 + c) 0)) = true := by decide +kernel
theorem vok118 : ∀ c < 53, vCheck 256 (x2KeyMult 2 k118 0 * x2KeyMult 2 k118 1 * x2KeyMult 2 k118 2) (x2KeySize 2 k118) gj409 (x2Trial_409.getD c 0) (v409.getD c 0) = true := by
  intro c hc
  show vCheck 256 1210 58 gj409 (x2Trial_409.getD c 0) (v409.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1210 58 gj409 (x2Trial_409.getD c 0) (v409.getD c 0)) 0 53 vc118_0 c (Nat.zero_le c) (by omega)
theorem small118 : x2KeyDegree 2 k118 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k118 0 ∧ 1 ≤ x2KeyMult 2 k118 1 ∧ 1 ≤ x2KeyMult 2 k118 2 ∧ glRowOK 2 (x2KeyTypes 2 k118 0) (x2KeyMult 2 k118 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k118 1) (x2KeyMult 2 k118 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k118 2) (x2KeyMult 2 k118 2) 512 = true ∧ gj409.length = x2KeySize 2 k118 ∧ x2KeySize 2 k118 ≤ 512 ∧ v409.length = 53 := by decide +kernel
theorem chk118 : trialKeyChk 2 k118 53 gj409 x2Trial_409 v409 :=
  trialKeyChk_intro 2 k118 53 gj409 x2Trial_409 v409 small118 gjok118 vok118
def k119 : x2Key 2 := ⟨119, by decide⟩
x2_gj_cols gj410 410 2 5 6 6 256
theorem gjc119_0 : (List.range 44).all (fun d => gjCheck 256 2 5 6 6 10 11 11 (x2JCols 410 (0 + d)) (gj410.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok119 : ∀ d < x2KeySize 2 k119, gjCheck 256 2 (x2KeyTypes 2 k119 0) (x2KeyTypes 2 k119 1) (x2KeyTypes 2 k119 2) (x2KeyMult 2 k119 0) (x2KeyMult 2 k119 1) (x2KeyMult 2 k119 2) (x2JCols (x2KeyGlobal 2 k119) d) (gj410.getD d 0) = true := by
  have hr : x2KeySize 2 k119 = 44 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 5 6 6 10 11 11 (x2JCols 410 d) (gj410.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 5 6 6 10 11 11 (x2JCols 410 d) (gj410.getD d 0)) 0 44 gjc119_0 d (Nat.zero_le d) (by omega)
x2_v_cols v410 gj410 410 256 1210
theorem vc119_0 : (List.range 43).all (fun c => vCheck 256 1210 44 gj410 (x2Trial_410.getD (0 + c) 0) (v410.getD (0 + c) 0)) = true := by decide +kernel
theorem vok119 : ∀ c < 43, vCheck 256 (x2KeyMult 2 k119 0 * x2KeyMult 2 k119 1 * x2KeyMult 2 k119 2) (x2KeySize 2 k119) gj410 (x2Trial_410.getD c 0) (v410.getD c 0) = true := by
  intro c hc
  show vCheck 256 1210 44 gj410 (x2Trial_410.getD c 0) (v410.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1210 44 gj410 (x2Trial_410.getD c 0) (v410.getD c 0)) 0 43 vc119_0 c (Nat.zero_le c) (by omega)
theorem small119 : x2KeyDegree 2 k119 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k119 0 ∧ 1 ≤ x2KeyMult 2 k119 1 ∧ 1 ≤ x2KeyMult 2 k119 2 ∧ glRowOK 2 (x2KeyTypes 2 k119 0) (x2KeyMult 2 k119 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k119 1) (x2KeyMult 2 k119 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k119 2) (x2KeyMult 2 k119 2) 512 = true ∧ gj410.length = x2KeySize 2 k119 ∧ x2KeySize 2 k119 ≤ 512 ∧ v410.length = 43 := by decide +kernel
theorem chk119 : trialKeyChk 2 k119 43 gj410 x2Trial_410 v410 :=
  trialKeyChk_intro 2 k119 43 gj410 x2Trial_410 v410 small119 gjok119 vok119

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k118, ibFS [(v409, v409, 94810963968000)]), (k119, ibFS [(v410, v410, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![5, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN118 : N k118 = x2TrialForm 2 k118) (hN119 : N k119 = x2TrialForm 2 k119) :
    ∀ e ∈ ks, keyOK (x2Mult 2 5 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k118 53 _ gj409 x2Trial_409 v409 (by decide) (by rw [hN118]; exact trialForm_eq 2 k118 53 x2Trial_409 (by decide) rfl) chk118
  · exact keyOK_of_trialChk 2 N k119 43 _ gj410 x2Trial_410 v410 (by decide) (by rw [hN119]; exact trialForm_eq 2 k119 43 x2Trial_410 (by decide) rfl) chk119

end ThreeCopyQutritWerner.X2.InK2x566
