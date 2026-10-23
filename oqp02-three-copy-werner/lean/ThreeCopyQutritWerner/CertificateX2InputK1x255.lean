module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 5, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x255
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k95 : x2Key 1 := ⟨95, by decide⟩
x2_gj_cols gj217 217 1 2 5 5 256
theorem gjc95_0 : (List.range 7).all (fun d => gjCheck 256 1 2 5 5 2 7 7 (x2JCols 217 (0 + d)) (gj217.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok95 : ∀ d < x2KeySize 1 k95, gjCheck 256 1 (x2KeyTypes 1 k95 0) (x2KeyTypes 1 k95 1) (x2KeyTypes 1 k95 2) (x2KeyMult 1 k95 0) (x2KeyMult 1 k95 1) (x2KeyMult 1 k95 2) (x2JCols (x2KeyGlobal 1 k95) d) (gj217.getD d 0) = true := by
  have hr : x2KeySize 1 k95 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 5 5 2 7 7 (x2JCols 217 d) (gj217.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 5 5 2 7 7 (x2JCols 217 d) (gj217.getD d 0)) 0 7 gjc95_0 d (Nat.zero_le d) (by omega)
x2_v_cols v217 gj217 217 256 98
theorem vc95_0 : (List.range 2).all (fun c => vCheck 256 98 7 gj217 (x2Trial_217.getD (0 + c) 0) (v217.getD (0 + c) 0)) = true := by decide +kernel
theorem vok95 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k95 0 * x2KeyMult 1 k95 1 * x2KeyMult 1 k95 2) (x2KeySize 1 k95) gj217 (x2Trial_217.getD c 0) (v217.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 7 gj217 (x2Trial_217.getD c 0) (v217.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 7 gj217 (x2Trial_217.getD c 0) (v217.getD c 0)) 0 2 vc95_0 c (Nat.zero_le c) (by omega)
theorem small95 : x2KeyDegree 1 k95 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k95 0 ∧ 1 ≤ x2KeyMult 1 k95 1 ∧ 1 ≤ x2KeyMult 1 k95 2 ∧ glRowOK 1 (x2KeyTypes 1 k95 0) (x2KeyMult 1 k95 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k95 1) (x2KeyMult 1 k95 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k95 2) (x2KeyMult 1 k95 2) 512 = true ∧ gj217.length = x2KeySize 1 k95 ∧ x2KeySize 1 k95 ≤ 512 ∧ v217.length = 2 := by decide +kernel
theorem chk95 : trialKeyChk 1 k95 2 gj217 x2Trial_217 v217 :=
  trialKeyChk_intro 1 k95 2 gj217 x2Trial_217 v217 small95 gjok95 vok95
def k96 : x2Key 1 := ⟨96, by decide⟩
x2_gj_cols gj218 218 1 2 5 5 256
theorem gjc96_0 : (List.range 7).all (fun d => gjCheck 256 1 2 5 5 2 7 7 (x2JCols 218 (0 + d)) (gj218.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok96 : ∀ d < x2KeySize 1 k96, gjCheck 256 1 (x2KeyTypes 1 k96 0) (x2KeyTypes 1 k96 1) (x2KeyTypes 1 k96 2) (x2KeyMult 1 k96 0) (x2KeyMult 1 k96 1) (x2KeyMult 1 k96 2) (x2JCols (x2KeyGlobal 1 k96) d) (gj218.getD d 0) = true := by
  have hr : x2KeySize 1 k96 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 5 5 2 7 7 (x2JCols 218 d) (gj218.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 5 5 2 7 7 (x2JCols 218 d) (gj218.getD d 0)) 0 7 gjc96_0 d (Nat.zero_le d) (by omega)
x2_v_cols v218 gj218 218 256 98
theorem vc96_0 : (List.range 2).all (fun c => vCheck 256 98 7 gj218 (x2Trial_218.getD (0 + c) 0) (v218.getD (0 + c) 0)) = true := by decide +kernel
theorem vok96 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k96 0 * x2KeyMult 1 k96 1 * x2KeyMult 1 k96 2) (x2KeySize 1 k96) gj218 (x2Trial_218.getD c 0) (v218.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 7 gj218 (x2Trial_218.getD c 0) (v218.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 7 gj218 (x2Trial_218.getD c 0) (v218.getD c 0)) 0 2 vc96_0 c (Nat.zero_le c) (by omega)
theorem small96 : x2KeyDegree 1 k96 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k96 0 ∧ 1 ≤ x2KeyMult 1 k96 1 ∧ 1 ≤ x2KeyMult 1 k96 2 ∧ glRowOK 1 (x2KeyTypes 1 k96 0) (x2KeyMult 1 k96 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k96 1) (x2KeyMult 1 k96 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k96 2) (x2KeyMult 1 k96 2) 512 = true ∧ gj218.length = x2KeySize 1 k96 ∧ x2KeySize 1 k96 ≤ 512 ∧ v218.length = 2 := by decide +kernel
theorem chk96 : trialKeyChk 1 k96 2 gj218 x2Trial_218 v218 :=
  trialKeyChk_intro 1 k96 2 gj218 x2Trial_218 v218 small96 gjok96 vok96

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k95, ibFS [(v217, v217, 94810963968000)]), (k96, ibFS [(v218, v218, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN95 : N k95 = x2TrialForm 1 k95) (hN96 : N k96 = x2TrialForm 1 k96) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 5 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k95 2 _ gj217 x2Trial_217 v217 (by decide) (by rw [hN95]; exact trialForm_eq 1 k95 2 x2Trial_217 (by decide) rfl) chk95
  · exact keyOK_of_trialChk 1 N k96 2 _ gj218 x2Trial_218 v218 (by decide) (by rw [hN96]; exact trialForm_eq 1 k96 2 x2Trial_218 (by decide) rfl) chk96

end ThreeCopyQutritWerner.X2.InK1x255
