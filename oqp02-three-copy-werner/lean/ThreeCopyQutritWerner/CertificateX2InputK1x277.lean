module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x277
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k102 : x2Key 1 := ⟨102, by decide⟩
x2_gj_cols gj224 224 1 2 7 7 256
theorem gjc102_0 : (List.range 6).all (fun d => gjCheck 256 1 2 7 7 2 6 6 (x2JCols 224 (0 + d)) (gj224.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok102 : ∀ d < x2KeySize 1 k102, gjCheck 256 1 (x2KeyTypes 1 k102 0) (x2KeyTypes 1 k102 1) (x2KeyTypes 1 k102 2) (x2KeyMult 1 k102 0) (x2KeyMult 1 k102 1) (x2KeyMult 1 k102 2) (x2JCols (x2KeyGlobal 1 k102) d) (gj224.getD d 0) = true := by
  have hr : x2KeySize 1 k102 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 7 7 2 6 6 (x2JCols 224 d) (gj224.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 7 7 2 6 6 (x2JCols 224 d) (gj224.getD d 0)) 0 6 gjc102_0 d (Nat.zero_le d) (by omega)
x2_v_cols v224 gj224 224 256 72
theorem vc102_0 : (List.range 3).all (fun c => vCheck 256 72 6 gj224 (x2Trial_224.getD (0 + c) 0) (v224.getD (0 + c) 0)) = true := by decide +kernel
theorem vok102 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k102 0 * x2KeyMult 1 k102 1 * x2KeyMult 1 k102 2) (x2KeySize 1 k102) gj224 (x2Trial_224.getD c 0) (v224.getD c 0) = true := by
  intro c hc
  show vCheck 256 72 6 gj224 (x2Trial_224.getD c 0) (v224.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 72 6 gj224 (x2Trial_224.getD c 0) (v224.getD c 0)) 0 3 vc102_0 c (Nat.zero_le c) (by omega)
theorem small102 : x2KeyDegree 1 k102 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k102 0 ∧ 1 ≤ x2KeyMult 1 k102 1 ∧ 1 ≤ x2KeyMult 1 k102 2 ∧ glRowOK 1 (x2KeyTypes 1 k102 0) (x2KeyMult 1 k102 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k102 1) (x2KeyMult 1 k102 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k102 2) (x2KeyMult 1 k102 2) 512 = true ∧ gj224.length = x2KeySize 1 k102 ∧ x2KeySize 1 k102 ≤ 512 ∧ v224.length = 3 := by decide +kernel
theorem chk102 : trialKeyChk 1 k102 3 gj224 x2Trial_224 v224 :=
  trialKeyChk_intro 1 k102 3 gj224 x2Trial_224 v224 small102 gjok102 vok102
def k103 : x2Key 1 := ⟨103, by decide⟩
x2_gj_cols gj225 225 1 2 7 7 256
theorem gjc103_0 : (List.range 6).all (fun d => gjCheck 256 1 2 7 7 2 6 6 (x2JCols 225 (0 + d)) (gj225.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok103 : ∀ d < x2KeySize 1 k103, gjCheck 256 1 (x2KeyTypes 1 k103 0) (x2KeyTypes 1 k103 1) (x2KeyTypes 1 k103 2) (x2KeyMult 1 k103 0) (x2KeyMult 1 k103 1) (x2KeyMult 1 k103 2) (x2JCols (x2KeyGlobal 1 k103) d) (gj225.getD d 0) = true := by
  have hr : x2KeySize 1 k103 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 7 7 2 6 6 (x2JCols 225 d) (gj225.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 7 7 2 6 6 (x2JCols 225 d) (gj225.getD d 0)) 0 6 gjc103_0 d (Nat.zero_le d) (by omega)
x2_v_cols v225 gj225 225 256 72
theorem vc103_0 : (List.range 3).all (fun c => vCheck 256 72 6 gj225 (x2Trial_225.getD (0 + c) 0) (v225.getD (0 + c) 0)) = true := by decide +kernel
theorem vok103 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k103 0 * x2KeyMult 1 k103 1 * x2KeyMult 1 k103 2) (x2KeySize 1 k103) gj225 (x2Trial_225.getD c 0) (v225.getD c 0) = true := by
  intro c hc
  show vCheck 256 72 6 gj225 (x2Trial_225.getD c 0) (v225.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 72 6 gj225 (x2Trial_225.getD c 0) (v225.getD c 0)) 0 3 vc103_0 c (Nat.zero_le c) (by omega)
theorem small103 : x2KeyDegree 1 k103 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k103 0 ∧ 1 ≤ x2KeyMult 1 k103 1 ∧ 1 ≤ x2KeyMult 1 k103 2 ∧ glRowOK 1 (x2KeyTypes 1 k103 0) (x2KeyMult 1 k103 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k103 1) (x2KeyMult 1 k103 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k103 2) (x2KeyMult 1 k103 2) 512 = true ∧ gj225.length = x2KeySize 1 k103 ∧ x2KeySize 1 k103 ≤ 512 ∧ v225.length = 3 := by decide +kernel
theorem chk103 : trialKeyChk 1 k103 3 gj225 x2Trial_225 v225 :=
  trialKeyChk_intro 1 k103 3 gj225 x2Trial_225 v225 small103 gjok103 vok103

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k102, ibFS [(v224, v224, 94810963968000)]), (k103, ibFS [(v225, v225, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN102 : N k102 = x2TrialForm 1 k102) (hN103 : N k103 = x2TrialForm 1 k103) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k102 3 _ gj224 x2Trial_224 v224 (by decide) (by rw [hN102]; exact trialForm_eq 1 k102 3 x2Trial_224 (by decide) rfl) chk102
  · exact keyOK_of_trialChk 1 N k103 3 _ gj225 x2Trial_225 v225 (by decide) (by rw [hN103]; exact trialForm_eq 1 k103 3 x2Trial_225 (by decide) rfl) chk103

end ThreeCopyQutritWerner.X2.InK1x277
