module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x227
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k82 : x2Key 1 := ⟨82, by decide⟩
x2_gj_cols gj204 204 1 2 2 7 256
theorem gjc82_0 : (List.range 3).all (fun d => gjCheck 256 1 2 2 7 2 2 6 (x2JCols 204 (0 + d)) (gj204.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok82 : ∀ d < x2KeySize 1 k82, gjCheck 256 1 (x2KeyTypes 1 k82 0) (x2KeyTypes 1 k82 1) (x2KeyTypes 1 k82 2) (x2KeyMult 1 k82 0) (x2KeyMult 1 k82 1) (x2KeyMult 1 k82 2) (x2JCols (x2KeyGlobal 1 k82) d) (gj204.getD d 0) = true := by
  have hr : x2KeySize 1 k82 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 2 7 2 2 6 (x2JCols 204 d) (gj204.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 2 7 2 2 6 (x2JCols 204 d) (gj204.getD d 0)) 0 3 gjc82_0 d (Nat.zero_le d) (by omega)
x2_v_cols v204 gj204 204 256 24
theorem vc82_0 : (List.range 1).all (fun c => vCheck 256 24 3 gj204 (x2Trial_204.getD (0 + c) 0) (v204.getD (0 + c) 0)) = true := by decide +kernel
theorem vok82 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k82 0 * x2KeyMult 1 k82 1 * x2KeyMult 1 k82 2) (x2KeySize 1 k82) gj204 (x2Trial_204.getD c 0) (v204.getD c 0) = true := by
  intro c hc
  show vCheck 256 24 3 gj204 (x2Trial_204.getD c 0) (v204.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 24 3 gj204 (x2Trial_204.getD c 0) (v204.getD c 0)) 0 1 vc82_0 c (Nat.zero_le c) (by omega)
theorem small82 : x2KeyDegree 1 k82 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k82 0 ∧ 1 ≤ x2KeyMult 1 k82 1 ∧ 1 ≤ x2KeyMult 1 k82 2 ∧ glRowOK 1 (x2KeyTypes 1 k82 0) (x2KeyMult 1 k82 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k82 1) (x2KeyMult 1 k82 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k82 2) (x2KeyMult 1 k82 2) 512 = true ∧ gj204.length = x2KeySize 1 k82 ∧ x2KeySize 1 k82 ≤ 512 ∧ v204.length = 1 := by decide +kernel
theorem chk82 : trialKeyChk 1 k82 1 gj204 x2Trial_204 v204 :=
  trialKeyChk_intro 1 k82 1 gj204 x2Trial_204 v204 small82 gjok82 vok82
def k83 : x2Key 1 := ⟨83, by decide⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k82, ibFS [(v204, v204, 94810963968000)]), (k83, [])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 2, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN82 : N k82 = x2TrialForm 1 k82) (hN83 : N k83 = x2TrialForm 1 k83) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 2 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k82 1 _ gj204 x2Trial_204 v204 (by decide) (by rw [hN82]; exact trialForm_eq 1 k82 1 x2Trial_204 (by decide) rfl) chk82
  · exact keyOK_of_zeroBlock _ 1 N k83 (by rw [hN83]; exact trialForm_zero 1 k83 (by decide))

end ThreeCopyQutritWerner.X2.InK1x227
