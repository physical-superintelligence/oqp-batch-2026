module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x036
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k18 : x2Key 2 := ⟨18, by decide⟩
x2_gj_cols gj309 309 2 0 3 6 256
theorem gjc18_0 : (List.range 4).all (fun d => gjCheck 256 2 0 3 6 1 5 11 (x2JCols 309 (0 + d)) (gj309.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok18 : ∀ d < x2KeySize 2 k18, gjCheck 256 2 (x2KeyTypes 2 k18 0) (x2KeyTypes 2 k18 1) (x2KeyTypes 2 k18 2) (x2KeyMult 2 k18 0) (x2KeyMult 2 k18 1) (x2KeyMult 2 k18 2) (x2JCols (x2KeyGlobal 2 k18) d) (gj309.getD d 0) = true := by
  have hr : x2KeySize 2 k18 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 3 6 1 5 11 (x2JCols 309 d) (gj309.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 3 6 1 5 11 (x2JCols 309 d) (gj309.getD d 0)) 0 4 gjc18_0 d (Nat.zero_le d) (by omega)
x2_v_cols v309 gj309 309 256 55
theorem vc18_0 : (List.range 4).all (fun c => vCheck 256 55 4 gj309 (x2Trial_309.getD (0 + c) 0) (v309.getD (0 + c) 0)) = true := by decide +kernel
theorem vok18 : ∀ c < 4, vCheck 256 (x2KeyMult 2 k18 0 * x2KeyMult 2 k18 1 * x2KeyMult 2 k18 2) (x2KeySize 2 k18) gj309 (x2Trial_309.getD c 0) (v309.getD c 0) = true := by
  intro c hc
  show vCheck 256 55 4 gj309 (x2Trial_309.getD c 0) (v309.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 55 4 gj309 (x2Trial_309.getD c 0) (v309.getD c 0)) 0 4 vc18_0 c (Nat.zero_le c) (by omega)
theorem small18 : x2KeyDegree 2 k18 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k18 0 ∧ 1 ≤ x2KeyMult 2 k18 1 ∧ 1 ≤ x2KeyMult 2 k18 2 ∧ glRowOK 2 (x2KeyTypes 2 k18 0) (x2KeyMult 2 k18 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k18 1) (x2KeyMult 2 k18 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k18 2) (x2KeyMult 2 k18 2) 512 = true ∧ gj309.length = x2KeySize 2 k18 ∧ x2KeySize 2 k18 ≤ 512 ∧ v309.length = 4 := by decide +kernel
theorem chk18 : trialKeyChk 2 k18 4 gj309 x2Trial_309 v309 :=
  trialKeyChk_intro 2 k18 4 gj309 x2Trial_309 v309 small18 gjok18 vok18

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k18, ibFS [(v309, v309, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN18 : N k18 = x2TrialForm 2 k18) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 3 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k18 4 _ gj309 x2Trial_309 v309 (by decide) (by rw [hN18]; exact trialForm_eq 2 k18 4 x2Trial_309 (by decide) rfl) chk18

end ThreeCopyQutritWerner.X2.InK2x036
