module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x034
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k18 : x2Key 1 := ⟨18, by decide⟩
x2_gj_cols gj140 140 1 0 3 4 256
theorem gjc18_0 : (List.range 11).all (fun d => gjCheck 256 1 0 3 4 1 9 7 (x2JCols 140 (0 + d)) (gj140.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok18 : ∀ d < x2KeySize 1 k18, gjCheck 256 1 (x2KeyTypes 1 k18 0) (x2KeyTypes 1 k18 1) (x2KeyTypes 1 k18 2) (x2KeyMult 1 k18 0) (x2KeyMult 1 k18 1) (x2KeyMult 1 k18 2) (x2JCols (x2KeyGlobal 1 k18) d) (gj140.getD d 0) = true := by
  have hr : x2KeySize 1 k18 = 11 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 3 4 1 9 7 (x2JCols 140 d) (gj140.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 3 4 1 9 7 (x2JCols 140 d) (gj140.getD d 0)) 0 11 gjc18_0 d (Nat.zero_le d) (by omega)
x2_v_cols v140 gj140 140 256 63
theorem vc18_0 : (List.range 2).all (fun c => vCheck 256 63 11 gj140 (x2Trial_140.getD (0 + c) 0) (v140.getD (0 + c) 0)) = true := by decide +kernel
theorem vok18 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k18 0 * x2KeyMult 1 k18 1 * x2KeyMult 1 k18 2) (x2KeySize 1 k18) gj140 (x2Trial_140.getD c 0) (v140.getD c 0) = true := by
  intro c hc
  show vCheck 256 63 11 gj140 (x2Trial_140.getD c 0) (v140.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 63 11 gj140 (x2Trial_140.getD c 0) (v140.getD c 0)) 0 2 vc18_0 c (Nat.zero_le c) (by omega)
theorem small18 : x2KeyDegree 1 k18 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k18 0 ∧ 1 ≤ x2KeyMult 1 k18 1 ∧ 1 ≤ x2KeyMult 1 k18 2 ∧ glRowOK 1 (x2KeyTypes 1 k18 0) (x2KeyMult 1 k18 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k18 1) (x2KeyMult 1 k18 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k18 2) (x2KeyMult 1 k18 2) 512 = true ∧ gj140.length = x2KeySize 1 k18 ∧ x2KeySize 1 k18 ≤ 512 ∧ v140.length = 2 := by decide +kernel
theorem chk18 : trialKeyChk 1 k18 2 gj140 x2Trial_140 v140 :=
  trialKeyChk_intro 1 k18 2 gj140 x2Trial_140 v140 small18 gjok18 vok18

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k18, ibFS [(v140, v140, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN18 : N k18 = x2TrialForm 1 k18) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 3 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k18 2 _ gj140 x2Trial_140 v140 (by decide) (by rw [hN18]; exact trialForm_eq 1 k18 2 x2Trial_140 (by decide) rfl) chk18

end ThreeCopyQutritWerner.X2.InK1x034
