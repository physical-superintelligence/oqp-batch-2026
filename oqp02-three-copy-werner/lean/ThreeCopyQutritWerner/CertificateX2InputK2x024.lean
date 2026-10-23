module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 2, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x024
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k12 : x2Key 2 := ⟨12, by decide⟩
x2_gj_cols gj303 303 2 0 2 4 256
theorem gjc12_0 : (List.range 6).all (fun d => gjCheck 256 2 0 2 4 1 5 15 (x2JCols 303 (0 + d)) (gj303.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok12 : ∀ d < x2KeySize 2 k12, gjCheck 256 2 (x2KeyTypes 2 k12 0) (x2KeyTypes 2 k12 1) (x2KeyTypes 2 k12 2) (x2KeyMult 2 k12 0) (x2KeyMult 2 k12 1) (x2KeyMult 2 k12 2) (x2JCols (x2KeyGlobal 2 k12) d) (gj303.getD d 0) = true := by
  have hr : x2KeySize 2 k12 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 2 4 1 5 15 (x2JCols 303 d) (gj303.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 2 4 1 5 15 (x2JCols 303 d) (gj303.getD d 0)) 0 6 gjc12_0 d (Nat.zero_le d) (by omega)
x2_v_cols v303 gj303 303 256 75
theorem vc12_0 : (List.range 2).all (fun c => vCheck 256 75 6 gj303 (x2Trial_303.getD (0 + c) 0) (v303.getD (0 + c) 0)) = true := by decide +kernel
theorem vok12 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k12 0 * x2KeyMult 2 k12 1 * x2KeyMult 2 k12 2) (x2KeySize 2 k12) gj303 (x2Trial_303.getD c 0) (v303.getD c 0) = true := by
  intro c hc
  show vCheck 256 75 6 gj303 (x2Trial_303.getD c 0) (v303.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 75 6 gj303 (x2Trial_303.getD c 0) (v303.getD c 0)) 0 2 vc12_0 c (Nat.zero_le c) (by omega)
theorem small12 : x2KeyDegree 2 k12 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k12 0 ∧ 1 ≤ x2KeyMult 2 k12 1 ∧ 1 ≤ x2KeyMult 2 k12 2 ∧ glRowOK 2 (x2KeyTypes 2 k12 0) (x2KeyMult 2 k12 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k12 1) (x2KeyMult 2 k12 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k12 2) (x2KeyMult 2 k12 2) 512 = true ∧ gj303.length = x2KeySize 2 k12 ∧ x2KeySize 2 k12 ≤ 512 ∧ v303.length = 2 := by decide +kernel
theorem chk12 : trialKeyChk 2 k12 2 gj303 x2Trial_303 v303 :=
  trialKeyChk_intro 2 k12 2 gj303 x2Trial_303 v303 small12 gjok12 vok12

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k12, ibFS [(v303, v303, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 2, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN12 : N k12 = x2TrialForm 2 k12) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 2 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k12 2 _ gj303 x2Trial_303 v303 (by decide) (by rw [hN12]; exact trialForm_eq 2 k12 2 x2Trial_303 (by decide) rfl) chk12

end ThreeCopyQutritWerner.X2.InK2x024
