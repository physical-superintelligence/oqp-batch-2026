module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x247
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k94 : x2Key 1 := ⟨94, by decide⟩
x2_gj_cols gj216 216 1 2 4 7 256
theorem gjc94_0 : (List.range 14).all (fun d => gjCheck 256 1 2 4 7 2 7 6 (x2JCols 216 (0 + d)) (gj216.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok94 : ∀ d < x2KeySize 1 k94, gjCheck 256 1 (x2KeyTypes 1 k94 0) (x2KeyTypes 1 k94 1) (x2KeyTypes 1 k94 2) (x2KeyMult 1 k94 0) (x2KeyMult 1 k94 1) (x2KeyMult 1 k94 2) (x2JCols (x2KeyGlobal 1 k94) d) (gj216.getD d 0) = true := by
  have hr : x2KeySize 1 k94 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 4 7 2 7 6 (x2JCols 216 d) (gj216.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 4 7 2 7 6 (x2JCols 216 d) (gj216.getD d 0)) 0 14 gjc94_0 d (Nat.zero_le d) (by omega)
x2_v_cols v216 gj216 216 256 84
theorem vc94_0 : (List.range 5).all (fun c => vCheck 256 84 14 gj216 (x2Trial_216.getD (0 + c) 0) (v216.getD (0 + c) 0)) = true := by decide +kernel
theorem vok94 : ∀ c < 5, vCheck 256 (x2KeyMult 1 k94 0 * x2KeyMult 1 k94 1 * x2KeyMult 1 k94 2) (x2KeySize 1 k94) gj216 (x2Trial_216.getD c 0) (v216.getD c 0) = true := by
  intro c hc
  show vCheck 256 84 14 gj216 (x2Trial_216.getD c 0) (v216.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 84 14 gj216 (x2Trial_216.getD c 0) (v216.getD c 0)) 0 5 vc94_0 c (Nat.zero_le c) (by omega)
theorem small94 : x2KeyDegree 1 k94 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k94 0 ∧ 1 ≤ x2KeyMult 1 k94 1 ∧ 1 ≤ x2KeyMult 1 k94 2 ∧ glRowOK 1 (x2KeyTypes 1 k94 0) (x2KeyMult 1 k94 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k94 1) (x2KeyMult 1 k94 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k94 2) (x2KeyMult 1 k94 2) 512 = true ∧ gj216.length = x2KeySize 1 k94 ∧ x2KeySize 1 k94 ≤ 512 ∧ v216.length = 5 := by decide +kernel
theorem chk94 : trialKeyChk 1 k94 5 gj216 x2Trial_216 v216 :=
  trialKeyChk_intro 1 k94 5 gj216 x2Trial_216 v216 small94 gjok94 vok94

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k94, ibFS [(v216, v216, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 4, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN94 : N k94 = x2TrialForm 1 k94) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 4 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k94 5 _ gj216 x2Trial_216 v216 (by decide) (by rw [hN94]; exact trialForm_eq 1 k94 5 x2Trial_216 (by decide) rfl) chk94

end ThreeCopyQutritWerner.X2.InK1x247
