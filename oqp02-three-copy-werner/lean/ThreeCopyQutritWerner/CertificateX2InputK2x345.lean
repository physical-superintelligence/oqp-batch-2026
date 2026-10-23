module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x345
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k94 : x2Key 2 := ⟨94, by decide⟩
x2_gj_cols gj385 385 2 3 4 5 256
theorem gjc94_0 : (List.range 62).all (fun d => gjCheck 256 2 3 4 5 5 15 10 (x2JCols 385 (0 + d)) (gj385.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok94 : ∀ d < x2KeySize 2 k94, gjCheck 256 2 (x2KeyTypes 2 k94 0) (x2KeyTypes 2 k94 1) (x2KeyTypes 2 k94 2) (x2KeyMult 2 k94 0) (x2KeyMult 2 k94 1) (x2KeyMult 2 k94 2) (x2JCols (x2KeyGlobal 2 k94) d) (gj385.getD d 0) = true := by
  have hr : x2KeySize 2 k94 = 62 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 4 5 5 15 10 (x2JCols 385 d) (gj385.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 4 5 5 15 10 (x2JCols 385 d) (gj385.getD d 0)) 0 62 gjc94_0 d (Nat.zero_le d) (by omega)
x2_v_cols v385 gj385 385 256 750
theorem vc94_0 : (List.range 39).all (fun c => vCheck 256 750 62 gj385 (x2Trial_385.getD (0 + c) 0) (v385.getD (0 + c) 0)) = true := by decide +kernel
theorem vok94 : ∀ c < 39, vCheck 256 (x2KeyMult 2 k94 0 * x2KeyMult 2 k94 1 * x2KeyMult 2 k94 2) (x2KeySize 2 k94) gj385 (x2Trial_385.getD c 0) (v385.getD c 0) = true := by
  intro c hc
  show vCheck 256 750 62 gj385 (x2Trial_385.getD c 0) (v385.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 750 62 gj385 (x2Trial_385.getD c 0) (v385.getD c 0)) 0 39 vc94_0 c (Nat.zero_le c) (by omega)
theorem small94 : x2KeyDegree 2 k94 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k94 0 ∧ 1 ≤ x2KeyMult 2 k94 1 ∧ 1 ≤ x2KeyMult 2 k94 2 ∧ glRowOK 2 (x2KeyTypes 2 k94 0) (x2KeyMult 2 k94 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k94 1) (x2KeyMult 2 k94 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k94 2) (x2KeyMult 2 k94 2) 512 = true ∧ gj385.length = x2KeySize 2 k94 ∧ x2KeySize 2 k94 ≤ 512 ∧ v385.length = 39 := by decide +kernel
theorem chk94 : trialKeyChk 2 k94 39 gj385 x2Trial_385 v385 :=
  trialKeyChk_intro 2 k94 39 gj385 x2Trial_385 v385 small94 gjok94 vok94

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k94, ibFS [(v385, v385, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN94 : N k94 = x2TrialForm 2 k94) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 4 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k94 39 _ gj385 x2Trial_385 v385 (by decide) (by rw [hN94]; exact trialForm_eq 2 k94 39 x2Trial_385 (by decide) rfl) chk94

end ThreeCopyQutritWerner.X2.InK2x345
