module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x245
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k77 : x2Key 2 := ⟨77, by decide⟩
x2_gj_cols gj368 368 2 2 4 5 256
theorem gjc77_0 : (List.range 62).all (fun d => gjCheck 256 2 2 4 5 5 15 10 (x2JCols 368 (0 + d)) (gj368.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok77 : ∀ d < x2KeySize 2 k77, gjCheck 256 2 (x2KeyTypes 2 k77 0) (x2KeyTypes 2 k77 1) (x2KeyTypes 2 k77 2) (x2KeyMult 2 k77 0) (x2KeyMult 2 k77 1) (x2KeyMult 2 k77 2) (x2JCols (x2KeyGlobal 2 k77) d) (gj368.getD d 0) = true := by
  have hr : x2KeySize 2 k77 = 62 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 4 5 5 15 10 (x2JCols 368 d) (gj368.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 4 5 5 15 10 (x2JCols 368 d) (gj368.getD d 0)) 0 62 gjc77_0 d (Nat.zero_le d) (by omega)
x2_v_cols v368 gj368 368 256 750
theorem vc77_0 : (List.range 49).all (fun c => vCheck 256 750 62 gj368 (x2Trial_368.getD (0 + c) 0) (v368.getD (0 + c) 0)) = true := by decide +kernel
theorem vok77 : ∀ c < 49, vCheck 256 (x2KeyMult 2 k77 0 * x2KeyMult 2 k77 1 * x2KeyMult 2 k77 2) (x2KeySize 2 k77) gj368 (x2Trial_368.getD c 0) (v368.getD c 0) = true := by
  intro c hc
  show vCheck 256 750 62 gj368 (x2Trial_368.getD c 0) (v368.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 750 62 gj368 (x2Trial_368.getD c 0) (v368.getD c 0)) 0 49 vc77_0 c (Nat.zero_le c) (by omega)
theorem small77 : x2KeyDegree 2 k77 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k77 0 ∧ 1 ≤ x2KeyMult 2 k77 1 ∧ 1 ≤ x2KeyMult 2 k77 2 ∧ glRowOK 2 (x2KeyTypes 2 k77 0) (x2KeyMult 2 k77 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k77 1) (x2KeyMult 2 k77 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k77 2) (x2KeyMult 2 k77 2) 512 = true ∧ gj368.length = x2KeySize 2 k77 ∧ x2KeySize 2 k77 ≤ 512 ∧ v368.length = 49 := by decide +kernel
theorem chk77 : trialKeyChk 2 k77 49 gj368 x2Trial_368 v368 :=
  trialKeyChk_intro 2 k77 49 gj368 x2Trial_368 v368 small77 gjok77 vok77

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k77, ibFS [(v368, v368, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN77 : N k77 = x2TrialForm 2 k77) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 4 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k77 49 _ gj368 x2Trial_368 v368 (by decide) (by rw [hN77]; exact trialForm_eq 2 k77 49 x2Trial_368 (by decide) rfl) chk77

end ThreeCopyQutritWerner.X2.InK2x245
