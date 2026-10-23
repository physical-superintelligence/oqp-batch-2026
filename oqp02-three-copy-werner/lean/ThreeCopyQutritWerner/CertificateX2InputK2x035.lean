module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x035
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k17 : x2Key 2 := ⟨17, by decide⟩
x2_gj_cols gj308 308 2 0 3 5 256
theorem gjc17_0 : (List.range 4).all (fun d => gjCheck 256 2 0 3 5 1 5 10 (x2JCols 308 (0 + d)) (gj308.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok17 : ∀ d < x2KeySize 2 k17, gjCheck 256 2 (x2KeyTypes 2 k17 0) (x2KeyTypes 2 k17 1) (x2KeyTypes 2 k17 2) (x2KeyMult 2 k17 0) (x2KeyMult 2 k17 1) (x2KeyMult 2 k17 2) (x2JCols (x2KeyGlobal 2 k17) d) (gj308.getD d 0) = true := by
  have hr : x2KeySize 2 k17 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 3 5 1 5 10 (x2JCols 308 d) (gj308.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 3 5 1 5 10 (x2JCols 308 d) (gj308.getD d 0)) 0 4 gjc17_0 d (Nat.zero_le d) (by omega)
x2_v_cols v308 gj308 308 256 50
theorem vc17_0 : (List.range 2).all (fun c => vCheck 256 50 4 gj308 (x2Trial_308.getD (0 + c) 0) (v308.getD (0 + c) 0)) = true := by decide +kernel
theorem vok17 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k17 0 * x2KeyMult 2 k17 1 * x2KeyMult 2 k17 2) (x2KeySize 2 k17) gj308 (x2Trial_308.getD c 0) (v308.getD c 0) = true := by
  intro c hc
  show vCheck 256 50 4 gj308 (x2Trial_308.getD c 0) (v308.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 50 4 gj308 (x2Trial_308.getD c 0) (v308.getD c 0)) 0 2 vc17_0 c (Nat.zero_le c) (by omega)
theorem small17 : x2KeyDegree 2 k17 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k17 0 ∧ 1 ≤ x2KeyMult 2 k17 1 ∧ 1 ≤ x2KeyMult 2 k17 2 ∧ glRowOK 2 (x2KeyTypes 2 k17 0) (x2KeyMult 2 k17 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k17 1) (x2KeyMult 2 k17 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k17 2) (x2KeyMult 2 k17 2) 512 = true ∧ gj308.length = x2KeySize 2 k17 ∧ x2KeySize 2 k17 ≤ 512 ∧ v308.length = 2 := by decide +kernel
theorem chk17 : trialKeyChk 2 k17 2 gj308 x2Trial_308 v308 :=
  trialKeyChk_intro 2 k17 2 gj308 x2Trial_308 v308 small17 gjok17 vok17

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k17, ibFS [(v308, v308, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN17 : N k17 = x2TrialForm 2 k17) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 3 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k17 2 _ gj308 x2Trial_308 v308 (by decide) (by rw [hN17]; exact trialForm_eq 2 k17 2 x2Trial_308 (by decide) rfl) chk17

end ThreeCopyQutritWerner.X2.InK2x035
