module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x137
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k59 : x2Key 1 := ⟨59, by decide⟩
x2_gj_cols gj181 181 1 1 3 7 256
theorem gjc59_0 : (List.range 18).all (fun d => gjCheck 256 1 1 3 7 2 9 6 (x2JCols 181 (0 + d)) (gj181.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok59 : ∀ d < x2KeySize 1 k59, gjCheck 256 1 (x2KeyTypes 1 k59 0) (x2KeyTypes 1 k59 1) (x2KeyTypes 1 k59 2) (x2KeyMult 1 k59 0) (x2KeyMult 1 k59 1) (x2KeyMult 1 k59 2) (x2JCols (x2KeyGlobal 1 k59) d) (gj181.getD d 0) = true := by
  have hr : x2KeySize 1 k59 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 3 7 2 9 6 (x2JCols 181 d) (gj181.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 3 7 2 9 6 (x2JCols 181 d) (gj181.getD d 0)) 0 18 gjc59_0 d (Nat.zero_le d) (by omega)
x2_v_cols v181 gj181 181 256 108
theorem vc59_0 : (List.range 3).all (fun c => vCheck 256 108 18 gj181 (x2Trial_181.getD (0 + c) 0) (v181.getD (0 + c) 0)) = true := by decide +kernel
theorem vok59 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k59 0 * x2KeyMult 1 k59 1 * x2KeyMult 1 k59 2) (x2KeySize 1 k59) gj181 (x2Trial_181.getD c 0) (v181.getD c 0) = true := by
  intro c hc
  show vCheck 256 108 18 gj181 (x2Trial_181.getD c 0) (v181.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 108 18 gj181 (x2Trial_181.getD c 0) (v181.getD c 0)) 0 3 vc59_0 c (Nat.zero_le c) (by omega)
theorem small59 : x2KeyDegree 1 k59 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k59 0 ∧ 1 ≤ x2KeyMult 1 k59 1 ∧ 1 ≤ x2KeyMult 1 k59 2 ∧ glRowOK 1 (x2KeyTypes 1 k59 0) (x2KeyMult 1 k59 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k59 1) (x2KeyMult 1 k59 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k59 2) (x2KeyMult 1 k59 2) 512 = true ∧ gj181.length = x2KeySize 1 k59 ∧ x2KeySize 1 k59 ≤ 512 ∧ v181.length = 3 := by decide +kernel
theorem chk59 : trialKeyChk 1 k59 3 gj181 x2Trial_181 v181 :=
  trialKeyChk_intro 1 k59 3 gj181 x2Trial_181 v181 small59 gjok59 vok59

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k59, ibFS [(v181, v181, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 3, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN59 : N k59 = x2TrialForm 1 k59) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 3 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k59 3 _ gj181 x2Trial_181 v181 (by decide) (by rw [hN59]; exact trialForm_eq 1 k59 3 x2Trial_181 (by decide) rfl) chk59

end ThreeCopyQutritWerner.X2.InK1x137
