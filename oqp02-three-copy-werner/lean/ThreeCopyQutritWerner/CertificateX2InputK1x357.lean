module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 5, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x357
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k123 : x2Key 1 := ⟨123, by decide⟩
x2_gj_cols gj245 245 1 3 5 7 256
theorem gjc123_0 : (List.range 63).all (fun d => gjCheck 256 1 3 5 7 9 7 6 (x2JCols 245 (0 + d)) (gj245.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok123 : ∀ d < x2KeySize 1 k123, gjCheck 256 1 (x2KeyTypes 1 k123 0) (x2KeyTypes 1 k123 1) (x2KeyTypes 1 k123 2) (x2KeyMult 1 k123 0) (x2KeyMult 1 k123 1) (x2KeyMult 1 k123 2) (x2JCols (x2KeyGlobal 1 k123) d) (gj245.getD d 0) = true := by
  have hr : x2KeySize 1 k123 = 63 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 5 7 9 7 6 (x2JCols 245 d) (gj245.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 5 7 9 7 6 (x2JCols 245 d) (gj245.getD d 0)) 0 63 gjc123_0 d (Nat.zero_le d) (by omega)
x2_v_cols v245 gj245 245 256 378
theorem vc123_0 : (List.range 31).all (fun c => vCheck 256 378 63 gj245 (x2Trial_245.getD (0 + c) 0) (v245.getD (0 + c) 0)) = true := by decide +kernel
theorem vok123 : ∀ c < 31, vCheck 256 (x2KeyMult 1 k123 0 * x2KeyMult 1 k123 1 * x2KeyMult 1 k123 2) (x2KeySize 1 k123) gj245 (x2Trial_245.getD c 0) (v245.getD c 0) = true := by
  intro c hc
  show vCheck 256 378 63 gj245 (x2Trial_245.getD c 0) (v245.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 378 63 gj245 (x2Trial_245.getD c 0) (v245.getD c 0)) 0 31 vc123_0 c (Nat.zero_le c) (by omega)
theorem small123 : x2KeyDegree 1 k123 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k123 0 ∧ 1 ≤ x2KeyMult 1 k123 1 ∧ 1 ≤ x2KeyMult 1 k123 2 ∧ glRowOK 1 (x2KeyTypes 1 k123 0) (x2KeyMult 1 k123 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k123 1) (x2KeyMult 1 k123 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k123 2) (x2KeyMult 1 k123 2) 512 = true ∧ gj245.length = x2KeySize 1 k123 ∧ x2KeySize 1 k123 ≤ 512 ∧ v245.length = 31 := by decide +kernel
theorem chk123 : trialKeyChk 1 k123 31 gj245 x2Trial_245 v245 :=
  trialKeyChk_intro 1 k123 31 gj245 x2Trial_245 v245 small123 gjok123 vok123

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k123, ibFS [(v245, v245, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 5, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN123 : N k123 = x2TrialForm 1 k123) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 5 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k123 31 _ gj245 x2Trial_245 v245 (by decide) (by rw [hN123]; exact trialForm_eq 1 k123 31 x2Trial_245 (by decide) rfl) chk123

end ThreeCopyQutritWerner.X2.InK1x357
