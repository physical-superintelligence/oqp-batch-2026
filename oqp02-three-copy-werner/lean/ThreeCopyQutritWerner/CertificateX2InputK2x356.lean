module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 5, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x356
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k98 : x2Key 2 := ⟨98, by decide⟩
x2_gj_cols gj389 389 2 3 5 6 256
theorem gjc98_0 : (List.range 46).all (fun d => gjCheck 256 2 3 5 6 5 10 11 (x2JCols 389 (0 + d)) (gj389.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok98 : ∀ d < x2KeySize 2 k98, gjCheck 256 2 (x2KeyTypes 2 k98 0) (x2KeyTypes 2 k98 1) (x2KeyTypes 2 k98 2) (x2KeyMult 2 k98 0) (x2KeyMult 2 k98 1) (x2KeyMult 2 k98 2) (x2JCols (x2KeyGlobal 2 k98) d) (gj389.getD d 0) = true := by
  have hr : x2KeySize 2 k98 = 46 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 5 6 5 10 11 (x2JCols 389 d) (gj389.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 5 6 5 10 11 (x2JCols 389 d) (gj389.getD d 0)) 0 46 gjc98_0 d (Nat.zero_le d) (by omega)
x2_v_cols v389 gj389 389 256 550
theorem vc98_0 : (List.range 39).all (fun c => vCheck 256 550 46 gj389 (x2Trial_389.getD (0 + c) 0) (v389.getD (0 + c) 0)) = true := by decide +kernel
theorem vok98 : ∀ c < 39, vCheck 256 (x2KeyMult 2 k98 0 * x2KeyMult 2 k98 1 * x2KeyMult 2 k98 2) (x2KeySize 2 k98) gj389 (x2Trial_389.getD c 0) (v389.getD c 0) = true := by
  intro c hc
  show vCheck 256 550 46 gj389 (x2Trial_389.getD c 0) (v389.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 550 46 gj389 (x2Trial_389.getD c 0) (v389.getD c 0)) 0 39 vc98_0 c (Nat.zero_le c) (by omega)
theorem small98 : x2KeyDegree 2 k98 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k98 0 ∧ 1 ≤ x2KeyMult 2 k98 1 ∧ 1 ≤ x2KeyMult 2 k98 2 ∧ glRowOK 2 (x2KeyTypes 2 k98 0) (x2KeyMult 2 k98 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k98 1) (x2KeyMult 2 k98 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k98 2) (x2KeyMult 2 k98 2) 512 = true ∧ gj389.length = x2KeySize 2 k98 ∧ x2KeySize 2 k98 ≤ 512 ∧ v389.length = 39 := by decide +kernel
theorem chk98 : trialKeyChk 2 k98 39 gj389 x2Trial_389 v389 :=
  trialKeyChk_intro 2 k98 39 gj389 x2Trial_389 v389 small98 gjok98 vok98

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k98, ibFS [(v389, v389, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN98 : N k98 = x2TrialForm 2 k98) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 5 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k98 39 _ gj389 x2Trial_389 v389 (by decide) (by rw [hN98]; exact trialForm_eq 2 k98 39 x2Trial_389 (by decide) rfl) chk98

end ThreeCopyQutritWerner.X2.InK2x356
