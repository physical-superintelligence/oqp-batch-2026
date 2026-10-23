module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 5, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x256
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k81 : x2Key 2 := ⟨81, by decide⟩
x2_gj_cols gj372 372 2 2 5 6 256
theorem gjc81_0 : (List.range 44).all (fun d => gjCheck 256 2 2 5 6 5 10 11 (x2JCols 372 (0 + d)) (gj372.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok81 : ∀ d < x2KeySize 2 k81, gjCheck 256 2 (x2KeyTypes 2 k81 0) (x2KeyTypes 2 k81 1) (x2KeyTypes 2 k81 2) (x2KeyMult 2 k81 0) (x2KeyMult 2 k81 1) (x2KeyMult 2 k81 2) (x2JCols (x2KeyGlobal 2 k81) d) (gj372.getD d 0) = true := by
  have hr : x2KeySize 2 k81 = 44 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 5 6 5 10 11 (x2JCols 372 d) (gj372.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 5 6 5 10 11 (x2JCols 372 d) (gj372.getD d 0)) 0 44 gjc81_0 d (Nat.zero_le d) (by omega)
x2_v_cols v372 gj372 372 256 550
theorem vc81_0 : (List.range 43).all (fun c => vCheck 256 550 44 gj372 (x2Trial_372.getD (0 + c) 0) (v372.getD (0 + c) 0)) = true := by decide +kernel
theorem vok81 : ∀ c < 43, vCheck 256 (x2KeyMult 2 k81 0 * x2KeyMult 2 k81 1 * x2KeyMult 2 k81 2) (x2KeySize 2 k81) gj372 (x2Trial_372.getD c 0) (v372.getD c 0) = true := by
  intro c hc
  show vCheck 256 550 44 gj372 (x2Trial_372.getD c 0) (v372.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 550 44 gj372 (x2Trial_372.getD c 0) (v372.getD c 0)) 0 43 vc81_0 c (Nat.zero_le c) (by omega)
theorem small81 : x2KeyDegree 2 k81 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k81 0 ∧ 1 ≤ x2KeyMult 2 k81 1 ∧ 1 ≤ x2KeyMult 2 k81 2 ∧ glRowOK 2 (x2KeyTypes 2 k81 0) (x2KeyMult 2 k81 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k81 1) (x2KeyMult 2 k81 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k81 2) (x2KeyMult 2 k81 2) 512 = true ∧ gj372.length = x2KeySize 2 k81 ∧ x2KeySize 2 k81 ≤ 512 ∧ v372.length = 43 := by decide +kernel
theorem chk81 : trialKeyChk 2 k81 43 gj372 x2Trial_372 v372 :=
  trialKeyChk_intro 2 k81 43 gj372 x2Trial_372 v372 small81 gjok81 vok81

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k81, ibFS [(v372, v372, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN81 : N k81 = x2TrialForm 2 k81) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 5 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k81 43 _ gj372 x2Trial_372 v372 (by decide) (by rw [hN81]; exact trialForm_eq 2 k81 43 x2Trial_372 (by decide) rfl) chk81

end ThreeCopyQutritWerner.X2.InK2x256
