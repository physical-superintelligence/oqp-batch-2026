module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 5, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x057
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k30 : x2Key 1 := ⟨30, by decide⟩
x2_gj_cols gj152 152 1 0 5 7 256
theorem gjc30_0 : (List.range 7).all (fun d => gjCheck 256 1 0 5 7 1 7 6 (x2JCols 152 (0 + d)) (gj152.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok30 : ∀ d < x2KeySize 1 k30, gjCheck 256 1 (x2KeyTypes 1 k30 0) (x2KeyTypes 1 k30 1) (x2KeyTypes 1 k30 2) (x2KeyMult 1 k30 0) (x2KeyMult 1 k30 1) (x2KeyMult 1 k30 2) (x2JCols (x2KeyGlobal 1 k30) d) (gj152.getD d 0) = true := by
  have hr : x2KeySize 1 k30 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 5 7 1 7 6 (x2JCols 152 d) (gj152.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 5 7 1 7 6 (x2JCols 152 d) (gj152.getD d 0)) 0 7 gjc30_0 d (Nat.zero_le d) (by omega)
x2_v_cols v152 gj152 152 256 42
theorem vc30_0 : (List.range 3).all (fun c => vCheck 256 42 7 gj152 (x2Trial_152.getD (0 + c) 0) (v152.getD (0 + c) 0)) = true := by decide +kernel
theorem vok30 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k30 0 * x2KeyMult 1 k30 1 * x2KeyMult 1 k30 2) (x2KeySize 1 k30) gj152 (x2Trial_152.getD c 0) (v152.getD c 0) = true := by
  intro c hc
  show vCheck 256 42 7 gj152 (x2Trial_152.getD c 0) (v152.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 42 7 gj152 (x2Trial_152.getD c 0) (v152.getD c 0)) 0 3 vc30_0 c (Nat.zero_le c) (by omega)
theorem small30 : x2KeyDegree 1 k30 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k30 0 ∧ 1 ≤ x2KeyMult 1 k30 1 ∧ 1 ≤ x2KeyMult 1 k30 2 ∧ glRowOK 1 (x2KeyTypes 1 k30 0) (x2KeyMult 1 k30 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k30 1) (x2KeyMult 1 k30 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k30 2) (x2KeyMult 1 k30 2) 512 = true ∧ gj152.length = x2KeySize 1 k30 ∧ x2KeySize 1 k30 ≤ 512 ∧ v152.length = 3 := by decide +kernel
theorem chk30 : trialKeyChk 1 k30 3 gj152 x2Trial_152 v152 :=
  trialKeyChk_intro 1 k30 3 gj152 x2Trial_152 v152 small30 gjok30 vok30

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k30, ibFS [(v152, v152, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 5, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN30 : N k30 = x2TrialForm 1 k30) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 5 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k30 3 _ gj152 x2Trial_152 v152 (by decide) (by rw [hN30]; exact trialForm_eq 1 k30 3 x2Trial_152 (by decide) rfl) chk30

end ThreeCopyQutritWerner.X2.InK1x057
