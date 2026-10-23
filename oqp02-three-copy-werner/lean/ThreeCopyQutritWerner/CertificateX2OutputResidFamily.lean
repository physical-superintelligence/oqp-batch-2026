module

public import ThreeCopyQutritWerner.CertificateX2OutputPipeline
public import ThreeCopyQutritWerner.CertificateX2NhFamily
public import ThreeCopyQutritWerner.CertificateX2OutLitS1
public import ThreeCopyQutritWerner.CertificateX2OutLitS2

@[expose] public section


/-! Output stage: the residual identity for all 122 h blocks. With the proved targets
(`x2Target_concrete`), the kernel-checked integer identities `N k₀ = T8 k₁ - O1 k₂ - O2 k₃` (one per block) give:
if the two sectors' outputs are the literals `x2OLit1`, `x2OLit2` (what the output stage proves from the tables, block by block, with `x2Out_of_tables`), then every corrected residual block is `x2NhLit b / den`
(the `heq` with `Nlit = x2HNum = x2NhLit`, `den b = X2Nh.den`).
k₀ = 3584528202624742195200000, k₁ = 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000, k₂ = 1, k₃ = 729. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem hintM_003k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_003k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_003k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_003k0 - (729 : ℤ) • OutLit2.o2_003k0 := by
  decide +kernel

theorem hint_003k0 : ∀ c c' : Fin 1,
    X2Nh.nh_003k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_003k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_003k0 c c' * 1 -
        OutLit2.o2_003k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_003k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_004k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_004k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_004k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_004k0 - (729 : ℤ) • OutLit2.o2_004k0 := by
  decide +kernel

theorem hint_004k0 : ∀ c c' : Fin 1,
    X2Nh.nh_004k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_004k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_004k0 c c' * 1 -
        OutLit2.o2_004k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_004k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_005k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_005k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_005k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_005k0 - (729 : ℤ) • OutLit2.o2_005k0 := by
  decide +kernel

theorem hint_005k0 : ∀ c c' : Fin 1,
    X2Nh.nh_005k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_005k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_005k0 c c' * 1 -
        OutLit2.o2_005k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_005k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_011k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_011k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_011k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_011k0 - (729 : ℤ) • OutLit2.o2_011k0 := by
  decide +kernel

theorem hint_011k0 : ∀ c c' : Fin 1,
    X2Nh.nh_011k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_011k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_011k0 c c' * 1 -
        OutLit2.o2_011k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_011k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_012k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_012k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_012k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_012k0 - (729 : ℤ) • OutLit2.o2_012k0 := by
  decide +kernel

theorem hint_012k0 : ∀ c c' : Fin 1,
    X2Nh.nh_012k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_012k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_012k0 c c' * 1 -
        OutLit2.o2_012k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_012k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_013k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_013k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_013k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_013k0 - (729 : ℤ) • OutLit2.o2_013k0 := by
  decide +kernel

theorem hint_013k0 : ∀ c c' : Fin 1,
    X2Nh.nh_013k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_013k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_013k0 c c' * 1 -
        OutLit2.o2_013k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_013k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_014k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_014k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_014k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_014k0 - (729 : ℤ) • OutLit2.o2_014k0 := by
  decide +kernel

theorem hint_014k0 : ∀ c c' : Fin 3,
    X2Nh.nh_014k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_014k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_014k0 c c' * 1 -
        OutLit2.o2_014k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_014k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_015k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_015k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_015k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_015k0 - (729 : ℤ) • OutLit2.o2_015k0 := by
  decide +kernel

theorem hint_015k0 : ∀ c c' : Fin 2,
    X2Nh.nh_015k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_015k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_015k0 c c' * 1 -
        OutLit2.o2_015k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_015k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_016k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_016k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_016k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_016k0 - (729 : ℤ) • OutLit2.o2_016k0 := by
  decide +kernel

theorem hint_016k0 : ∀ c c' : Fin 2,
    X2Nh.nh_016k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_016k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_016k0 c c' * 1 -
        OutLit2.o2_016k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_016k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_022k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_022k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_022k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_022k0 - (729 : ℤ) • OutLit2.o2_022k0 := by
  decide +kernel

theorem hint_022k0 : ∀ c c' : Fin 1,
    X2Nh.nh_022k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_022k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_022k0 c c' * 1 -
        OutLit2.o2_022k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_022k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_023k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_023k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_023k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_023k0 - (729 : ℤ) • OutLit2.o2_023k0 := by
  decide +kernel

theorem hint_023k0 : ∀ c c' : Fin 2,
    X2Nh.nh_023k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_023k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_023k0 c c' * 1 -
        OutLit2.o2_023k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_023k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_024k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_024k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_024k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_024k0 - (729 : ℤ) • OutLit2.o2_024k0 := by
  decide +kernel

theorem hint_024k0 : ∀ c c' : Fin 4,
    X2Nh.nh_024k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_024k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_024k0 c c' * 1 -
        OutLit2.o2_024k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_024k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_025k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_025k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_025k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_025k0 - (729 : ℤ) • OutLit2.o2_025k0 := by
  decide +kernel

theorem hint_025k0 : ∀ c c' : Fin 3,
    X2Nh.nh_025k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_025k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_025k0 c c' * 1 -
        OutLit2.o2_025k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_025k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_026k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_026k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_026k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_026k0 - (729 : ℤ) • OutLit2.o2_026k0 := by
  decide +kernel

theorem hint_026k0 : ∀ c c' : Fin 2,
    X2Nh.nh_026k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_026k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_026k0 c c' * 1 -
        OutLit2.o2_026k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_026k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_033k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_033k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_033k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_033k0 - (729 : ℤ) • OutLit2.o2_033k0 := by
  decide +kernel

theorem hint_033k0 : ∀ c c' : Fin 1,
    X2Nh.nh_033k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_033k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_033k0 c c' * 1 -
        OutLit2.o2_033k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_033k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_034k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_034k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_034k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_034k0 - (729 : ℤ) • OutLit2.o2_034k0 := by
  decide +kernel

theorem hint_034k0 : ∀ c c' : Fin 3,
    X2Nh.nh_034k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_034k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_034k0 c c' * 1 -
        OutLit2.o2_034k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_034k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_035k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_035k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_035k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_035k0 - (729 : ℤ) • OutLit2.o2_035k0 := by
  decide +kernel

theorem hint_035k0 : ∀ c c' : Fin 2,
    X2Nh.nh_035k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_035k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_035k0 c c' * 1 -
        OutLit2.o2_035k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_035k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_036k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_036k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_036k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_036k0 - (729 : ℤ) • OutLit2.o2_036k0 := by
  decide +kernel

theorem hint_036k0 : ∀ c c' : Fin 2,
    X2Nh.nh_036k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_036k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_036k0 c c' * 1 -
        OutLit2.o2_036k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_036k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_044k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_044k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_044k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_044k0 - (729 : ℤ) • OutLit2.o2_044k0 := by
  decide +kernel

theorem hint_044k0 : ∀ c c' : Fin 7,
    X2Nh.nh_044k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_044k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_044k0 c c' * 1 -
        OutLit2.o2_044k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_044k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_044k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_044k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_044k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_044k1 - (729 : ℤ) • OutLit2.o2_044k1 := by
  decide +kernel

theorem hint_044k1 : ∀ c c' : Fin 3,
    X2Nh.nh_044k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_044k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_044k1 c c' * 1 -
        OutLit2.o2_044k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_044k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_045k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_045k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 6) => (Tgt.t8_045k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_045k0 - (729 : ℤ) • OutLit2.o2_045k0 := by
  decide +kernel

theorem hint_045k0 : ∀ c c' : Fin 6,
    X2Nh.nh_045k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_045k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_045k0 c c' * 1 -
        OutLit2.o2_045k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_045k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_046k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_046k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_046k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_046k0 - (729 : ℤ) • OutLit2.o2_046k0 := by
  decide +kernel

theorem hint_046k0 : ∀ c c' : Fin 7,
    X2Nh.nh_046k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_046k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_046k0 c c' * 1 -
        OutLit2.o2_046k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_046k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_055k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_055k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_055k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_055k0 - (729 : ℤ) • OutLit2.o2_055k0 := by
  decide +kernel

theorem hint_055k0 : ∀ c c' : Fin 3,
    X2Nh.nh_055k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_055k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_055k0 c c' * 1 -
        OutLit2.o2_055k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_055k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_055k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_055k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_055k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_055k1 - (729 : ℤ) • OutLit2.o2_055k1 := by
  decide +kernel

theorem hint_055k1 : ∀ c c' : Fin 1,
    X2Nh.nh_055k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_055k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_055k1 c c' * 1 -
        OutLit2.o2_055k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_055k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_056k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_056k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_056k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_056k0 - (729 : ℤ) • OutLit2.o2_056k0 := by
  decide +kernel

theorem hint_056k0 : ∀ c c' : Fin 4,
    X2Nh.nh_056k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_056k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_056k0 c c' * 1 -
        OutLit2.o2_056k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_056k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_066k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_066k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_066k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_066k0 - (729 : ℤ) • OutLit2.o2_066k0 := by
  decide +kernel

theorem hint_066k0 : ∀ c c' : Fin 4,
    X2Nh.nh_066k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_066k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_066k0 c c' * 1 -
        OutLit2.o2_066k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_066k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_066k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_066k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_066k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_066k1 - (729 : ℤ) • OutLit2.o2_066k1 := by
  decide +kernel

theorem hint_066k1 : ∀ c c' : Fin 1,
    X2Nh.nh_066k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_066k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_066k1 c c' * 1 -
        OutLit2.o2_066k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_066k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_111k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_111k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_111k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_111k0 - (729 : ℤ) • OutLit2.o2_111k0 := by
  decide +kernel

theorem hint_111k0 : ∀ c c' : Fin 1,
    X2Nh.nh_111k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_111k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_111k0 c c' * 1 -
        OutLit2.o2_111k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_111k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_111k2 : (3584528202624742195200000 : ℤ) • X2Nh.nh_111k2 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_111k2.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_111k2 - (729 : ℤ) • OutLit2.o2_111k2 := by
  decide +kernel

theorem hint_111k2 : ∀ c c' : Fin 1,
    X2Nh.nh_111k2 c c' * 3584528202624742195200000 =
      (Tgt.t8_111k2.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_111k2 c c' * 1 -
        OutLit2.o2_111k2 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_111k2 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_112k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_112k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_112k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_112k0 - (729 : ℤ) • OutLit2.o2_112k0 := by
  decide +kernel

theorem hint_112k0 : ∀ c c' : Fin 3,
    X2Nh.nh_112k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_112k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_112k0 c c' * 1 -
        OutLit2.o2_112k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_112k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_112k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_112k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_112k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_112k1 - (729 : ℤ) • OutLit2.o2_112k1 := by
  decide +kernel

theorem hint_112k1 : ∀ c c' : Fin 1,
    X2Nh.nh_112k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_112k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_112k1 c c' * 1 -
        OutLit2.o2_112k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_112k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_113k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_113k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_113k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_113k0 - (729 : ℤ) • OutLit2.o2_113k0 := by
  decide +kernel

theorem hint_113k0 : ∀ c c' : Fin 3,
    X2Nh.nh_113k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_113k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_113k0 c c' * 1 -
        OutLit2.o2_113k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_113k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_113k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_113k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_113k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_113k1 - (729 : ℤ) • OutLit2.o2_113k1 := by
  decide +kernel

theorem hint_113k1 : ∀ c c' : Fin 1,
    X2Nh.nh_113k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_113k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_113k1 c c' * 1 -
        OutLit2.o2_113k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_113k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_114k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_114k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_114k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_114k0 - (729 : ℤ) • OutLit2.o2_114k0 := by
  decide +kernel

theorem hint_114k0 : ∀ c c' : Fin 7,
    X2Nh.nh_114k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_114k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_114k0 c c' * 1 -
        OutLit2.o2_114k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_114k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_114k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_114k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_114k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_114k1 - (729 : ℤ) • OutLit2.o2_114k1 := by
  decide +kernel

theorem hint_114k1 : ∀ c c' : Fin 4,
    X2Nh.nh_114k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_114k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_114k1 c c' * 1 -
        OutLit2.o2_114k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_114k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_115k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_115k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 5) => (Tgt.t8_115k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_115k0 - (729 : ℤ) • OutLit2.o2_115k0 := by
  decide +kernel

theorem hint_115k0 : ∀ c c' : Fin 5,
    X2Nh.nh_115k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_115k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_115k0 c c' * 1 -
        OutLit2.o2_115k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_115k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_115k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_115k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_115k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_115k1 - (729 : ℤ) • OutLit2.o2_115k1 := by
  decide +kernel

theorem hint_115k1 : ∀ c c' : Fin 2,
    X2Nh.nh_115k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_115k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_115k1 c c' * 1 -
        OutLit2.o2_115k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_115k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_116k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_116k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_116k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_116k0 - (729 : ℤ) • OutLit2.o2_116k0 := by
  decide +kernel

theorem hint_116k0 : ∀ c c' : Fin 4,
    X2Nh.nh_116k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_116k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_116k0 c c' * 1 -
        OutLit2.o2_116k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_116k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_116k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_116k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_116k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_116k1 - (729 : ℤ) • OutLit2.o2_116k1 := by
  decide +kernel

theorem hint_116k1 : ∀ c c' : Fin 3,
    X2Nh.nh_116k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_116k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_116k1 c c' * 1 -
        OutLit2.o2_116k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_116k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_122k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_122k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_122k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_122k0 - (729 : ℤ) • OutLit2.o2_122k0 := by
  decide +kernel

theorem hint_122k0 : ∀ c c' : Fin 3,
    X2Nh.nh_122k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_122k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_122k0 c c' * 1 -
        OutLit2.o2_122k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_122k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_122k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_122k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_122k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_122k1 - (729 : ℤ) • OutLit2.o2_122k1 := by
  decide +kernel

theorem hint_122k1 : ∀ c c' : Fin 2,
    X2Nh.nh_122k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_122k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_122k1 c c' * 1 -
        OutLit2.o2_122k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_122k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_123k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_123k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 5) => (Tgt.t8_123k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_123k0 - (729 : ℤ) • OutLit2.o2_123k0 := by
  decide +kernel

theorem hint_123k0 : ∀ c c' : Fin 5,
    X2Nh.nh_123k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_123k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_123k0 c c' * 1 -
        OutLit2.o2_123k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_123k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_124k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_124k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 14) => (Tgt.t8_124k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_124k0 - (729 : ℤ) • OutLit2.o2_124k0 := by
  decide +kernel

theorem hint_124k0 : ∀ c c' : Fin 14,
    X2Nh.nh_124k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_124k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_124k0 c c' * 1 -
        OutLit2.o2_124k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_124k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_125k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_125k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 9) => (Tgt.t8_125k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_125k0 - (729 : ℤ) • OutLit2.o2_125k0 := by
  decide +kernel

theorem hint_125k0 : ∀ c c' : Fin 9,
    X2Nh.nh_125k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_125k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_125k0 c c' * 1 -
        OutLit2.o2_125k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_125k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_126k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_126k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 9) => (Tgt.t8_126k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_126k0 - (729 : ℤ) • OutLit2.o2_126k0 := by
  decide +kernel

theorem hint_126k0 : ∀ c c' : Fin 9,
    X2Nh.nh_126k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_126k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_126k0 c c' * 1 -
        OutLit2.o2_126k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_126k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_133k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_133k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 3) => (Tgt.t8_133k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_133k0 - (729 : ℤ) • OutLit2.o2_133k0 := by
  decide +kernel

theorem hint_133k0 : ∀ c c' : Fin 3,
    X2Nh.nh_133k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_133k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_133k0 c c' * 1 -
        OutLit2.o2_133k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_133k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_133k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_133k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_133k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_133k1 - (729 : ℤ) • OutLit2.o2_133k1 := by
  decide +kernel

theorem hint_133k1 : ∀ c c' : Fin 1,
    X2Nh.nh_133k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_133k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_133k1 c c' * 1 -
        OutLit2.o2_133k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_133k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_134k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_134k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 13) => (Tgt.t8_134k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_134k0 - (729 : ℤ) • OutLit2.o2_134k0 := by
  decide +kernel

theorem hint_134k0 : ∀ c c' : Fin 13,
    X2Nh.nh_134k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_134k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_134k0 c c' * 1 -
        OutLit2.o2_134k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_134k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_135k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_135k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 8) => (Tgt.t8_135k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_135k0 - (729 : ℤ) • OutLit2.o2_135k0 := by
  decide +kernel

theorem hint_135k0 : ∀ c c' : Fin 8,
    X2Nh.nh_135k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_135k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_135k0 c c' * 1 -
        OutLit2.o2_135k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_135k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_136k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_136k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 9) => (Tgt.t8_136k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_136k0 - (729 : ℤ) • OutLit2.o2_136k0 := by
  decide +kernel

theorem hint_136k0 : ∀ c c' : Fin 9,
    X2Nh.nh_136k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_136k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_136k0 c c' * 1 -
        OutLit2.o2_136k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_136k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_144k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_144k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 22) => (Tgt.t8_144k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_144k0 - (729 : ℤ) • OutLit2.o2_144k0 := by
  decide +kernel

theorem hint_144k0 : ∀ c c' : Fin 22,
    X2Nh.nh_144k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_144k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_144k0 c c' * 1 -
        OutLit2.o2_144k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_144k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_144k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_144k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 17) => (Tgt.t8_144k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_144k1 - (729 : ℤ) • OutLit2.o2_144k1 := by
  decide +kernel

theorem hint_144k1 : ∀ c c' : Fin 17,
    X2Nh.nh_144k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_144k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_144k1 c c' * 1 -
        OutLit2.o2_144k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_144k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_145k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_145k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 25) => (Tgt.t8_145k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_145k0 - (729 : ℤ) • OutLit2.o2_145k0 := by
  decide +kernel

theorem hint_145k0 : ∀ c c' : Fin 25,
    X2Nh.nh_145k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_145k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_145k0 c c' * 1 -
        OutLit2.o2_145k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_145k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_146k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_146k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 27) => (Tgt.t8_146k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_146k0 - (729 : ℤ) • OutLit2.o2_146k0 := by
  decide +kernel

theorem hint_146k0 : ∀ c c' : Fin 27,
    X2Nh.nh_146k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_146k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_146k0 c c' * 1 -
        OutLit2.o2_146k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_146k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_155k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_155k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 10) => (Tgt.t8_155k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_155k0 - (729 : ℤ) • OutLit2.o2_155k0 := by
  decide +kernel

theorem hint_155k0 : ∀ c c' : Fin 10,
    X2Nh.nh_155k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_155k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_155k0 c c' * 1 -
        OutLit2.o2_155k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_155k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_155k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_155k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 6) => (Tgt.t8_155k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_155k1 - (729 : ℤ) • OutLit2.o2_155k1 := by
  decide +kernel

theorem hint_155k1 : ∀ c c' : Fin 6,
    X2Nh.nh_155k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_155k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_155k1 c c' * 1 -
        OutLit2.o2_155k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_155k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_156k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_156k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 18) => (Tgt.t8_156k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_156k0 - (729 : ℤ) • OutLit2.o2_156k0 := by
  decide +kernel

theorem hint_156k0 : ∀ c c' : Fin 18,
    X2Nh.nh_156k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_156k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_156k0 c c' * 1 -
        OutLit2.o2_156k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_156k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_166k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_166k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 12) => (Tgt.t8_166k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_166k0 - (729 : ℤ) • OutLit2.o2_166k0 := by
  decide +kernel

theorem hint_166k0 : ∀ c c' : Fin 12,
    X2Nh.nh_166k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_166k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_166k0 c c' * 1 -
        OutLit2.o2_166k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_166k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_166k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_166k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 8) => (Tgt.t8_166k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_166k1 - (729 : ℤ) • OutLit2.o2_166k1 := by
  decide +kernel

theorem hint_166k1 : ∀ c c' : Fin 8,
    X2Nh.nh_166k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_166k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_166k1 c c' * 1 -
        OutLit2.o2_166k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_166k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_222k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_222k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_222k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_222k0 - (729 : ℤ) • OutLit2.o2_222k0 := by
  decide +kernel

theorem hint_222k0 : ∀ c c' : Fin 2,
    X2Nh.nh_222k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_222k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_222k0 c c' * 1 -
        OutLit2.o2_222k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_222k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_222k2 : (3584528202624742195200000 : ℤ) • X2Nh.nh_222k2 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_222k2.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_222k2 - (729 : ℤ) • OutLit2.o2_222k2 := by
  decide +kernel

theorem hint_222k2 : ∀ c c' : Fin 2,
    X2Nh.nh_222k2 c c' * 3584528202624742195200000 =
      (Tgt.t8_222k2.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_222k2 c c' * 1 -
        OutLit2.o2_222k2 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_222k2 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_223k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_223k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 5) => (Tgt.t8_223k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_223k0 - (729 : ℤ) • OutLit2.o2_223k0 := by
  decide +kernel

theorem hint_223k0 : ∀ c c' : Fin 5,
    X2Nh.nh_223k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_223k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_223k0 c c' * 1 -
        OutLit2.o2_223k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_223k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_223k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_223k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_223k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_223k1 - (729 : ℤ) • OutLit2.o2_223k1 := by
  decide +kernel

theorem hint_223k1 : ∀ c c' : Fin 2,
    X2Nh.nh_223k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_223k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_223k1 c c' * 1 -
        OutLit2.o2_223k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_223k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_224k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_224k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 11) => (Tgt.t8_224k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_224k0 - (729 : ℤ) • OutLit2.o2_224k0 := by
  decide +kernel

theorem hint_224k0 : ∀ c c' : Fin 11,
    X2Nh.nh_224k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_224k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_224k0 c c' * 1 -
        OutLit2.o2_224k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_224k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_224k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_224k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_224k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_224k1 - (729 : ℤ) • OutLit2.o2_224k1 := by
  decide +kernel

theorem hint_224k1 : ∀ c c' : Fin 7,
    X2Nh.nh_224k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_224k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_224k1 c c' * 1 -
        OutLit2.o2_224k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_224k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_225k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_225k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 8) => (Tgt.t8_225k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_225k0 - (729 : ℤ) • OutLit2.o2_225k0 := by
  decide +kernel

theorem hint_225k0 : ∀ c c' : Fin 8,
    X2Nh.nh_225k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_225k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_225k0 c c' * 1 -
        OutLit2.o2_225k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_225k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_225k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_225k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_225k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_225k1 - (729 : ℤ) • OutLit2.o2_225k1 := by
  decide +kernel

theorem hint_225k1 : ∀ c c' : Fin 4,
    X2Nh.nh_225k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_225k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_225k1 c c' * 1 -
        OutLit2.o2_225k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_225k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_226k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_226k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 6) => (Tgt.t8_226k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_226k0 - (729 : ℤ) • OutLit2.o2_226k0 := by
  decide +kernel

theorem hint_226k0 : ∀ c c' : Fin 6,
    X2Nh.nh_226k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_226k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_226k0 c c' * 1 -
        OutLit2.o2_226k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_226k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_226k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_226k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 5) => (Tgt.t8_226k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_226k1 - (729 : ℤ) • OutLit2.o2_226k1 := by
  decide +kernel

theorem hint_226k1 : ∀ c c' : Fin 5,
    X2Nh.nh_226k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_226k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_226k1 c c' * 1 -
        OutLit2.o2_226k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_226k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_233k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_233k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_233k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_233k0 - (729 : ℤ) • OutLit2.o2_233k0 := by
  decide +kernel

theorem hint_233k0 : ∀ c c' : Fin 4,
    X2Nh.nh_233k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_233k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_233k0 c c' * 1 -
        OutLit2.o2_233k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_233k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_233k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_233k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 1) => (Tgt.t8_233k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_233k1 - (729 : ℤ) • OutLit2.o2_233k1 := by
  decide +kernel

theorem hint_233k1 : ∀ c c' : Fin 1,
    X2Nh.nh_233k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_233k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_233k1 c c' * 1 -
        OutLit2.o2_233k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_233k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_234k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_234k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 16) => (Tgt.t8_234k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_234k0 - (729 : ℤ) • OutLit2.o2_234k0 := by
  decide +kernel

theorem hint_234k0 : ∀ c c' : Fin 16,
    X2Nh.nh_234k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_234k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_234k0 c c' * 1 -
        OutLit2.o2_234k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_234k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_235k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_235k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 10) => (Tgt.t8_235k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_235k0 - (729 : ℤ) • OutLit2.o2_235k0 := by
  decide +kernel

theorem hint_235k0 : ∀ c c' : Fin 10,
    X2Nh.nh_235k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_235k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_235k0 c c' * 1 -
        OutLit2.o2_235k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_235k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_236k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_236k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 11) => (Tgt.t8_236k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_236k0 - (729 : ℤ) • OutLit2.o2_236k0 := by
  decide +kernel

theorem hint_236k0 : ∀ c c' : Fin 11,
    X2Nh.nh_236k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_236k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_236k0 c c' * 1 -
        OutLit2.o2_236k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_236k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_244k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_244k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 29) => (Tgt.t8_244k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_244k0 - (729 : ℤ) • OutLit2.o2_244k0 := by
  decide +kernel

theorem hint_244k0 : ∀ c c' : Fin 29,
    X2Nh.nh_244k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_244k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_244k0 c c' * 1 -
        OutLit2.o2_244k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_244k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_244k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_244k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 20) => (Tgt.t8_244k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_244k1 - (729 : ℤ) • OutLit2.o2_244k1 := by
  decide +kernel

theorem hint_244k1 : ∀ c c' : Fin 20,
    X2Nh.nh_244k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_244k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_244k1 c c' * 1 -
        OutLit2.o2_244k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_244k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_245k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_245k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 31) => (Tgt.t8_245k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_245k0 - (729 : ℤ) • OutLit2.o2_245k0 := by
  decide +kernel

theorem hint_245k0 : ∀ c c' : Fin 31,
    X2Nh.nh_245k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_245k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_245k0 c c' * 1 -
        OutLit2.o2_245k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_245k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_246k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_246k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 34) => (Tgt.t8_246k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_246k0 - (729 : ℤ) • OutLit2.o2_246k0 := by
  decide +kernel

theorem hint_246k0 : ∀ c c' : Fin 34,
    X2Nh.nh_246k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_246k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_246k0 c c' * 1 -
        OutLit2.o2_246k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_246k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_255k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_255k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 13) => (Tgt.t8_255k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_255k0 - (729 : ℤ) • OutLit2.o2_255k0 := by
  decide +kernel

theorem hint_255k0 : ∀ c c' : Fin 13,
    X2Nh.nh_255k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_255k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_255k0 c c' * 1 -
        OutLit2.o2_255k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_255k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_255k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_255k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_255k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_255k1 - (729 : ℤ) • OutLit2.o2_255k1 := by
  decide +kernel

theorem hint_255k1 : ∀ c c' : Fin 7,
    X2Nh.nh_255k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_255k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_255k1 c c' * 1 -
        OutLit2.o2_255k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_255k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_256k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_256k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 22) => (Tgt.t8_256k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_256k0 - (729 : ℤ) • OutLit2.o2_256k0 := by
  decide +kernel

theorem hint_256k0 : ∀ c c' : Fin 22,
    X2Nh.nh_256k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_256k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_256k0 c c' * 1 -
        OutLit2.o2_256k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_256k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_266k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_266k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 16) => (Tgt.t8_266k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_266k0 - (729 : ℤ) • OutLit2.o2_266k0 := by
  decide +kernel

theorem hint_266k0 : ∀ c c' : Fin 16,
    X2Nh.nh_266k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_266k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_266k0 c c' * 1 -
        OutLit2.o2_266k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_266k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_266k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_266k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 9) => (Tgt.t8_266k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_266k1 - (729 : ℤ) • OutLit2.o2_266k1 := by
  decide +kernel

theorem hint_266k1 : ∀ c c' : Fin 9,
    X2Nh.nh_266k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_266k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_266k1 c c' * 1 -
        OutLit2.o2_266k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_266k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_333k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_333k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_333k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_333k0 - (729 : ℤ) • OutLit2.o2_333k0 := by
  decide +kernel

theorem hint_333k0 : ∀ c c' : Fin 2,
    X2Nh.nh_333k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_333k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_333k0 c c' * 1 -
        OutLit2.o2_333k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_333k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_333k2 : (3584528202624742195200000 : ℤ) • X2Nh.nh_333k2 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 2) => (Tgt.t8_333k2.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_333k2 - (729 : ℤ) • OutLit2.o2_333k2 := by
  decide +kernel

theorem hint_333k2 : ∀ c c' : Fin 2,
    X2Nh.nh_333k2 c c' * 3584528202624742195200000 =
      (Tgt.t8_333k2.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_333k2 c c' * 1 -
        OutLit2.o2_333k2 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_333k2 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_334k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_334k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 10) => (Tgt.t8_334k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_334k0 - (729 : ℤ) • OutLit2.o2_334k0 := by
  decide +kernel

theorem hint_334k0 : ∀ c c' : Fin 10,
    X2Nh.nh_334k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_334k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_334k0 c c' * 1 -
        OutLit2.o2_334k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_334k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_334k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_334k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 6) => (Tgt.t8_334k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_334k1 - (729 : ℤ) • OutLit2.o2_334k1 := by
  decide +kernel

theorem hint_334k1 : ∀ c c' : Fin 6,
    X2Nh.nh_334k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_334k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_334k1 c c' * 1 -
        OutLit2.o2_334k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_334k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_335k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_335k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_335k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_335k0 - (729 : ℤ) • OutLit2.o2_335k0 := by
  decide +kernel

theorem hint_335k0 : ∀ c c' : Fin 7,
    X2Nh.nh_335k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_335k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_335k0 c c' * 1 -
        OutLit2.o2_335k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_335k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_335k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_335k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_335k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_335k1 - (729 : ℤ) • OutLit2.o2_335k1 := by
  decide +kernel

theorem hint_335k1 : ∀ c c' : Fin 4,
    X2Nh.nh_335k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_335k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_335k1 c c' * 1 -
        OutLit2.o2_335k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_335k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_336k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_336k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 6) => (Tgt.t8_336k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_336k0 - (729 : ℤ) • OutLit2.o2_336k0 := by
  decide +kernel

theorem hint_336k0 : ∀ c c' : Fin 6,
    X2Nh.nh_336k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_336k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_336k0 c c' * 1 -
        OutLit2.o2_336k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_336k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_336k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_336k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 5) => (Tgt.t8_336k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_336k1 - (729 : ℤ) • OutLit2.o2_336k1 := by
  decide +kernel

theorem hint_336k1 : ∀ c c' : Fin 5,
    X2Nh.nh_336k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_336k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_336k1 c c' * 1 -
        OutLit2.o2_336k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_336k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_344k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_344k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 27) => (Tgt.t8_344k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_344k0 - (729 : ℤ) • OutLit2.o2_344k0 := by
  decide +kernel

theorem hint_344k0 : ∀ c c' : Fin 27,
    X2Nh.nh_344k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_344k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_344k0 c c' * 1 -
        OutLit2.o2_344k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_344k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_344k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_344k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 21) => (Tgt.t8_344k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_344k1 - (729 : ℤ) • OutLit2.o2_344k1 := by
  decide +kernel

theorem hint_344k1 : ∀ c c' : Fin 21,
    X2Nh.nh_344k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_344k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_344k1 c c' * 1 -
        OutLit2.o2_344k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_344k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_345k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_345k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 31) => (Tgt.t8_345k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_345k0 - (729 : ℤ) • OutLit2.o2_345k0 := by
  decide +kernel

theorem hint_345k0 : ∀ c c' : Fin 31,
    X2Nh.nh_345k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_345k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_345k0 c c' * 1 -
        OutLit2.o2_345k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_345k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_346k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_346k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 34) => (Tgt.t8_346k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_346k0 - (729 : ℤ) • OutLit2.o2_346k0 := by
  decide +kernel

theorem hint_346k0 : ∀ c c' : Fin 34,
    X2Nh.nh_346k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_346k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_346k0 c c' * 1 -
        OutLit2.o2_346k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_346k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_355k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_355k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 13) => (Tgt.t8_355k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_355k0 - (729 : ℤ) • OutLit2.o2_355k0 := by
  decide +kernel

theorem hint_355k0 : ∀ c c' : Fin 13,
    X2Nh.nh_355k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_355k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_355k0 c c' * 1 -
        OutLit2.o2_355k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_355k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_355k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_355k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 9) => (Tgt.t8_355k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_355k1 - (729 : ℤ) • OutLit2.o2_355k1 := by
  decide +kernel

theorem hint_355k1 : ∀ c c' : Fin 9,
    X2Nh.nh_355k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_355k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_355k1 c c' * 1 -
        OutLit2.o2_355k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_355k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_356k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_356k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 23) => (Tgt.t8_356k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_356k0 - (729 : ℤ) • OutLit2.o2_356k0 := by
  decide +kernel

theorem hint_356k0 : ∀ c c' : Fin 23,
    X2Nh.nh_356k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_356k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_356k0 c c' * 1 -
        OutLit2.o2_356k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_356k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_366k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_366k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 15) => (Tgt.t8_366k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_366k0 - (729 : ℤ) • OutLit2.o2_366k0 := by
  decide +kernel

theorem hint_366k0 : ∀ c c' : Fin 15,
    X2Nh.nh_366k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_366k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_366k0 c c' * 1 -
        OutLit2.o2_366k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_366k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_366k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_366k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 11) => (Tgt.t8_366k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_366k1 - (729 : ℤ) • OutLit2.o2_366k1 := by
  decide +kernel

theorem hint_366k1 : ∀ c c' : Fin 11,
    X2Nh.nh_366k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_366k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_366k1 c c' * 1 -
        OutLit2.o2_366k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_366k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_444k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_444k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 29) => (Tgt.t8_444k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_444k0 - (729 : ℤ) • OutLit2.o2_444k0 := by
  decide +kernel

theorem hint_444k0 : ∀ c c' : Fin 29,
    X2Nh.nh_444k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_444k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_444k0 c c' * 1 -
        OutLit2.o2_444k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_444k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_444k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_444k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 18) => (Tgt.t8_444k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_444k1 - (729 : ℤ) • OutLit2.o2_444k1 := by
  decide +kernel

theorem hint_444k1 : ∀ c c' : Fin 18,
    X2Nh.nh_444k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_444k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_444k1 c c' * 1 -
        OutLit2.o2_444k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_444k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_444k2 : (3584528202624742195200000 : ℤ) • X2Nh.nh_444k2 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 48) => (Tgt.t8_444k2.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_444k2 - (729 : ℤ) • OutLit2.o2_444k2 := by
  decide +kernel

theorem hint_444k2 : ∀ c c' : Fin 48,
    X2Nh.nh_444k2 c c' * 3584528202624742195200000 =
      (Tgt.t8_444k2.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_444k2 c c' * 1 -
        OutLit2.o2_444k2 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_444k2 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_445k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_445k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 52) => (Tgt.t8_445k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_445k0 - (729 : ℤ) • OutLit2.o2_445k0 := by
  decide +kernel

theorem hint_445k0 : ∀ c c' : Fin 52,
    X2Nh.nh_445k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_445k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_445k0 c c' * 1 -
        OutLit2.o2_445k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_445k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_445k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_445k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 42) => (Tgt.t8_445k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_445k1 - (729 : ℤ) • OutLit2.o2_445k1 := by
  decide +kernel

theorem hint_445k1 : ∀ c c' : Fin 42,
    X2Nh.nh_445k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_445k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_445k1 c c' * 1 -
        OutLit2.o2_445k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_445k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_446k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_446k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 53) => (Tgt.t8_446k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_446k0 - (729 : ℤ) • OutLit2.o2_446k0 := by
  decide +kernel

theorem hint_446k0 : ∀ c c' : Fin 53,
    X2Nh.nh_446k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_446k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_446k0 c c' * 1 -
        OutLit2.o2_446k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_446k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_446k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_446k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 49) => (Tgt.t8_446k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_446k1 - (729 : ℤ) • OutLit2.o2_446k1 := by
  decide +kernel

theorem hint_446k1 : ∀ c c' : Fin 49,
    X2Nh.nh_446k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_446k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_446k1 c c' * 1 -
        OutLit2.o2_446k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_446k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_455k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_455k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 35) => (Tgt.t8_455k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_455k0 - (729 : ℤ) • OutLit2.o2_455k0 := by
  decide +kernel

theorem hint_455k0 : ∀ c c' : Fin 35,
    X2Nh.nh_455k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_455k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_455k0 c c' * 1 -
        OutLit2.o2_455k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_455k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_455k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_455k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 27) => (Tgt.t8_455k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_455k1 - (729 : ℤ) • OutLit2.o2_455k1 := by
  decide +kernel

theorem hint_455k1 : ∀ c c' : Fin 27,
    X2Nh.nh_455k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_455k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_455k1 c c' * 1 -
        OutLit2.o2_455k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_455k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_456k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_456k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 69) => (Tgt.t8_456k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_456k0 - (729 : ℤ) • OutLit2.o2_456k0 := by
  decide +kernel

theorem hint_456k0 : ∀ c c' : Fin 69,
    X2Nh.nh_456k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_456k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_456k0 c c' * 1 -
        OutLit2.o2_456k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_456k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_466k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_466k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 42) => (Tgt.t8_466k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_466k0 - (729 : ℤ) • OutLit2.o2_466k0 := by
  decide +kernel

theorem hint_466k0 : ∀ c c' : Fin 42,
    X2Nh.nh_466k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_466k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_466k0 c c' * 1 -
        OutLit2.o2_466k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_466k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_466k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_466k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 34) => (Tgt.t8_466k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_466k1 - (729 : ℤ) • OutLit2.o2_466k1 := by
  decide +kernel

theorem hint_466k1 : ∀ c c' : Fin 34,
    X2Nh.nh_466k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_466k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_466k1 c c' * 1 -
        OutLit2.o2_466k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_466k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_555k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_555k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 10) => (Tgt.t8_555k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_555k0 - (729 : ℤ) • OutLit2.o2_555k0 := by
  decide +kernel

theorem hint_555k0 : ∀ c c' : Fin 10,
    X2Nh.nh_555k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_555k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_555k0 c c' * 1 -
        OutLit2.o2_555k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_555k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_555k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_555k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 4) => (Tgt.t8_555k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_555k1 - (729 : ℤ) • OutLit2.o2_555k1 := by
  decide +kernel

theorem hint_555k1 : ∀ c c' : Fin 4,
    X2Nh.nh_555k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_555k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_555k1 c c' * 1 -
        OutLit2.o2_555k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_555k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_555k2 : (3584528202624742195200000 : ℤ) • X2Nh.nh_555k2 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 15) => (Tgt.t8_555k2.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_555k2 - (729 : ℤ) • OutLit2.o2_555k2 := by
  decide +kernel

theorem hint_555k2 : ∀ c c' : Fin 15,
    X2Nh.nh_555k2 c c' * 3584528202624742195200000 =
      (Tgt.t8_555k2.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_555k2 c c' * 1 -
        OutLit2.o2_555k2 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_555k2 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_556k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_556k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 24) => (Tgt.t8_556k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_556k0 - (729 : ℤ) • OutLit2.o2_556k0 := by
  decide +kernel

theorem hint_556k0 : ∀ c c' : Fin 24,
    X2Nh.nh_556k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_556k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_556k0 c c' * 1 -
        OutLit2.o2_556k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_556k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_556k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_556k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 22) => (Tgt.t8_556k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_556k1 - (729 : ℤ) • OutLit2.o2_556k1 := by
  decide +kernel

theorem hint_556k1 : ∀ c c' : Fin 22,
    X2Nh.nh_556k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_556k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_556k1 c c' * 1 -
        OutLit2.o2_556k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_556k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_566k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_566k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 29) => (Tgt.t8_566k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_566k0 - (729 : ℤ) • OutLit2.o2_566k0 := by
  decide +kernel

theorem hint_566k0 : ∀ c c' : Fin 29,
    X2Nh.nh_566k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_566k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_566k0 c c' * 1 -
        OutLit2.o2_566k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_566k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_566k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_566k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 22) => (Tgt.t8_566k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_566k1 - (729 : ℤ) • OutLit2.o2_566k1 := by
  decide +kernel

theorem hint_566k1 : ∀ c c' : Fin 22,
    X2Nh.nh_566k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_566k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_566k1 c c' * 1 -
        OutLit2.o2_566k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_566k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_666k0 : (3584528202624742195200000 : ℤ) • X2Nh.nh_666k0 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 10) => (Tgt.t8_666k0.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_666k0 - (729 : ℤ) • OutLit2.o2_666k0 := by
  decide +kernel

theorem hint_666k0 : ∀ c c' : Fin 10,
    X2Nh.nh_666k0 c c' * 3584528202624742195200000 =
      (Tgt.t8_666k0.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_666k0 c c' * 1 -
        OutLit2.o2_666k0 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_666k0 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_666k1 : (3584528202624742195200000 : ℤ) • X2Nh.nh_666k1 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 7) => (Tgt.t8_666k1.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_666k1 - (729 : ℤ) • OutLit2.o2_666k1 := by
  decide +kernel

theorem hint_666k1 : ∀ c c' : Fin 7,
    X2Nh.nh_666k1 c c' * 3584528202624742195200000 =
      (Tgt.t8_666k1.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_666k1 c c' * 1 -
        OutLit2.o2_666k1 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_666k1 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

theorem hintM_666k2 : (3584528202624742195200000 : ℤ) • X2Nh.nh_666k2 =
    (25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 : ℤ) • (Matrix.of fun (c c' : Fin 19) => (Tgt.t8_666k2.getD c []).getD c' 0) -
      (1 : ℤ) • OutLit1.o1_666k2 - (729 : ℤ) • OutLit2.o2_666k2 := by
  decide +kernel

theorem hint_666k2 : ∀ c c' : Fin 19,
    X2Nh.nh_666k2 c c' * 3584528202624742195200000 =
      (Tgt.t8_666k2.getD c []).getD c' 0 * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - OutLit1.o1_666k2 c c' * 1 -
        OutLit2.o2_666k2 c c' * 729 := by
  intro c c'
  have h := congrFun (congrFun hintM_666k2 c) c'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at h
  linarith

/-- The integer identities of all 122 blocks. -/
theorem x2_hint : ∀ b : x2Key 0, ∀ c c' : x2Col 0 b,
    x2NhLit b c c' * 3584528202624742195200000 = x2TgtLit b c c' * 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 - x2OLit1 b c c' * 1 - x2OLit2 b c c' * 729
  | ⟨0, _⟩ => hint_003k0
  | ⟨1, _⟩ => hint_004k0
  | ⟨2, _⟩ => hint_005k0
  | ⟨3, _⟩ => hint_011k0
  | ⟨4, _⟩ => hint_012k0
  | ⟨5, _⟩ => hint_013k0
  | ⟨6, _⟩ => hint_014k0
  | ⟨7, _⟩ => hint_015k0
  | ⟨8, _⟩ => hint_016k0
  | ⟨9, _⟩ => hint_022k0
  | ⟨10, _⟩ => hint_023k0
  | ⟨11, _⟩ => hint_024k0
  | ⟨12, _⟩ => hint_025k0
  | ⟨13, _⟩ => hint_026k0
  | ⟨14, _⟩ => hint_033k0
  | ⟨15, _⟩ => hint_034k0
  | ⟨16, _⟩ => hint_035k0
  | ⟨17, _⟩ => hint_036k0
  | ⟨18, _⟩ => hint_044k0
  | ⟨19, _⟩ => hint_044k1
  | ⟨20, _⟩ => hint_045k0
  | ⟨21, _⟩ => hint_046k0
  | ⟨22, _⟩ => hint_055k0
  | ⟨23, _⟩ => hint_055k1
  | ⟨24, _⟩ => hint_056k0
  | ⟨25, _⟩ => hint_066k0
  | ⟨26, _⟩ => hint_066k1
  | ⟨27, _⟩ => hint_111k0
  | ⟨28, _⟩ => hint_111k2
  | ⟨29, _⟩ => hint_112k0
  | ⟨30, _⟩ => hint_112k1
  | ⟨31, _⟩ => hint_113k0
  | ⟨32, _⟩ => hint_113k1
  | ⟨33, _⟩ => hint_114k0
  | ⟨34, _⟩ => hint_114k1
  | ⟨35, _⟩ => hint_115k0
  | ⟨36, _⟩ => hint_115k1
  | ⟨37, _⟩ => hint_116k0
  | ⟨38, _⟩ => hint_116k1
  | ⟨39, _⟩ => hint_122k0
  | ⟨40, _⟩ => hint_122k1
  | ⟨41, _⟩ => hint_123k0
  | ⟨42, _⟩ => hint_124k0
  | ⟨43, _⟩ => hint_125k0
  | ⟨44, _⟩ => hint_126k0
  | ⟨45, _⟩ => hint_133k0
  | ⟨46, _⟩ => hint_133k1
  | ⟨47, _⟩ => hint_134k0
  | ⟨48, _⟩ => hint_135k0
  | ⟨49, _⟩ => hint_136k0
  | ⟨50, _⟩ => hint_144k0
  | ⟨51, _⟩ => hint_144k1
  | ⟨52, _⟩ => hint_145k0
  | ⟨53, _⟩ => hint_146k0
  | ⟨54, _⟩ => hint_155k0
  | ⟨55, _⟩ => hint_155k1
  | ⟨56, _⟩ => hint_156k0
  | ⟨57, _⟩ => hint_166k0
  | ⟨58, _⟩ => hint_166k1
  | ⟨59, _⟩ => hint_222k0
  | ⟨60, _⟩ => hint_222k2
  | ⟨61, _⟩ => hint_223k0
  | ⟨62, _⟩ => hint_223k1
  | ⟨63, _⟩ => hint_224k0
  | ⟨64, _⟩ => hint_224k1
  | ⟨65, _⟩ => hint_225k0
  | ⟨66, _⟩ => hint_225k1
  | ⟨67, _⟩ => hint_226k0
  | ⟨68, _⟩ => hint_226k1
  | ⟨69, _⟩ => hint_233k0
  | ⟨70, _⟩ => hint_233k1
  | ⟨71, _⟩ => hint_234k0
  | ⟨72, _⟩ => hint_235k0
  | ⟨73, _⟩ => hint_236k0
  | ⟨74, _⟩ => hint_244k0
  | ⟨75, _⟩ => hint_244k1
  | ⟨76, _⟩ => hint_245k0
  | ⟨77, _⟩ => hint_246k0
  | ⟨78, _⟩ => hint_255k0
  | ⟨79, _⟩ => hint_255k1
  | ⟨80, _⟩ => hint_256k0
  | ⟨81, _⟩ => hint_266k0
  | ⟨82, _⟩ => hint_266k1
  | ⟨83, _⟩ => hint_333k0
  | ⟨84, _⟩ => hint_333k2
  | ⟨85, _⟩ => hint_334k0
  | ⟨86, _⟩ => hint_334k1
  | ⟨87, _⟩ => hint_335k0
  | ⟨88, _⟩ => hint_335k1
  | ⟨89, _⟩ => hint_336k0
  | ⟨90, _⟩ => hint_336k1
  | ⟨91, _⟩ => hint_344k0
  | ⟨92, _⟩ => hint_344k1
  | ⟨93, _⟩ => hint_345k0
  | ⟨94, _⟩ => hint_346k0
  | ⟨95, _⟩ => hint_355k0
  | ⟨96, _⟩ => hint_355k1
  | ⟨97, _⟩ => hint_356k0
  | ⟨98, _⟩ => hint_366k0
  | ⟨99, _⟩ => hint_366k1
  | ⟨100, _⟩ => hint_444k0
  | ⟨101, _⟩ => hint_444k1
  | ⟨102, _⟩ => hint_444k2
  | ⟨103, _⟩ => hint_445k0
  | ⟨104, _⟩ => hint_445k1
  | ⟨105, _⟩ => hint_446k0
  | ⟨106, _⟩ => hint_446k1
  | ⟨107, _⟩ => hint_455k0
  | ⟨108, _⟩ => hint_455k1
  | ⟨109, _⟩ => hint_456k0
  | ⟨110, _⟩ => hint_466k0
  | ⟨111, _⟩ => hint_466k1
  | ⟨112, _⟩ => hint_555k0
  | ⟨113, _⟩ => hint_555k1
  | ⟨114, _⟩ => hint_555k2
  | ⟨115, _⟩ => hint_556k0
  | ⟨116, _⟩ => hint_556k1
  | ⟨117, _⟩ => hint_566k0
  | ⟨118, _⟩ => hint_566k1
  | ⟨119, _⟩ => hint_666k0
  | ⟨120, _⟩ => hint_666k1
  | ⟨121, _⟩ => hint_666k2
  | ⟨k + 122, h⟩ => False.elim (by have h122 : x2NumKeys 0 = 122 := rfl; omega)

/-- THE RESIDUAL BLOCKS from the two sectors' outputs (corrected sources, concrete data). -/
theorem x2Residual_family (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (h1 : ∀ b : x2Key 0, x2Out x2DataConcrete 1 Nm b =
      Matrix.of fun (c c' : x2Col 0 b) => ((x2OLit1 b c c' : ℤ) : ℚ) / ((206956289055859274695422315107442708940202250654556041696680864486258286526464000000000 : ℕ) : ℚ))
    (h2 : ∀ b : x2Key 0, x2Out x2DataConcrete 2 Na b =
      Matrix.of fun (c c' : x2Col 0 b) => ((x2OLit2 b c c' : ℤ) : ℚ) / ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ)) :
    ∀ b : x2Key 0, x2Residual x2DataConcrete Nm Na b =
      (1 / ((X2Nh.den : ℕ) : ℚ)) • (x2NhLit b).map (Int.cast : ℤ → ℚ) := fun b =>
  x2Residual_eq_fam x2DataConcrete Nm Na b (x2TgtLit b) (x2OLit1 b) (x2OLit2 b) (x2NhLit b) 206956289055859274695422315107442708940202250654556041696680864486258286526464000000000 283890657141096398759152695620634717339097737523396490667600637155361161216000000000 X2Nh.den
    3584528202624742195200000 25869536131982409336927789388430338617525281331819505212085108060782285815808000000000 1 729 (by unfold X2Nh.den; norm_num) (by norm_num) (by unfold X2Nh.den; norm_num)
    (by unfold X2Nh.den; norm_num) (by unfold X2Nh.den; norm_num) (x2Target_concrete b) (h1 b) (h2 b) (x2_hint b)

end ThreeCopyQutritWerner.X2
