module

public import CFSG.Certificates.Kernel.TwoAC.Fact
public import CFSG.Certificates.Kernel.TwoAC.Sound
public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Certificates.Kernel.BabyMonster.FixSound
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import Certificates.Kernel.BabyMonster.ForallLt
public import Certificates.Kernel.BabyMonster.FiveA.RankLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Certificates.Kernel.TwoAC.Check0
public import Certificates.Kernel.TwoAC.Check1
public import Certificates.Kernel.TwoAC.Check2
public import Certificates.Kernel.TwoAC.Wf
public import CFSG.Certificates.Kernel.BabyMonster.Sound

public section

namespace CertificateChecks.KernelTwoAC

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BM.SL CertificateChecks.KernelBM.FiveA Module
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "mA" => stripMat CFSG.KC.BM.Seeds.A1
local notation "mB" => stripMat CFSG.KC.BM.Seeds.A2

set_option maxRecDepth 100000

theorem mul1 {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : stripMat A * stripMat B = stripMat C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h

theorem one1 {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : stripMat A * stripMat B = 1 := by
  simpa using stripMat_mul_eq_one (Ws := [B]) (by simp [hB]) hA h

theorem stripMat_idStrips : stripMat idStrips = 1 := by
  rw [stripMat_eq]
  exact stripMatG_id (by norm_num) idStrips_eq

theorem mulC (C : List Nat) {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : stripMat A * stripMat B = stripMat C := mul1 hA hB h

theorem e_B2 : stripMat TwoAC.B2 = mB ^ 2 := by
  rw [← mulC TwoAC.B2 Seeds.wf_A2 Seeds.wf_A2 (by bm_strips4 CFSG.KC.BM.TwoAC.cB2 69), sq]

theorem e_p : stripMat TwoAC.p = mA * mB ^ 2 := by
  rw [← mulC TwoAC.p Seeds.wf_A1 TwoAC.wf_B2 (by bm_strips4 CFSG.KC.BM.TwoAC.cp 69), e_B2]

theorem e_q : stripMat TwoAC.q = mA * mB :=
  (mulC TwoAC.q Seeds.wf_A1 Seeds.wf_A2 (by bm_strips4 CFSG.KC.BM.TwoAC.cq 69)).symm

theorem e_w : stripMat TwoAC.w = TwoAC.wW mA mB := by
  rw [← mulC TwoAC.w TwoAC.wf_ss TwoAC.wf_p (by bm_strips4 CFSG.KC.BM.TwoAC.cw 69),
    ← mulC TwoAC.ss TwoAC.wf_s TwoAC.wf_s (by bm_strips4 CFSG.KC.BM.TwoAC.css 69),
    ← mulC TwoAC.s TwoAC.wf_pq TwoAC.wf_p (by bm_strips4 CFSG.KC.BM.TwoAC.cs 69),
    ← mulC TwoAC.pq TwoAC.wf_p TwoAC.wf_q (by bm_strips4 CFSG.KC.BM.TwoAC.cpq 69), e_p, e_q,
    TwoAC.wW]
  simp only [mul_assoc]

theorem e_w2 : stripMat TwoAC.w2 = TwoAC.wW mA mB ^ 2 := by
  rw [← mulC TwoAC.w2 TwoAC.wf_w TwoAC.wf_w (by bm_strips4 CFSG.KC.BM.TwoAC.cw2 69), e_w, sq]

theorem e_w4 : stripMat TwoAC.w4 = TwoAC.wW mA mB ^ 4 := by
  rw [← mulC TwoAC.w4 TwoAC.wf_w2 TwoAC.wf_w2 (by bm_strips4 CFSG.KC.BM.TwoAC.cw4 69), e_w2,
    ← pow_add]

theorem e_w8 : stripMat TwoAC.w8 = TwoAC.wW mA mB ^ 8 := by
  rw [← mulC TwoAC.w8 TwoAC.wf_w4 TwoAC.wf_w4 (by bm_strips4 CFSG.KC.BM.TwoAC.cw8 69), e_w4,
    ← pow_add]

theorem e_w16 : stripMat TwoAC.w16 = TwoAC.wW mA mB ^ 16 := by
  rw [← mulC TwoAC.w16 TwoAC.wf_w8 TwoAC.wf_w8 (by bm_strips4 CFSG.KC.BM.TwoAC.cw16 69), e_w8,
    ← pow_add]

theorem e_x : stripMat TwoAC.x = TwoAC.xW mA mB := by
  rw [← mulC TwoAC.x TwoAC.wf_w16 TwoAC.wf_w (by bm_strips4 CFSG.KC.BM.TwoAC.cx 69), e_w16, e_w,
    ← pow_succ, TwoAC.xW]

theorem e_b : stripMat TwoAC.w2 = TwoAC.bW mA mB := by rw [e_w2, TwoAC.bW]

theorem e_g : stripMat TwoAC.g = TwoAC.gW mA mB := by
  rw [← mulC TwoAC.g TwoAC.wf_B2 TwoAC.wf_q2 (by bm_strips4 CFSG.KC.BM.TwoAC.cg 69),
    ← mulC TwoAC.q2 TwoAC.wf_q TwoAC.wf_q (by bm_strips4 CFSG.KC.BM.TwoAC.cq2 69), e_B2, e_q,
    TwoAC.gW]
  simp only [mul_assoc]

theorem e_gi : stripMat TwoAC.gi = TwoAC.hW mA mB := by
  rw [← mulC TwoAC.gi TwoAC.wf_B2p TwoAC.wf_q (by bm_strips4 CFSG.KC.BM.TwoAC.cgi 69),
    ← mulC TwoAC.B2p TwoAC.wf_B2 TwoAC.wf_p (by bm_strips4 CFSG.KC.BM.TwoAC.cB2p 69), e_B2, e_p,
    e_q, TwoAC.hW]
  simp only [mul_assoc]

theorem e_a : stripMat TwoAC.a = TwoAC.aW mA mB := by
  rw [← mulC TwoAC.a TwoAC.wf_r28 TwoAC.wf_r28 (by bm_strips4 CFSG.KC.BM.TwoAC.ca 69),
    ← mulC TwoAC.r28 TwoAC.wf_xgix TwoAC.wf_g (by bm_strips4 CFSG.KC.BM.TwoAC.cr28 69),
    ← mulC TwoAC.xgix TwoAC.wf_xgi TwoAC.wf_x (by bm_strips4 CFSG.KC.BM.TwoAC.cxgix 69),
    ← mulC TwoAC.xgi TwoAC.wf_x TwoAC.wf_gi (by bm_strips4 CFSG.KC.BM.TwoAC.cxgi 69), e_x, e_gi,
    e_g, ← sq, TwoAC.aW]

theorem e_ab : stripMat TwoAC.ab = TwoAC.aW mA mB * TwoAC.bW mA mB := by
  rw [← mulC TwoAC.ab TwoAC.wf_a TwoAC.wf_w2 (by bm_strips4 CFSG.KC.BM.TwoAC.cab 69), e_a, e_b]

theorem x_sq : TwoAC.xW mA mB ^ 2 = 1 := by
  rw [← e_x, sq, one1 TwoAC.wf_x TwoAC.wf_x (by bm_strips4 CFSG.KC.BM.TwoAC.cxx 69)]

theorem a_sq : TwoAC.aW mA mB ^ 2 = 1 := by
  rw [← e_a, sq, one1 TwoAC.wf_a TwoAC.wf_a (by bm_strips4 CFSG.KC.BM.TwoAC.caa 69)]

theorem g_gi : TwoAC.gW mA mB * TwoAC.hW mA mB = 1 := by
  rw [← e_g, ← e_gi, one1 TwoAC.wf_g TwoAC.wf_gi (by bm_strips4 CFSG.KC.BM.TwoAC.cggi 69)]

theorem ab_pow : (TwoAC.aW mA mB * TwoAC.bW mA mB) ^ 13 = 1 := by
  have e2 := mulC TwoAC.ab2 TwoAC.wf_ab TwoAC.wf_ab (by bm_strips4 CFSG.KC.BM.TwoAC.cab2 69)
  have e4 := mulC TwoAC.ab4 TwoAC.wf_ab2 TwoAC.wf_ab2 (by bm_strips4 CFSG.KC.BM.TwoAC.cab4 69)
  have e8 := mulC TwoAC.ab8 TwoAC.wf_ab4 TwoAC.wf_ab4 (by bm_strips4 CFSG.KC.BM.TwoAC.cab8 69)
  have e12 := mulC TwoAC.ab12 TwoAC.wf_ab8 TwoAC.wf_ab4
    (by bm_strips4 CFSG.KC.BM.TwoAC.cab12 69)
  have e := one1 TwoAC.wf_ab12 TwoAC.wf_ab (by bm_strips4 CFSG.KC.BM.TwoAC.cab13 69)
  have h2 : stripMat TwoAC.ab2 = (TwoAC.aW mA mB * TwoAC.bW mA mB) ^ 2 := by
    rw [← e2, e_ab, sq]
  have h4 : stripMat TwoAC.ab4 = (TwoAC.aW mA mB * TwoAC.bW mA mB) ^ 4 := by
    rw [← e4, h2, ← pow_add]
  have h8 : stripMat TwoAC.ab8 = (TwoAC.aW mA mB * TwoAC.bW mA mB) ^ 8 := by
    rw [← e8, h4, ← pow_add]
  have h12 : stripMat TwoAC.ab12 = (TwoAC.aW mA mB * TwoAC.bW mA mB) ^ 12 := by
    rw [← e12, h8, h4, ← pow_add]
  rw [h12, e_ab, ← pow_succ] at e
  exact e

theorem b_pow : TwoAC.bW mA mB ^ 17 = 1 := by
  rw [TwoAC.bW, ← pow_mul, show 2 * 17 = 17 * 2 by norm_num, pow_mul, ← TwoAC.xW, x_sq]

theorem b_comm : TwoAC.bW mA mB * TwoAC.xW mA mB = TwoAC.xW mA mB * TwoAC.bW mA mB := by
  rw [TwoAC.bW, TwoAC.xW, ← pow_add, ← pow_add, add_comm]

theorem comm_of_inv {G : Type*} [Group G] (X Y : G) (hX : X * X = 1) (hY : Y * Y = 1)
    (h : (X * Y) ^ 2 * (X * Y) ^ 2 = 1) : (X * Y) ^ 2 * X = X * (X * Y) ^ 2 := by
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX
  have hYi : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY
  have e1 : (X * Y) ^ 2 = Y * X * Y * X := by
    rw [eq_inv_of_mul_eq_one_left h, sq, mul_inv_rev, mul_inv_rev, hXi, hYi]
    simp only [mul_assoc]
  calc (X * Y) ^ 2 * X = Y * X * Y * (X * X) := by rw [e1]; simp only [mul_assoc]
    _ = X * X * (Y * X * Y) := by rw [hX, mul_one, one_mul]
    _ = X * (X * Y) ^ 2 := by rw [sq]; simp only [mul_assoc]

theorem a_comm : TwoAC.aW mA mB * TwoAC.xW mA mB = TwoAC.xW mA mB * TwoAC.aW mA mB := by
  have hxx : TwoAC.xW mA mB * TwoAC.xW mA mB = 1 := by rw [← sq, x_sq]
  have hgg := g_gi
  have hgg' : TwoAC.hW mA mB * TwoAC.gW mA mB = 1 := by
    rw [← Matrix.inv_eq_right_inv hgg]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse hgg)
  let X : MatBˣ := ⟨TwoAC.xW mA mB, TwoAC.xW mA mB, hxx, hxx⟩
  let G : MatBˣ := ⟨TwoAC.gW mA mB, TwoAC.hW mA mB, hgg, hgg'⟩
  have hX : X * X = 1 := Units.ext hxx
  have hY : (G⁻¹ * X * G) * (G⁻¹ * X * G) = 1 := by
    rw [show G⁻¹ * X * G * (G⁻¹ * X * G) = G⁻¹ * (X * X) * G by group, hX]
    group
  have h4 : (TwoAC.xW mA mB * (TwoAC.hW mA mB * (TwoAC.xW mA mB * TwoAC.gW mA mB))) ^ 4 = 1 := by
    have := a_sq
    rw [TwoAC.aW, ← pow_mul] at this
    simpa only [mul_assoc] using this
  have ha : (X * (G⁻¹ * X * G)) ^ 2 * (X * (G⁻¹ * X * G)) ^ 2 = 1 := by
    rw [Units.ext_iff]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, X, G, Units.inv_mk]
    rw [← pow_add]
    simpa only [mul_assoc] using h4
  have e := congrArg Units.val (comm_of_inv X (G⁻¹ * X * G) hX hY ha)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, X, G, Units.inv_mk] at e
  rw [TwoAC.aW]
  simpa only [mul_assoc] using e

theorem rank_of_cert {M P R : List Nat} {k : ℕ} (hk : k ≤ 4370) (hM : wfMat M = true)
    (hP : wfMat P = true) (hR : wfMat R = true) (hrk : AllStrips [M] P R)
    (hs : shapeOK R k = true) (he : echFrom P k = true) : (stripMat M).rank = k := by
  have hmul := mul1 hP hM hrk
  have hs' := shapeOK_sound hR hs
  have he' := echFrom_sound hP he
  apply le_antisymm
  · have hK := card_le_kerL (A := stripMat M)
      (fun i : {i : Fin 4370 // k ≤ i.val} => stripMat P i)
      (fun i => by rw [← rowMul, hmul]; exact hs'.2 i i.2) he'
    rw [card_ge 4370 k hk] at hK
    have := finrank_kerL (stripMat M)
    omega
  · have h1 := card_le_rank (A := stripMat R) (fun i : {i : Fin 4370 // i.val < k} => i.1) hs'.1
    rw [card_lt 4370 k hk, ← hmul] at h1
    exact h1.trans (Matrix.rank_mul_le_right _ _)

theorem le_rank_of_shape {M P R : List Nat} {k : ℕ} (hk : k ≤ 4370) (hM : wfMat M = true)
    (hP : wfMat P = true) (hR : wfMat R = true) (hrk : AllStrips [M] P R)
    (hs : shapeOK R k = true) : k ≤ (stripMat M).rank := by
  have hmul := mul1 hP hM hrk
  have h1 := card_le_rank (A := stripMat R) (fun i : {i : Fin 4370 // i.val < k} => i.1)
    (shapeOK_sound hR hs).1
  rw [card_lt 4370 k hk, ← hmul] at h1
  exact h1.trans (Matrix.rank_mul_le_right _ _)

theorem x_rank : (TwoAC.xW mA mB - 1).rank = 1860 := by
  have hX1 : stripMat TwoAC.X1 = stripMat TwoAC.x + 1 := by
    rw [TwoAC.xorRowL_sound (T := TwoAC.X1) (As := [TwoAC.x, idStrips])
      (by forall_lt_consts CFSG.KC.BM.TwoAC.xX1_ 69)]
    simp [stripMat_idStrips]
  have e : TwoAC.xW mA mB - 1 = stripMat TwoAC.X1 := by
    rw [hX1, e_x]
    ext i j
    rw [Matrix.sub_apply, Matrix.add_apply]
    exact CharTwo.sub_eq_add _ _
  rw [e]
  exact rank_of_cert (by norm_num) TwoAC.wf_X1 TwoAC.wf_Px TwoAC.wf_Qx
    (by bm_strips4 CFSG.KC.BM.TwoAC.cPx 69) TwoAC.shape_x TwoAC.ech_x

theorem th0_eq : stripMat TwoAC.th0 = TwoAC.bW mA mB * TwoAC.aW mA mB +
    TwoAC.aW mA mB * TwoAC.bW mA mB * TwoAC.bW mA mB + TwoAC.aW mA mB := by
  rw [TwoAC.xorRowL_sound (T := TwoAC.th0) (As := [TwoAC.ba, TwoAC.abb, TwoAC.a])
    (by forall_lt_consts CFSG.KC.BM.TwoAC.xth0_ 69)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← mulC TwoAC.ba TwoAC.wf_w2 TwoAC.wf_a (by bm_strips4 CFSG.KC.BM.TwoAC.cba 69),
    ← mulC TwoAC.abb TwoAC.wf_ab TwoAC.wf_w2 (by bm_strips4 CFSG.KC.BM.TwoAC.cabb 69), e_ab, e_a,
    e_b]
  simp [add_assoc]

theorem th1_eq : stripMat TwoAC.th1 = TwoAC.bW mA mB +
    TwoAC.aW mA mB * TwoAC.bW mA mB * TwoAC.bW mA mB +
      TwoAC.bW mA mB * TwoAC.bW mA mB * TwoAC.bW mA mB + 1 := by
  rw [TwoAC.xorRowL_sound (T := TwoAC.th1) (As := [TwoAC.w2, TwoAC.abb, TwoAC.b3, idStrips])
    (by forall_lt_consts CFSG.KC.BM.TwoAC.xth1_ 69)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← mulC TwoAC.abb TwoAC.wf_ab TwoAC.wf_w2 (by bm_strips4 CFSG.KC.BM.TwoAC.cabb 69),
    ← mulC TwoAC.b3 TwoAC.wf_w4 TwoAC.wf_w2 (by bm_strips4 CFSG.KC.BM.TwoAC.cb3 69),
    ← mulC TwoAC.w4 TwoAC.wf_w2 TwoAC.wf_w2 (by bm_strips4 CFSG.KC.BM.TwoAC.cw4 69), e_ab, e_b]
  simp [add_assoc, stripMat_idStrips]

end CertificateChecks.KernelTwoAC

end
