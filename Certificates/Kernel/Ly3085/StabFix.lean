
module

public import Certificates.Kernel.Ly3085.SqueezeBase
public import Certificates.Kernel.Ly3085.HEnum
public import Certificates.Kernel.Ly3085.Omega.HFix
public import Certificates.Kernel.Ly3085.O2Count
public import Certificates.Kernel.Ly3085.O34Count

public section

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL CFSG.KC.Loop
open Matrix MulAction

theorem smul_rs [LySeed] {m : Type*} (g : J)
    (X : Matrix m (Fin 111) (ZMod 5)) : g • (⟨rs X⟩ : LySp) = ⟨rs (X * (mat g)ᵀ)⟩ := by
  ext1
  rw [lySp_smul_V, rs_mul_right, vecMulLinear_transpose]

theorem rinv_of_eq [LySeed] (g : J)
    {X : Matrix (Fin 7) (Fin 111) (ZMod 5)} {F : Matrix (Fin 7) (Fin 7) (ZMod 5)}
    (h : (mat g * lyU)ᵀ = F * X) : ∃ Z : Matrix (Fin 111) (Fin 7) (ZMod 5), X * Z = 1 := by
  have hR := rowU_rinv g
  rw [h, Matrix.mul_assoc] at hR
  have := mul_comm_one hR
  exact ⟨(mat g⁻¹)ᵀ * E7ᵀ * F, by rw [← Matrix.mul_assoc]; exact this⟩

theorem fix_of_mul [LySeed] {X : Matrix (Fin 7) (Fin 111) (ZMod 5)}
    {Z : Matrix (Fin 111) (Fin 7) (ZMod 5)} (hZ : X * Z = 1) (g : J)
    {M : Matrix (Fin 7) (Fin 7) (ZMod 5)} (h : X * (mat g)ᵀ = M * X) :
    g • (⟨rs X⟩ : LySp) = ⟨rs X⟩ := by
  rw [smul_rs]
  refine congrArg LySp.mk (rs_eq_of_right_inv (Z := (mat g⁻¹)ᵀ * Z) ?_ h)
  calc X * (mat g)ᵀ * ((mat g⁻¹)ᵀ * Z) = X * (mat g⁻¹ * mat g)ᵀ * Z := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [mat_inv_mul, Matrix.transpose_one, Matrix.mul_one, hZ]

theorem bword_facts [LySeed] :
    ∀ (w : List ℕ) (X : ℕ), (∀ l ∈ w, l < 4) → LCanon 12 7 111 X →
      LCanon 12 7 111 (bWord CFSG.KD.LyOm.BC CFSG.KD.LyOm.GP2 X w.reverse) ∧
      blkM (bWord CFSG.KD.LyOm.BC CFSG.KD.LyOm.GP2 X w.reverse) = blkM X * bigM (CFSG.KD.LyOm.PW w)
  | [], X, _, hX => ⟨hX, by
      change blkM X = blkM X * bigM CFSG.KD.LyOm.BC.ONEF
      rw [one_facts.2, Matrix.mul_one]⟩
  | l :: w, X, hw, hX => by
    obtain ⟨c, e⟩ := bword_facts w X (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) hX
    obtain ⟨cl, -⟩ := gp_facts (hw l List.mem_cons_self)
    have cw := (pw_facts w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))).1
    have hrev : bWord CFSG.KD.LyOm.BC CFSG.KD.LyOm.GP2 X (l :: w).reverse =
        bMul CFSG.KD.LyOm.BC (bWord CFSG.KD.LyOm.BC CFSG.KD.LyOm.GP2 X w.reverse)
          (CFSG.KD.LyOm.GP2 l) := by
      unfold bWord
      rw [List.reverse_cons, wordR_append, wordR_cons, wordR_nil]
    have hpw : CFSG.KD.LyOm.PW (l :: w) = fMul CFSG.KD.LyOm.BC (CFSG.KD.LyOm.PW w)
        (CFSG.KD.LyOm.GP2 l) := by
      unfold CFSG.KD.LyOm.PW
      rw [List.reverse_cons, fWord_append, fWord_cons, fWord_nil]
    rw [hrev, hpw]
    refine ⟨(bmul c cl).1, ?_⟩
    rw [(bmul c cl).2, e, (fmul cw cl).2, Matrix.mul_assoc]

theorem pairOp_fix
    [LySeed] {p : LyOperator} {h : lyH} (hb : h • beta p = beta p)
    (hi : (h : J) • imOp p = imOp p) : h ∈ stabilizer lyH (pairOp p) := by
  rw [mem_stabilizer_iff]
  exact Prod.ext hb hi

theorem letB_app (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by cases v <;> rfl

theorem n2_facts
    [LySeed] : LCanon 12 7 111 CFSG.KD.LyOm.N2 ∧
    (mat (gRep 2) * lyU)ᵀ = firstCols (blkM (bMul CFSG.KD.LyOm.BC CFSG.KD.LyOm.UT2 CFSG.KD.LyOm.T)) *
      (blkM CFSG.KD.LyOm.N2 * TIm) := by
  obtain ⟨cN, -⟩ := spreadB_sound CFSG.KD.LyO2.consts (getRec_lt _ _ _) (o2_fields 0 (by
    rw [CFSG.KD.LyO2.n_eq]
    norm_num))
  have cN' : LCanon 12 7 111 CFSG.KD.LyOm.N2 := cN
  obtain ⟨cUT, eUT, -⟩ := rep2
  have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
  have b1 := bmul cUT cT
  have hs := sameSpan_sound hBC cN' b1.1 CFSG.KD.LyOm.root2
  refine ⟨cN', ?_⟩
  have e1 : bigM CFSG.KD.LyOm.T * TIm = 1 := t_facts.1
  rw [← Matrix.mul_assoc, ← hs, b1.2, eUT, Matrix.mul_assoc, e1, Matrix.mul_one]

theorem wh2_fix
    [LySeed] {w : List ℕ} (hw : ∀ l ∈ w, l < 4)
    (h : CFSG.KD.LyOm.fixSpan CFSG.KD.LyOm.N2 w = true) :
    (⟨wordJ w, wordJ_mem w⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 2 • opE)) := by
  obtain ⟨cN, eN⟩ := n2_facts
  obtain ⟨Z, hZ⟩ := rinv_of_eq _ eN
  have hsp : imOp (gRep 2 • opE) = ⟨rs (blkM CFSG.KD.LyOm.N2 * TIm)⟩ := by
    rw [imOp_smul_opE]
    exact congrArg LySp.mk (rs_eq_of_right_inv (rowU_rinv (gRep 2)) eN)
  unfold CFSG.KD.LyOm.fixSpan at h
  obtain ⟨cY, eY⟩ := bword_facts w CFSG.KD.LyOm.N2 hw cN
  have hs := sameSpan_sound hBC cN cY h
  rw [eY] at hs
  have epw := (pw_facts w hw).2
  refine pairOp_fix (by rw [beta_rep2]; exact beta2_fixed _) ?_
  rw [hsp]
  refine fix_of_mul hZ _ (M := firstCols (blkM CFSG.KD.LyOm.N2 * bigM (CFSG.KD.LyOm.PW w))) ?_
  rw [← epw]
  calc blkM CFSG.KD.LyOm.N2 * TIm * (Tm * bigM (CFSG.KD.LyOm.PW w) * TIm)
      = blkM CFSG.KD.LyOm.N2 * (TIm * Tm) * bigM (CFSG.KD.LyOm.PW w) * TIm := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [t_facts.2, Matrix.mul_one]
        nth_rewrite 1 [hs]
        simp only [Matrix.mul_assoc]

theorem whc_fix
    [LySeed] {KX PT PI PJ : ℕ → ℕ} {nc UT BE c : ℕ} {w : List ℕ}
    (hcan0 : LCanon 12 7 111 (getRec KX 9324 0) ∧ chartOf (getRec PT 32 0) < nc)
    (hpi : tabPI CFSG.KD.LyOm.BC PI PJ nc = true) (hnc : nc ≤ 8)
    (cUT : LCanon 12 7 111 UT) (eUT : blkM UT = (mat (gRep c) * lyU)ᵀ)
    (hroot : rootOK CFSG.KD.LyOm.BC KX PT PI (bMul CFSG.KD.LyOm.BC UT CFSG.KD.LyOm.T) = true)
    (hbeta : beta (gRep c • opE) = fm BE) (cBE : LCanon 11 7 7 BE) (hw : ∀ l ∈ w, l < 4)
    (hfix : rootFix CFSG.KD.LyOm.BC KX PT PI PJ CFSG.KD.LyOm.GP2 w = true)
    (hfb : CFSG.KD.LyOm.fixBeta BE w = true) :
    (⟨wordJ w, wordJ_mem w⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep c • opE)) := by
  set c0 := chartOf (getRec PT 32 0)
  set N := blkM (getRec KX 9324 0)
  have hP := tabPI_sound hpi c0 (by omega) hcan0.2
  have cP := fvld_canon hP.1
  have cJ := fvld_canon hP.2.1
  have eP : bigM (PI c0) * bigM (PJ c0) = 1 := by
    rw [← (fmul cP cJ).2, beq_eq hP.2.2, one_facts.2]
  have eP' : bigM (PJ c0) * bigM (PI c0) = 1 := mul_comm_one eP
  have hsp : imOp (gRep c • opE) = ⟨rs (N * bigM (PJ c0) * TIm)⟩ := by
    rw [imOp_smul_opE]
    exact congrArg LySp.mk (root_space hcan0 hpi hnc cUT eUT hroot).symm
  have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
  have b1 := bmul cUT cT
  have b2 := bmul b1.1 cP
  unfold rootOK at hroot
  have hs0 := sameSpanL_sound hBC hcan0.1 b2.1 hroot
  rw [b2.2, b1.2, eUT] at hs0
  have eN : (mat (gRep c) * lyU)ᵀ = lastCols ((mat (gRep c) * lyU)ᵀ * Tm * bigM (PI c0)) *
      (N * bigM (PJ c0) * TIm) := by
    calc (mat (gRep c) * lyU)ᵀ = (mat (gRep c) * lyU)ᵀ * Tm * (bigM (PI c0) * bigM (PJ c0)) * TIm := by
          rw [eP, Matrix.mul_one, Matrix.mul_assoc, t_facts.1, Matrix.mul_one]
      _ = ((mat (gRep c) * lyU)ᵀ * Tm * bigM (PI c0)) * bigM (PJ c0) * TIm := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [show Tm = bigM CFSG.KD.LyOm.T from rfl]
          nth_rewrite 1 [hs0]
          simp only [Matrix.mul_assoc]
          rfl
  obtain ⟨Z, hZ⟩ := rinv_of_eq _ eN
  unfold rootFix at hfix
  rw [letB_app] at hfix
  have y0 := bmul hcan0.1 cJ
  obtain ⟨cY1, eY1⟩ := bword_facts w _ hw y0.1
  have y2 := bmul cY1 cP
  have hs := sameSpanL_sound hBC hcan0.1 y2.1 hfix
  rw [y2.2, eY1, y0.2] at hs
  set M := lastCols (N * bigM (PJ c0) * bigM (CFSG.KD.LyOm.PW w) * bigM (PI c0))
  have hs' : N * bigM (PJ c0) * bigM (CFSG.KD.LyOm.PW w) = M * N * bigM (PJ c0) := by
    calc N * bigM (PJ c0) * bigM (CFSG.KD.LyOm.PW w)
        = N * bigM (PJ c0) * bigM (CFSG.KD.LyOm.PW w) * (bigM (PI c0) * bigM (PJ c0)) := by
          rw [eP, Matrix.mul_one]
      _ = (N * bigM (PJ c0) * bigM (CFSG.KD.LyOm.PW w) * bigM (PI c0)) * bigM (PJ c0) := by
          simp only [Matrix.mul_assoc]
      _ = M * N * bigM (PJ c0) := by
          nth_rewrite 1 [hs]
          rfl
  have epw := (pw_facts w hw).2
  refine pairOp_fix ?_ ?_
  · rw [hbeta]
    exact fixBeta_stab hw cBE hfb
  · rw [hsp]
    refine fix_of_mul hZ _ (M := M) ?_
    rw [← epw]
    calc N * bigM (PJ c0) * TIm * (Tm * bigM (CFSG.KD.LyOm.PW w) * TIm)
        = N * bigM (PJ c0) * (TIm * Tm) * bigM (CFSG.KD.LyOm.PW w) * TIm := by
          simp only [Matrix.mul_assoc]
      _ = M * (N * bigM (PJ c0) * TIm) := by
          rw [t_facts.2, Matrix.mul_one, hs']
          simp only [Matrix.mul_assoc]

theorem fw_all : ∀ p ∈ CFSG.KD.LyOm.hGens, CFSG.KD.LyOm.fixBeta p.1 p.2 = true :=
  fun p hp => List.all_eq_true.1 CFSG.KD.LyOm.fwh p hp

theorem fb_facts : CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE3 CFSG.KD.LyOm.WH3_0 = true ∧
    CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE3 CFSG.KD.LyOm.WH3_1 = true ∧
    CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE3 CFSG.KD.LyOm.WH3_2 = true ∧
    CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE4 CFSG.KD.LyOm.WH4_0 = true ∧
    CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE4 CFSG.KD.LyOm.WH4_1 = true ∧
    CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE4 CFSG.KD.LyOm.WH4_2 = true ∧
    CFSG.KD.LyOm.fixBeta CFSG.KD.LyOm.BE4 CFSG.KD.LyOm.WH4_3 = true := by
  refine ⟨fw_all (CFSG.KD.LyOm.BE3, CFSG.KD.LyOm.WH3_0) ?_,
    fw_all (CFSG.KD.LyOm.BE3, CFSG.KD.LyOm.WH3_1) ?_, fw_all (CFSG.KD.LyOm.BE3, CFSG.KD.LyOm.WH3_2) ?_,
    fw_all (CFSG.KD.LyOm.BE4, CFSG.KD.LyOm.WH4_0) ?_, fw_all (CFSG.KD.LyOm.BE4, CFSG.KD.LyOm.WH4_1) ?_,
    fw_all (CFSG.KD.LyOm.BE4, CFSG.KD.LyOm.WH4_2) ?_, fw_all (CFSG.KD.LyOm.BE4, CFSG.KD.LyOm.WH4_3) ?_⟩
    <;> unfold CFSG.KD.LyOm.hGens
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))

theorem f3_root [LySeed] :
    LCanon 12 7 111 (getRec CFSG.KD.LyF3.KX 9324 0) ∧
      chartOf (getRec CFSG.KD.LyF3.PT 32 0) < CFSG.KD.LyF3.nc := by
  have hnc := CFSG.KD.LyF3.nc_eq
  have hs := cNode_sound' hBC (GT := CFSG.KD.LyF3.GT) (WC := CFSG.KD.LyF3.WC)
    (nc := CFSG.KD.LyF3.nc) (i := 0)
    (fun s hs c hc c' hc' => by
      have h1 : c = 0 := by omega
      have h2 : c' = 0 := by omega
      subst h1 h2
      have := tabGT_sound CFSG.KD.LyOm.f3gt s (by omega) (by omega) (by omega) (by omega)
      have e3 : s % 2 = s := Nat.mod_eq_of_lt hs
      rw [e3] at this
      simpa using fvld_canon this.1)
    (fun e c hec hc => absurd hc (by omega)) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (cRange_sound CFSG.KD.LyF3.f30 0 (by change 64 * 0 ≤ 0; omega)
      (by change 0 < 64 * (0 + 1); omega) (by rw [CFSG.KD.LyF3.n_eq]; norm_num))
  exact ⟨hs.2.1, hs.1⟩

theorem f4_root [LySeed] :
    LCanon 12 7 111 (getRec CFSG.KD.LyF4.KX 9324 0) ∧
      chartOf (getRec CFSG.KD.LyF4.PT 32 0) < CFSG.KD.LyF4.nc := by
  have hnc := CFSG.KD.LyF4.nc_eq
  have hs := cNode_sound' hBC (GT := CFSG.KD.LyF4.GT) (WC := CFSG.KD.LyF4.WC)
    (nc := CFSG.KD.LyF4.nc) (i := 0)
    (fun s hs c hc c' hc' => by
      have h1 : c = 0 := by omega
      have h2 : c' = 0 := by omega
      subst h1 h2
      have := tabGT_sound CFSG.KD.LyOm.f4gt s (by omega) (by omega) (by omega) (by omega)
      have e3 : s % 2 = s := Nat.mod_eq_of_lt hs
      rw [e3] at this
      simpa using fvld_canon this.1)
    (fun e c hec hc => absurd hc (by omega)) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (cRange_sound (CFSG.KD.LyF4.leavesOK 0 (by norm_num)) 0 (by change 64 * 0 ≤ 0; omega)
      (by change 0 < 64 * (0 + 1); omega) (by rw [CFSG.KD.LyF4.n_eq]; norm_num))
  exact ⟨hs.2.1, hs.1⟩

theorem k2_gens
    [LySeed] :
    (⟨wordJ CFSG.KD.LyOm.WH2_0, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 2 • opE)) ∧
    (⟨wordJ CFSG.KD.LyOm.WH2_1, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 2 • opE)) := by
  obtain ⟨l0, l1, -⟩ := wh_lt
  exact ⟨wh2_fix l0 CFSG.KD.LyOm.h2fix0, wh2_fix l1 CFSG.KD.LyOm.h2fix1⟩

theorem k3_gens
    [LySeed] :
    (⟨wordJ CFSG.KD.LyOm.WH3_0, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧
    (⟨wordJ CFSG.KD.LyOm.WH3_1, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧
    (⟨wordJ CFSG.KD.LyOm.WH3_2, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 3 • opE)) := by
  obtain ⟨-, -, l0, l1, l2, -⟩ := wh_lt
  obtain ⟨cUT, eUT, -, cBE, -⟩ := rep3
  have hnc : CFSG.KD.LyF3.nc ≤ 8 := by rw [CFSG.KD.LyF3.nc_eq]; norm_num
  have key := fun {w : List ℕ} (hw : ∀ l ∈ w, l < 4) hfix hfb =>
    whc_fix (w := w) f3_root CFSG.KD.LyOm.f3pi hnc cUT eUT CFSG.KD.LyOm.f3root beta_rep3 cBE hw
      hfix hfb
  obtain ⟨f0, f1, f2, -⟩ := fb_facts
  exact ⟨key l0 CFSG.KD.LyOm.f3fix0 f0, key l1 CFSG.KD.LyOm.f3fix1 f1,
    key l2 CFSG.KD.LyOm.f3fix2 f2⟩

theorem k4_gens
    [LySeed] :
    (⟨wordJ CFSG.KD.LyOm.WH4_0, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧
    (⟨wordJ CFSG.KD.LyOm.WH4_1, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧
    (⟨wordJ CFSG.KD.LyOm.WH4_2, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧
    (⟨wordJ CFSG.KD.LyOm.WH4_3, wordJ_mem _⟩ : lyH) ∈ stabilizer lyH (pairOp (gRep 4 • opE)) := by
  obtain ⟨-, -, -, -, -, l0, l1, l2, l3⟩ := wh_lt
  obtain ⟨cUT, eUT, -, cBE, -⟩ := rep4
  have hnc : CFSG.KD.LyF4.nc ≤ 8 := by rw [CFSG.KD.LyF4.nc_eq]; norm_num
  have key := fun {w : List ℕ} (hw : ∀ l ∈ w, l < 4) hfix hfb =>
    whc_fix (w := w) f4_root CFSG.KD.LyOm.f4pi hnc cUT eUT CFSG.KD.LyOm.f4root beta_rep4 cBE hw
      hfix hfb
  obtain ⟨-, -, -, f0, f1, f2, f3⟩ := fb_facts
  exact ⟨key l0 CFSG.KD.LyOm.f4fix0 f0, key l1 CFSG.KD.LyOm.f4fix1 f1,
    key l2 CFSG.KD.LyOm.f4fix2 f2, key l3 CFSG.KD.LyOm.f4fix3 f3⟩

end CertificateChecks.KernelLy.Omega

end

end
