
module

public import Certificates.Kernel.Ly3085.Bridge

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open Matrix

theorem lanesW_inj (w : ℕ) : ∀ (n X Y : ℕ), X < 2 ^ (w * n) → Y < 2 ^ (w * n) →
    (∀ q < n, X / 2 ^ (w * q) % 2 ^ w = Y / 2 ^ (w * q) % 2 ^ w) → X = Y
  | 0, X, Y, hX, hY, _ => by simp at hX hY; omega
  | n + 1, X, Y, hX, hY, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have hdiv : ∀ Z : ℕ, Z < 2 ^ (w * (n + 1)) → Z / 2 ^ w < 2 ^ (w * n) := by
      intro Z hZ
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      convert hZ using 2
    have hq : ∀ (Z q : ℕ), Z / 2 ^ w / 2 ^ (w * q) = Z / 2 ^ (w * (q + 1)) := by
      intro Z q
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
      ring
    have e := lanesW_inj w n (X / 2 ^ w) (Y / 2 ^ w) (hdiv X hX) (hdiv Y hY) (fun q hq' => by
      rw [hq, hq]
      exact h (q + 1) (by omega))
    rw [← Nat.div_add_mod X (2 ^ w), ← Nat.div_add_mod Y (2 ^ w), e, h0]

theorem blkM_inj {X Y : ℕ} (hX : LCanon 12 7 111 X) (hY : LCanon 12 7 111 Y)
    (h : blkM X = blkM Y) : X = Y := by
  have hb : (12 * 111 * 7 : ℕ) = 12 * 777 := by norm_num
  refine lanesW_inj 12 777 X Y (hb ▸ hX.1) (hb ▸ hY.1) fun q hq => ?_
  have hi : q / 111 < 7 := by omega
  have hj : q % 111 < 111 := Nat.mod_lt _ (by norm_num)
  have ho : 12 * 111 * (q / 111) + 12 * (q % 111) = 12 * q := by omega
  have hfX := hX.2 _ hi _ hj
  have hfY := hY.2 _ hi _ hj
  rw [ho] at hfX hfY
  have e := congrFun (congrFun h ⟨q / 111, hi⟩) ⟨q % 111, hj⟩
  simp only [blkM, ent] at e
  have ho' : 1332 * (q / 111) + 12 * (q % 111) = 12 * q := by omega
  rw [ho', ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hfX, Nat.mod_eq_of_lt hfY] at e
  exact e

theorem add_shift_inj {a a' c c' m : ℕ} (ha : a < 2 ^ m) (ha' : a' < 2 ^ m)
    (h : Nat.add a (Nat.shiftLeft c m) = Nat.add a' (Nat.shiftLeft c' m)) : a = a' ∧ c = c' := by
  change a + c <<< m = a' + c' <<< m at h
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq] at h
  have h1 := congrArg (· % 2 ^ m) h
  have h2 := congrArg (· / 2 ^ m) h
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt ha'] at h1
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha'] at h2
  exact ⟨h1, by omega⟩

theorem bIf_true {c x : Bool} (h : Bool.rec (motive := fun _ => Bool) true x c = true)
    (hc : c = true) : x = true := by
  subst hc
  exact h

theorem tabPI_sound {C : BConsts} {PI PJ : ℕ → ℕ} {nc : ℕ} (h : tabPI C PI PJ nc = true) :
    ∀ c < 8, c < nc → fVld C (PI c) = true ∧ fVld C (PJ c) = true ∧
      Nat.beq (fMul C (PI c) (PJ c)) C.ONEF = true := by
  intro c hc8 hc
  unfold tabPI at h
  have := recAnd (p := fun c => bIf(Nat.blt c nc, bAnd(fVld C (PI c), bAnd(fVld C (PJ c),
    Nat.beq (fMul C (PI c) (PJ c)) C.ONEF)), true)) 8 h c hc8
  have e := bIf_true this (by rw [Nat.blt_eq]; exact hc)
  obtain ⟨a1, e⟩ := bAnd_true e
  obtain ⟨a2, a3⟩ := bAnd_true e
  exact ⟨a1, a2, a3⟩

theorem tabGT_sound {C : BConsts} {PI GT : ℕ → ℕ} {G0 G1 nc lo cnt : ℕ}
    (h : tabGT C PI GT G0 G1 nc lo cnt = true) :
    ∀ k, lo ≤ k → k < lo + cnt → k / 2 % 8 < nc → k / 16 < nc →
      fVld C (GT k) = true ∧
      Nat.beq (fMul C (PI (k / 2 % 8)) (GT k)) (fMul C (pickL [G0, G1] (k % 2)) (PI (k / 16))) =
        true := by
  intro k hk1 hk2 hc hc'
  unfold tabGT at h
  have := recAnd cnt h (k - lo) (by omega)
  rw [show Nat.add lo (k - lo) = k by change lo + (k - lo) = k; omega] at this
  have e := bIf_true this (by
    change (Nat.blt (Nat.mod (Nat.div k 2) 8) nc && Nat.blt (Nat.div k 16) nc) = true
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
    exact ⟨hc, hc'⟩)
  exact bAnd_true e

theorem tabWC_sound {C : BConsts} {PI WC : ℕ → ℕ} {nc : ℕ} (h : tabWC C PI WC nc = true) :
    ∀ e c, e < c → c < nc → nc ≤ 8 → fVld C (WC (c + 8 * e)) = true ∧
      Nat.beq (fMul C (PI c) (WC (c + 8 * e))) (PI e) = true := by
  intro e c hec hc h8
  unfold tabWC at h
  have := recAnd (p := fun k => (fun c e => bIf(bAnd(Nat.blt e c, Nat.blt c nc),
      bAnd(fVld C (WC k), Nat.beq (fMul C (PI c) (WC k)) (PI e)), true))
      (Nat.mod k 8) (Nat.div k 8)) 64 h (c + 8 * e) (by omega)
  have m1 : Nat.mod (c + 8 * e) 8 = c := by change (c + 8 * e) % 8 = c; omega
  have m2 : Nat.div (c + 8 * e) 8 = e := by change (c + 8 * e) / 8 = e; omega
  rw [m1, m2] at this
  have e1 := bIf_true this (by
    change (Nat.blt e c && Nat.blt c nc) = true
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
    exact ⟨hec, hc⟩)
  exact bAnd_true e1

@[expose] def lastSel (j : Fin 7) : Fin 111 := ⟨104 + j.val, by omega⟩

theorem lastCols_eq (M : Matrix (Fin 7) (Fin 111) (ZMod 5)) : lastCols M = M.submatrix id lastSel :=
  rfl

theorem chart_tree {KX PT WT GT WC PI PJ SG : ℕ → ℕ} {n nc : ℕ} {G0 G1 : ℕ}
    {Gi0 Gi1 : Matrix (Fin 111) (Fin 111) (ZMod 5)}
    (hnc : nc ≤ 8)
    (cG : LCanon 12 111 111 G0 ∧ LCanon 12 111 111 G1)
    (hGi : bigM G0 * Gi0 = 1 ∧ bigM G1 * Gi1 = 1)
    (hpi : tabPI CFSG.KD.LyOm.BC PI PJ nc = true)
    (hgt : ∀ s < 2, ∀ c < nc, ∀ c' < nc,
      fVld CFSG.KD.LyOm.BC (GT (s + 2 * c + 16 * c')) = true ∧
      Nat.beq (fMul CFSG.KD.LyOm.BC (PI c) (GT (s + 2 * c + 16 * c')))
        (fMul CFSG.KD.LyOm.BC (pickL [G0, G1] s) (PI c')) = true)
    (hwc : tabWC CFSG.KD.LyOm.BC PI WC nc = true)
    (hnode : ∀ i < n, cNode CFSG.KD.LyOm.BC KX PT WT GT WC nc n i = true)
    (hsg : ∀ k < n, getRec SG 20 k < n)
    (hsort : ∀ k, k + 1 < n → cKey KX PT (getRec SG 20 k) < cKey KX PT (getRec SG 20 (k + 1))) :
    (∀ i < n, LCanon 12 7 111 (getRec KX 9324 i) ∧ chartOf (getRec PT 32 i) < nc) ∧
    (∀ i < n, 0 < i → fldW (getRec PT 32 i) 0 20 < i ∧ fldW (getRec PT 32 i) 20 4 < 2 ∧
      rs (blkM (getRec KX 9324 i) * bigM (PJ (chartOf (getRec PT 32 i))) * TIm) =
        (rs (blkM (getRec KX 9324 (fldW (getRec PT 32 i) 0 20)) *
          bigM (PJ (chartOf (getRec PT 32 (fldW (getRec PT 32 i) 0 20)))) * TIm)).map
          (Matrix.vecMulLinear (Tm * bigM (pickL [G0, G1] (fldW (getRec PT 32 i) 20 4)) * TIm))) ∧
    (∀ i < n, ∀ j < n,
      rs (blkM (getRec KX 9324 i) * bigM (PJ (chartOf (getRec PT 32 i))) * TIm) =
        rs (blkM (getRec KX 9324 j) * bigM (PJ (chartOf (getRec PT 32 j))) * TIm) → i = j) := by
  have hPI := tabPI_sound hpi
  have hWC := tabWC_sound hwc
  have cPI : ∀ c < nc, LCanon 12 111 111 (PI c) := fun c hc => fvld_canon (hPI c (by omega) hc).1
  have cPJ : ∀ c < nc, LCanon 12 111 111 (PJ c) := fun c hc => fvld_canon (hPI c (by omega) hc).2.1
  have cGT : ∀ s < 2, ∀ c < nc, ∀ c' < nc, LCanon 12 111 111 (GT (s + 2 * c + 16 * c')) :=
    fun s hs c hc c' hc' => fvld_canon (hgt s hs c hc c' hc').1
  have cWC : ∀ e c, e < c → c < nc → LCanon 12 111 111 (WC (c + 8 * e)) :=
    fun e c hec hc => fvld_canon (hWC e c hec hc hnc).1
  have cGs : ∀ s < 2, LCanon 12 111 111 (pickL [G0, G1] s) := by
    intro s hs
    interval_cases s
    · exact cG.1
    · exact cG.2
  have hcan : ∀ i < n, LCanon 12 7 111 (getRec KX 9324 i) ∧ chartOf (getRec PT 32 i) < nc := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hs := cNode_sound' hBC cGT cWC (fun j hj => ih j hj (by omega)) (hnode i hi)
      exact ⟨hs.2.1, hs.1⟩
  have hs : ∀ i < n, _ := fun i hi =>
    cNode_sound' hBC cGT cWC (fun j hj => hcan j (by omega)) (hnode i hi)
  have mPI : ∀ c < nc, bigM (PI c) * bigM (PJ c) = 1 := by
    intro c hc
    rw [← (fmul (cPI c hc) (cPJ c hc)).2, beq_eq (hPI c (by omega) hc).2.2, one_facts.2]
  have mGT : ∀ s < 2, ∀ c < nc, ∀ c' < nc,
      bigM (PI c) * bigM (GT (s + 2 * c + 16 * c')) = bigM (pickL [G0, G1] s) * bigM (PI c') := by
    intro s hs c hc c' hc'
    rw [← (fmul (cPI c hc) (cGT s hs c hc c' hc')).2, beq_eq (hgt s hs c hc c' hc').2,
      (fmul (cGs s hs) (cPI c' hc')).2]
  have mWC : ∀ e c, e < c → c < nc → bigM (PI c) * bigM (WC (c + 8 * e)) = bigM (PI e) := by
    intro e c hec hc
    rw [← (fmul (cPI c hc) (cWC e c hec hc)).2, beq_eq (hWC e c hec hc hnc).2]
  have mG : ∀ s < 2, bigM (pickL [G0, G1] s) * (if s = 0 then Gi0 else Gi1) = 1 := by
    intro s hs
    interval_cases s
    · rw [if_pos rfl]
      exact hGi.1
    · rw [if_neg (by norm_num)]
      exact hGi.2
  have hkinj : ∀ i < n, ∀ j < n, blkM (getRec KX 9324 i) = blkM (getRec KX 9324 j) →
      chartOf (getRec PT 32 i) = chartOf (getRec PT 32 j) → i = j := by
    intro i hi j hj e hc
    have ek := blkM_inj (hcan i hi).1 (hcan j hj).1 e
    refine sorted_inj (cKey KX PT) (fun k => getRec SG 20 k) hsg hsort i hi j hj ?_
    unfold cKey
    rw [ek, hc]
  obtain ⟨h1, h2⟩ := chart_spaces (K := ZMod 5) (n := n) (nc := nc)
    (N := fun i => blkM (getRec KX 9324 i)) (ch := fun i => chartOf (getRec PT 32 i))
    (par := fun i => fldW (getRec PT 32 i) 0 20) (lab := fun i => fldW (getRec PT 32 i) 20 4)
    (PI := fun c => bigM (PI c)) (PJ := fun c => bigM (PJ c)) (GT := fun k => bigM (GT k))
    (WC := fun k => bigM (WC k)) (G := fun s => bigM (pickL [G0, G1] s))
    (Gi := fun s => if s = 0 then Gi0 else Gi1) (T := Tm) (TI := TIm) lastSel mPI mGT mWC mG
    t_facts.1 (fun i hi => ⟨(hs i hi).1, (hs i hi).2.2.1, (hs i hi).2.2.2.1, (hs i hi).2.2.2.2⟩)
    hkinj
  refine ⟨hcan, fun i hi hi0 => ⟨((hs i hi).2.2.2.2 hi0).1, ((hs i hi).2.2.2.2 hi0).2.1,
    h1 i hi hi0⟩, h2⟩

theorem root_space [LySeed]
    {KX PT PI PJ : ℕ → ℕ} {nc UT : ℕ} {g : J}
    (hcan0 : LCanon 12 7 111 (getRec KX 9324 0) ∧ chartOf (getRec PT 32 0) < nc)
    (hpi : tabPI CFSG.KD.LyOm.BC PI PJ nc = true) (hnc : nc ≤ 8)
    (cUT : LCanon 12 7 111 UT) (eUT : blkM UT = (mat g * lyU)ᵀ)
    (h : rootOK CFSG.KD.LyOm.BC KX PT PI (bMul CFSG.KD.LyOm.BC UT CFSG.KD.LyOm.T) = true) :
    rs (blkM (getRec KX 9324 0) * bigM (PJ (chartOf (getRec PT 32 0))) * TIm) =
      rs (mat g * lyU)ᵀ := by
  unfold rootOK at h
  set c := chartOf (getRec PT 32 0)
  have hP := tabPI_sound hpi c (by omega) hcan0.2
  have cP := fvld_canon hP.1
  have cJ := fvld_canon hP.2.1
  have eP : bigM (PI c) * bigM (PJ c) = 1 := by
    rw [← (fmul cP cJ).2, beq_eq hP.2.2, one_facts.2]
  have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
  have b1 := bmul cUT cT
  have b2 := bmul b1.1 cP
  have hs := sameSpanL_sound hBC hcan0.1 b2.1 h
  rw [b2.2, b1.2, eUT] at hs
  set N := blkM (getRec KX 9324 0)
  have e : (mat g * lyU)ᵀ = lastCols ((mat g * lyU)ᵀ * Tm * bigM (PI c)) *
      (N * bigM (PJ c) * TIm) := by
    calc (mat g * lyU)ᵀ = (mat g * lyU)ᵀ * Tm * (bigM (PI c) * bigM (PJ c)) * TIm := by
          rw [eP, Matrix.mul_one, Matrix.mul_assoc, t_facts.1, Matrix.mul_one]
      _ = ((mat g * lyU)ᵀ * Tm * bigM (PI c)) * bigM (PJ c) * TIm := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [show Tm = bigM CFSG.KD.LyOm.T from rfl]
          nth_rewrite 1 [hs]
          simp only [Matrix.mul_assoc]
  exact (rs_eq_of_right_inv (rowU_rinv g) e).symm

theorem imOp_smulS [LySeed] (S : Subgroup J) (h : S) (x : LyOperator) :
    imOp (h • x) = h • imOp x := by
  rw [Subgroup.smul_def, Subgroup.smul_def]
  exact imOp_smul _ _

theorem step_smul [LySeed] {m : Type*} {X : Matrix m (Fin 111) (ZMod 5)}
    {G : Matrix (Fin 111) (Fin 111) (ZMod 5)} {h : J} (hG : Tm * G * TIm = (mat h)ᵀ) :
    (⟨(rs X).map (Matrix.vecMulLinear (Tm * G * TIm))⟩ : LySp) = h • ⟨rs X⟩ := by
  rw [hG, vecMulLinear_transpose]
  rfl

end CertificateChecks.KernelLy.Omega

end
