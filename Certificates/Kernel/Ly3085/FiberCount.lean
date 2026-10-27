
module

public import Certificates.Kernel.Ly3085.ChartGlue

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open Matrix MulAction

theorem fiber_tree
    [LySeed] {KX PT WT GT WC PI PJ SG : ℕ → ℕ} {n nc UT : ℕ}
    {w0 w1 : List ℕ} {F : Form7} {g : J} (hnc : nc = 1)
    (hw0 : ∀ l ∈ w0, l < 4) (hw1 : ∀ l ∈ w1, l < 4)
    (hs0 : (⟨wordJ w0, wordJ_mem w0⟩ : lyH) ∈ stabilizer lyH F)
    (hs1 : (⟨wordJ w1, wordJ_mem w1⟩ : lyH) ∈ stabilizer lyH F)
    (hpi : tabPI CFSG.KD.LyOm.BC PI PJ nc = true)
    (hgt : tabGT CFSG.KD.LyOm.BC PI GT (CFSG.KD.LyOm.PW w0) (CFSG.KD.LyOm.PW w1) nc 0 128 = true)
    (hwc : tabWC CFSG.KD.LyOm.BC PI WC nc = true)
    (hnode : ∀ i < n, cNode CFSG.KD.LyOm.BC KX PT WT GT WC nc n i = true)
    (hsg : ∀ k < n, getRec SG 20 k < n)
    (hsort : ∀ k, k + 1 < n → cKey KX PT (getRec SG 20 k) < cKey KX PT (getRec SG 20 (k + 1)))
    (hn : 0 < n) (cUT : LCanon 12 7 111 UT) (eUT : blkM UT = (mat g * lyU)ᵀ)
    (hroot : rootOK CFSG.KD.LyOm.BC KX PT PI (bMul CFSG.KD.LyOm.BC UT CFSG.KD.LyOm.T) = true) :
    ∃ sp : ℕ → LySp, (∀ i < n, sp i ∈ orbit (stabilizer lyH F) (imOp (g • opE))) ∧
      (∀ i < n, ∀ j < n, sp i = sp j → i = j) := by
  obtain ⟨c0, e0⟩ := pw_facts w0 hw0
  obtain ⟨c1, e1⟩ := pw_facts w1 hw1
  have inv : ∀ (P : ℕ) (f : J), Tm * bigM P * TIm = (mat f)ᵀ →
      bigM P * (TIm * (mat f⁻¹)ᵀ * Tm) = 1 := by
    intro P f hP
    have eP : bigM P = TIm * (mat f)ᵀ * Tm := by
      rw [← hP]
      calc bigM P = (TIm * Tm) * bigM P * (TIm * Tm) := by
            rw [t_facts.2, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [eP]
    calc TIm * (mat f)ᵀ * Tm * (TIm * (mat f⁻¹)ᵀ * Tm)
        = TIm * ((mat f)ᵀ * (Tm * TIm) * (mat f⁻¹)ᵀ) * Tm := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [t_facts.1, Matrix.mul_one, mat_transpose_inv, Matrix.mul_one, t_facts.2]
  have hnc8 : nc ≤ 8 := by omega
  obtain ⟨hcan, hstep, hinj⟩ := chart_tree (KX := KX) (PT := PT) (WT := WT) (GT := GT) (WC := WC)
    (PI := PI) (PJ := PJ) (SG := SG) (n := n) (nc := nc) (G0 := CFSG.KD.LyOm.PW w0)
    (G1 := CFSG.KD.LyOm.PW w1) hnc8 ⟨c0, c1⟩ ⟨inv _ _ e0, inv _ _ e1⟩ hpi
    (fun s hs c hc c' hc' => by
      have h1 : c = 0 := by omega
      have h2 : c' = 0 := by omega
      subst h1 h2
      have := tabGT_sound hgt s (by omega) (by omega) (by omega) (by omega)
      have e3 : s % 2 = s := Nat.mod_eq_of_lt hs
      have e4 : s / 2 % 8 = 0 := by omega
      have e5 : s / 16 = 0 := by omega
      rw [e3, e4, e5] at this
      simpa using this)
    hwc hnode hsg hsort
  have hr := root_space (hcan 0 hn) hpi hnc8 cUT eUT hroot
  refine ⟨fun i => ⟨rs (blkM (getRec KX 9324 i) * bigM (PJ (chartOf (getRec PT 32 i))) * TIm)⟩,
    fun i hi => ?_, fun i hi j hj e => hinj i hi j hj (congrArg LySp.V e)⟩
  refine mem_orbit_of_tree (G := stabilizer lyH F) (X := LySp) (imOp (g • opE))
    (fun i => (⟨rs (blkM (getRec KX 9324 i) * bigM (PJ (chartOf (getRec PT 32 i))) * TIm)⟩ : LySp))
    (fun i => fldW (getRec PT 32 i) 0 20) n
    ?_ (fun i hi0 hi => ?_) i hi
  · rw [imOp_smul_opE]
    exact LySp.ext hr
  · obtain ⟨hp, hl, he⟩ := hstep i hi hi0
    set s := fldW (getRec PT 32 i) 20 4
    refine ⟨hp, ?_⟩
    by_cases h0 : s = 0
    · have hm : Tm * bigM (pickL [CFSG.KD.LyOm.PW w0, CFSG.KD.LyOm.PW w1] s) * TIm =
          (mat (wordJ w0))ᵀ := by
        rw [h0]
        exact e0
      refine ⟨⟨⟨wordJ w0, wordJ_mem w0⟩, hs0⟩, ?_⟩
      rw [Subgroup.smul_def, Subgroup.smul_def]
      rw [← step_smul hm]
      exact LySp.ext he
    · have h1 : s = 1 := by omega
      have hm : Tm * bigM (pickL [CFSG.KD.LyOm.PW w0, CFSG.KD.LyOm.PW w1] s) * TIm =
          (mat (wordJ w1))ᵀ := by
        rw [h1]
        exact e1
      refine ⟨⟨⟨wordJ w1, wordJ_mem w1⟩, hs1⟩, ?_⟩
      rw [Subgroup.smul_def, Subgroup.smul_def]
      rw [← step_smul hm]
      exact LySp.ext he

theorem beta_smulH
    [LySeed] (h : lyH) (x : LyOperator) : beta (h • x) = h • beta x := by
  rw [Subgroup.smul_def]
  exact beta_smul h x

@[expose] def pairOp (x : LyOperator) : Form7 × LySp := (beta x, imOp x)

theorem pairOp_smulH
    [LySeed] (h : lyH) (x : LyOperator) : pairOp (h • x) = h • pairOp x := by
  unfold pairOp
  rw [beta_smulH, imOp_smulS]
  rfl

theorem card_of_fiber_pair
    [LySeed] (p : LyOperator) (F : Form7) {nA nB : ℕ}
    (fA : ℕ → Form7) (hA : ∀ i < nA, fA i ∈ orbit lyH F)
    (hAi : ∀ i < nA, ∀ j < nA, fA i = fA j → i = j) (sp : ℕ → LySp)
    (hB : ∀ i < nB, sp i ∈ orbit (stabilizer lyH F) (imOp p))
    (hBi : ∀ i < nB, ∀ j < nB, sp i = sp j → i = j) :
    nA * nB ≤ Nat.card (orbit lyH ((F, imOp p) : Form7 × LySp)) := by
  have hAs : Set.range (fun i : Fin nA => fA i) ⊆ orbit lyH ((F, imOp p) : Form7 × LySp).1 := by
    rintro _ ⟨i, rfl⟩
    exact hA i i.2
  have hAc : (Set.range (fun i : Fin nA => fA i)).ncard = nA := by
    rw [Set.ncard_range_of_injective (fun i j e => Fin.ext (hAi i i.2 j j.2 e)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hBs : Set.range (fun i : Fin nB => ((F, sp i) : Form7 × LySp)) ⊆
      orbit (stabilizer lyH ((F, imOp p) : Form7 × LySp).1) ((F, imOp p) : Form7 × LySp) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB i i.2
    refine ⟨k, ?_⟩
    have hkF : (k : lyH) • F = F := k.2
    change ((k : lyH) • F, (k : lyH) • imOp p) = (F, sp i)
    rw [hkF]
    exact Prod.ext rfl hk
  have hBc : (Set.range (fun i : Fin nB => ((F, sp i) : Form7 × LySp))).ncard = nB := by
    rw [Set.ncard_range_of_injective (fun i j e => Fin.ext (hBi i i.2 j j.2 (congrArg Prod.snd e))),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have := mul_card_le_card_orbit (H := lyH) (X := Form7 × LySp) Prod.fst (fun h x => Prod.smul_fst h x)
    ((F, imOp p) : Form7 × LySp) _ hAs _ hBs
  rw [hAc, hBc] at this
  exact this

theorem card_of_fiber
    [LySeed] (p : LyOperator) (F : Form7) (hF : beta p = F) {nA nB : ℕ}
    (fA : ℕ → Form7) (hA : ∀ i < nA, fA i ∈ orbit lyH F)
    (hAi : ∀ i < nA, ∀ j < nA, fA i = fA j → i = j) (sp : ℕ → LySp)
    (hB : ∀ i < nB, sp i ∈ orbit (stabilizer lyH F) (imOp p))
    (hBi : ∀ i < nB, ∀ j < nB, sp i = sp j → i = j) :
    nA * nB ≤ Nat.card (orbit lyH p) := by
  subst hF
  obtain ⟨B, hBs, hBc⟩ := fiber_set (G := lyH) (stabilizer lyH (beta p)) imOp (imOp_smulS lyH) p nB
    sp hB hBi
  have hAs : Set.range (fun i : Fin nA => fA i) ⊆ orbit lyH (beta p) := by
    rintro _ ⟨i, rfl⟩
    exact hA i i.2
  have hAc : (Set.range (fun i : Fin nA => fA i)).ncard = nA := by
    rw [Set.ncard_range_of_injective (fun i j e => Fin.ext (hAi i i.2 j j.2 e)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have := mul_card_le_card_orbit (H := lyH) beta beta_smulH p _ hAs B hBs
  rw [hAc, hBc] at this
  exact this

end CertificateChecks.KernelLy.Omega

end
