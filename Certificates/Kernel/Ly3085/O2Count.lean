
module

public import Certificates.Kernel.Ly3085.ChartGlue
public import Certificates.Kernel.Ly3085.O2.Bound
public import Certificates.Kernel.Ly3085.O2.K0
public import Certificates.Kernel.Ly3085.O2.K1
public import Certificates.Kernel.Ly3085.O2.K2
public import Certificates.Kernel.Ly3085.O2.K3
public import Certificates.Kernel.Ly3085.O2.K4
public import Certificates.Kernel.Ly3085.O2.K5
public import Certificates.Kernel.Ly3085.O2.K6
public import Certificates.Kernel.Ly3085.O2.K7
public import Certificates.Kernel.Ly3085.O2.K8
public import Certificates.Kernel.Ly3085.O2.K9
public import Certificates.Kernel.Ly3085.O2.K10
public import Certificates.Kernel.Ly3085.O2.K11
public import Certificates.Kernel.Ly3085.O2.K12
public import Certificates.Kernel.Ly3085.O2.K13
public import Certificates.Kernel.Ly3085.O2.K14
public import Certificates.Kernel.Ly3085.O2.K15
public import Certificates.Kernel.Ly3085.O2.K16
public import Certificates.Kernel.Ly3085.O2.K17
public import Certificates.Kernel.Ly3085.O2.K18
public import Certificates.Kernel.Ly3085.O2.K19
public import Certificates.Kernel.Ly3085.O2.K20
public import Certificates.Kernel.Ly3085.O2.K21
public import Certificates.Kernel.Ly3085.O2.K22
public import Certificates.Kernel.Ly3085.O2.K23
public import Certificates.Kernel.Ly3085.O2.K24
public import Certificates.Kernel.Ly3085.O2.K25
public import Certificates.Kernel.Ly3085.O2.K26
public import Certificates.Kernel.Ly3085.O2.K27
public import Certificates.Kernel.Ly3085.O2.K28
public import Certificates.Kernel.Ly3085.O2.K29
public import Certificates.Kernel.Ly3085.O2.K30
public import Certificates.Kernel.Ly3085.O2.CanonK
public import Certificates.Kernel.Ly3085.O2.Neg
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.LyO2

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.treeRange C KX PT P0 P1 n b 1 = true) 15137
  CFSG.KD.LyO2.tree

#kc_forall_tree sortsOK (fun k => CFSG.KC.LyOm.sortChunk KX SG n (4096 * k) 4096 = true) 236
  CFSG.KD.LyO2.sort

#kc_forall_tree canonOK (fun k => CFSG.KC.LyOm.canonRange KX (512 * k) 512 = true) 29
  CFSG.KD.LyO2.cn

theorem n_eq : n = 968750 := by decide +kernel

theorem key0_normal : ∀ a < 7, ∀ b < 7,
    CFSG.KC.LL.getRec KX 2331 0 / 2 ^ (3 * (111 * a + b)) % 8 = if a = b then 1 else 0 := by
  decide +kernel

end CFSG.KD.LyO2

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open Matrix MulAction

theorem getRec_eq' (blk : ℕ → ℕ) (RB i : ℕ) :
    getRec blk RB i = blk (i / 64) / 2 ^ ((i % 64) * RB) % 2 ^ RB := by
  unfold getRec
  rw [strictN_eq', fldW_eq]
  have e1 : Nat.shiftRight i 6 = i / 64 := by
    change i >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land i 63 = i % 64 := by
    change i &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [e1, e2]
  rfl

theorem mod_div_mod {Y a b c : ℕ} (h : b + c ≤ a) : Y % 2 ^ a / 2 ^ b % 2 ^ c = Y / 2 ^ b % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hq : q < c
  · have : q + b < a := by omega
    simp [hq, this]
  · simp [hq]

theorem o2_fields : ∀ j < CFSG.KD.LyO2.n, ∀ e < 777,
    getRec CFSG.KD.LyO2.KX 2331 j / 2 ^ (3 * e) % 8 < 5 := by
  intro j hj e he
  rw [CFSG.KD.LyO2.n_eq] at hj
  have hb : j / 64 < 15137 := by omega
  have hc : ∀ b, b < 15137 → ∀ e < 49728, CFSG.KD.LyO2.KX b / 2 ^ (3 * e) % 8 < 5 := by
    intro b hb e he
    by_cases hl : b < 14848
    · exact canonRange_sound (CFSG.KD.LyO2.canonOK (b / 512) (by change b / 512 < 29; omega)) b
        (by omega) (by omega) e he
    · exact canonRange_sound CFSG.KD.LyO2.cn29 b (by change 14848 ≤ b; omega)
        (by change b < 14848 + 289; omega) e he
  have := hc (j / 64) hb (777 * (j % 64) + e) (by omega)
  have e8 : (8 : ℕ) = 2 ^ 3 := rfl
  rw [getRec_eq', e8, mod_div_mod (by omega), Nat.div_div_eq_div_mul, ← pow_add]
  rw [show 3 * (777 * (j % 64) + e) = j % 64 * 2331 + 3 * e by ring, e8] at this
  exact this

theorem getRec_lt (blk : ℕ → ℕ) (RB i : ℕ) : getRec blk RB i < 2 ^ RB := by
  rw [getRec_eq']
  exact Nat.mod_lt _ (by positivity)

theorem keyM_inj {k k' : ℕ} (hk : k < 2 ^ 2331) (hk' : k' < 2 ^ 2331)
    (hf : ∀ e < 777, k / 2 ^ (3 * e) % 8 < 5) (hf' : ∀ e < 777, k' / 2 ^ (3 * e) % 8 < 5)
    (h : keyM k = keyM k') : k = k' := by
  have e3 : 3 * 777 = 2331 := by norm_num
  refine lanesW_inj 3 777 k k' (by rw [e3]; exact hk) (by rw [e3]; exact hk') fun q hq => ?_
  have hi : q / 111 < 7 := by omega
  have hj : q % 111 < 111 := Nat.mod_lt _ (by norm_num)
  have e := congrFun (congrFun h ⟨q / 111, hi⟩) ⟨q % 111, hj⟩
  simp only [keyM] at e
  have ho : 111 * (q / 111) + q % 111 = q := by omega
  rw [ho, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hf q hq),
    Nat.mod_eq_of_lt (hf' q hq)] at e
  have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [e8]
  exact e

@[expose] def firstSel (j : Fin 7) : Fin 111 := ⟨j.val, by omega⟩

theorem firstCols_eq (M : Matrix (Fin 7) (Fin 111) (ZMod 5)) :
    firstCols M = M.submatrix id firstSel := rfl

theorem o2_gens [LySeed] :
    LCanon 12 111 111 CFSG.KD.LyO2.P0 ∧ LCanon 12 111 111 CFSG.KD.LyO2.P1 ∧
    bigM CFSG.KD.LyO2.P0 * bigM CFSG.KD.LyO2.PI0 = 1 ∧
    bigM CFSG.KD.LyO2.P1 * bigM CFSG.KD.LyO2.PI1 = 1 ∧
    Tm * bigM CFSG.KD.LyO2.P0 * TIm = (mat (aStar 2))ᵀ ∧
    Tm * bigM CFSG.KD.LyO2.P1 * TIm = (mat (aStar 3))ᵀ := by
  have h := CFSG.KD.LyOm.o2p
  generalize hA : CFSG.KD.LyO2.P0 = A at h ⊢
  generalize hB : CFSG.KD.LyO2.P1 = B at h ⊢
  generalize hC : CFSG.KD.LyO2.PI0 = C at h ⊢
  generalize hD : CFSG.KD.LyO2.PI1 = D at h ⊢
  generalize hA' : CFSG.KD.LyOm.P0 = A' at h
  generalize hB' : CFSG.KD.LyOm.P1 = B' at h
  generalize hC' : CFSG.KD.LyOm.PI0 = C' at h
  generalize hD' : CFSG.KD.LyOm.PI1 = D' at h
  obtain ⟨a1, h⟩ := bAnd_true h
  obtain ⟨a2, h⟩ := bAnd_true h
  obtain ⟨a3, a4⟩ := bAnd_true h
  rw [← beq_eq a1, ← beq_eq a2, ← beq_eq a3, ← beq_eq a4]
  subst hA' hB' hC' hD'
  obtain ⟨cP0, cP1, cPI0, cPI1, e0, -, e1, -⟩ := p_facts
  exact ⟨cP0, cP1, by rw [← (fmul cP0 cPI0).2, beq_eq CFSG.KD.LyOm.pi0, one_facts.2],
    by rw [← (fmul cP1 cPI1).2, beq_eq CFSG.KD.LyOm.pi1, one_facts.2], e0, e1⟩

theorem o2_sort {k : ℕ} (hk : k + 1 < 968750) :
    getRec CFSG.KD.LyO2.SG 20 k < CFSG.KD.LyO2.n ∧
      getRec CFSG.KD.LyO2.SG 20 (k + 1) < CFSG.KD.LyO2.n ∧
      getRec CFSG.KD.LyO2.KX 2331 (getRec CFSG.KD.LyO2.SG 20 k) <
        getRec CFSG.KD.LyO2.KX 2331 (getRec CFSG.KD.LyO2.SG 20 (k + 1)) := by
  by_cases hl : k < 966656
  · exact sortChunk_sound (CFSG.KD.LyO2.sortsOK (k / 4096) (by change k / 4096 < 236; omega)) k
      (by omega) (by omega)
  · exact sortChunk_sound CFSG.KD.LyO2.sort236 k (by change 966656 ≤ k; omega)
      (by change k < 966656 + 2093; omega)

theorem card_orbit_o2_sp
    [LySeed] : 968750 ≤ Nat.card (orbit lyH (imOp (gRep 2 • opE))) := by
  obtain ⟨cG0, cG1, mG0, mG1, eG0, eG1⟩ := o2_gens
  have hf := o2_fields
  have hlt : ∀ j, getRec CFSG.KD.LyO2.KX 2331 j < 2 ^ 2331 := fun j => getRec_lt _ _ _
  have hleaf : ∀ b < 15137, treeLeaf CFSG.KD.LyO2.C CFSG.KD.LyO2.KX CFSG.KD.LyO2.PT
      CFSG.KD.LyO2.P0 CFSG.KD.LyO2.P1 CFSG.KD.LyO2.n b = true := fun b hb =>
    treeRange_sound (CFSG.KD.LyO2.leavesOK b (by change b < 15137; omega)) b (by omega) (by omega)
  have hnode : ∀ i < CFSG.KD.LyO2.n, 0 < i →
      fldW (getRec CFSG.KD.LyO2.PT 21 i) 0 20 < i ∧
        firstCols (keyM (getRec CFSG.KD.LyO2.KX 2331 i)) = 1 ∧
        ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
          keyM (getRec CFSG.KD.LyO2.KX 2331 (fldW (getRec CFSG.KD.LyO2.PT 21 i) 0 20)) *
            bigM (if fldW (getRec CFSG.KD.LyO2.PT 21 i) 20 1 = 0 then CFSG.KD.LyO2.P0
              else CFSG.KD.LyO2.P1) = M * keyM (getRec CFSG.KD.LyO2.KX 2331 i) :=
    fun i hi hi0 => by
    have hi' := hi
    rw [CFSG.KD.LyO2.n_eq] at hi'
    have hKb : CFSG.KD.LyO2.KX (i / 64) < 2 ^ 196608 := by
      have := CFSG.KD.LyO2.kxBound (i / 64) (by omega)
      rwa [Nat.blt_eq] at this
    have := treeLeaf_sound CFSG.KD.LyO2.consts cG0 cG1 hf hKb (hleaf (i / 64) (by omega))
      (r := i % 64) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
    rw [show 64 * (i / 64) + i % 64 = i by omega] at this
    exact this
  have hn0 : firstCols (keyM (getRec CFSG.KD.LyO2.KX 2331 0)) = 1 := by
    ext a b
    simp only [firstCols, keyM, Matrix.one_apply]
    rw [CFSG.KD.LyO2.key0_normal a.val a.2 b.val b.2]
    by_cases h : a = b
    · subst h
      simp
    · have : a.val ≠ b.val := fun e => h (Fin.ext e)
      simp [h, this]
  let G : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5) :=
    fun s => bigM (if s = 0 then CFSG.KD.LyO2.P0 else CFSG.KD.LyO2.P1)
  let Gi : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5) :=
    fun s => bigM (if s = 0 then CFSG.KD.LyO2.PI0 else CFSG.KD.LyO2.PI1)
  have hlab : ∀ x, fldW x 20 1 < 2 := fun x => by
    rw [fldW_eq]
    exact Nat.mod_lt _ (by norm_num)
  obtain ⟨hstep, hinj⟩ := chart_spaces (K := ZMod 5) (n := CFSG.KD.LyO2.n) (nc := 1)
    (N := fun i => keyM (getRec CFSG.KD.LyO2.KX 2331 i)) (ch := fun _ => 0)
    (par := fun i => fldW (getRec CFSG.KD.LyO2.PT 21 i) 0 20)
    (lab := fun i => fldW (getRec CFSG.KD.LyO2.PT 21 i) 20 1)
    (PI := fun _ => 1) (PJ := fun _ => 1) (GT := G) (WC := fun _ => 1) (G := G) (Gi := Gi)
    (T := Tm) (TI := TIm) firstSel
    (fun _ _ => Matrix.mul_one 1)
    (fun s hs c hc c' hc' => by
      have h1 : c = 0 := by omega
      have h2 : c' = 0 := by omega
      subst h1 h2
      simp)
    (fun e c hec hc => absurd hc (by omega))
    (fun s hs => by
      by_cases h : s = 0
      · simp only [G, Gi, h, if_true]
        exact mG0
      · simp only [G, Gi, h, if_false]
        exact mG1)
    t_facts.1
    (fun i hi => by
      refine ⟨by norm_num, ?_, fun e he => absurd he (Nat.not_lt_zero _), fun hi0 => ?_⟩
      · rcases Nat.eq_zero_or_pos i with rfl | hpos
        · rw [← firstCols_eq]
          exact hn0
        · rw [← firstCols_eq]
          exact (hnode i hi hpos).2.1
      · obtain ⟨hp, -, M, hM⟩ := hnode i hi hi0
        refine ⟨hp, hlab _, M, ?_⟩
        simp only [Nat.mul_zero, Nat.add_zero, G]
        exact hM)
    (fun i hi j hj e _ => by
      have ek := keyM_inj (hlt i) (hlt j) (hf i hi) (hf j hj) e
      refine sorted_inj (getRec CFSG.KD.LyO2.KX 2331) (fun k => getRec CFSG.KD.LyO2.SG 20 k)
        (fun k hk => ?_) (fun k hk => ?_) i hi j hj ek
      · have hk' := hk
        rw [CFSG.KD.LyO2.n_eq] at hk'
        by_cases hm : k + 1 < 968750
        · exact (o2_sort hm).1
        · have : k = 968748 + 1 := by omega
          rw [this]
          exact (o2_sort (k := 968748) (by norm_num)).2.1
      · rw [CFSG.KD.LyO2.n_eq] at hk
        exact (o2_sort hk).2.2)
  obtain ⟨cUT, eUT, -⟩ := rep2
  have hroot : rs (keyM (getRec CFSG.KD.LyO2.KX 2331 0) * (1 : Matrix (Fin 111) (Fin 111) (ZMod 5)) * TIm) = rs (mat (gRep 2) * lyU)ᵀ := by
    obtain ⟨cN, eN⟩ := spreadB_sound CFSG.KD.LyO2.consts (hlt 0) (hf 0 (by
      rw [CFSG.KD.LyO2.n_eq]
      norm_num))
    have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
    have b1 := bmul cUT cT
    have hs := sameSpan_sound hBC cN b1.1 CFSG.KD.LyOm.root2
    rw [b1.2, eUT, eN] at hs
    have e : (mat (gRep 2) * lyU)ᵀ = firstCols ((mat (gRep 2) * lyU)ᵀ * Tm) *
        (keyM (getRec CFSG.KD.LyO2.KX 2331 0) * (1 : Matrix (Fin 111) (Fin 111) (ZMod 5)) * TIm) := by
      calc (mat (gRep 2) * lyU)ᵀ = (mat (gRep 2) * lyU)ᵀ * Tm * TIm := by
            rw [Matrix.mul_assoc, t_facts.1, Matrix.mul_one]
        _ = _ := by
            rw [show Tm = bigM CFSG.KD.LyOm.T from rfl]
            nth_rewrite 1 [hs]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
    exact (rs_eq_of_right_inv (rowU_rinv (gRep 2)) e).symm
  let sp : ℕ → LySp := fun i => ⟨rs (keyM (getRec CFSG.KD.LyO2.KX 2331 i) * (1 : Matrix (Fin 111) (Fin 111) (ZMod 5)) * TIm)⟩
  have hmem : ∀ i < CFSG.KD.LyO2.n, sp i ∈ orbit lyH (imOp (gRep 2 • opE)) := by
    refine mem_orbit_of_tree (G := lyH) _ sp (fun i => fldW (getRec CFSG.KD.LyO2.PT 21 i) 0 20) _
      ?_ fun i hi0 hi => ?_
    · rw [imOp_smul_opE]
      exact LySp.ext hroot
    · obtain ⟨hp, -, -⟩ := hnode i hi hi0
      have hl := hlab (getRec CFSG.KD.LyO2.PT 21 i)
      set s := fldW (getRec CFSG.KD.LyO2.PT 21 i) 20 1
      have hm : Tm * G s * TIm = (mat (aStar (s + 2)))ᵀ := by
        by_cases h : s = 0
        · simp only [G, h, if_true]
          exact eG0
        · have h1 : s = 1 := by omega
          simp only [G, h, if_false, h1]
          exact eG1
      refine ⟨hp, ⟨aStar (s + 2), aStar_mem_lyH (by omega)⟩, ?_⟩
      change sp i = aStar (s + 2) • sp _
      rw [← step_smul hm]
      exact LySp.ext (hstep i hi hi0)
  have h := card_le_orbit_of_inj (G := lyH) (fun x : LySp => x) (fun _ _ => rfl)
    (imOp (gRep 2 • opE)) _ sp hmem (fun i hi j hj e => hinj i hi j hj (congrArg LySp.V e))
  rw [CFSG.KD.LyO2.n_eq] at h
  exact h

theorem card_orbit_o2
    [LySeed] : 968750 ≤ Nat.card (orbit lyH (gRep 2 • opE)) :=
  card_orbit_o2_sp.trans (card_orbit_le_of_map imOp (imOp_smulS lyH) _)

end CertificateChecks.KernelLy.Omega

end

end
