
module

public import Certificates.Kernel.Ly3085.Cent
public import Certificates.Kernel.Ly3085.Omega.Base2
public import CFSG.Sporadic.Ly.OmegaAct
public import CFSG.Certificates.Kernel.LyOmega.PackSound
public import CFSG.Certificates.Kernel.LyOmega.GlueSound
public import CFSG.Certificates.Kernel.LyOmega.SoundB1
public import CFSG.Certificates.Kernel.LyOmega.SoundB2
public import CFSG.Certificates.Kernel.LyOmega.SoundB3
public import CFSG.Certificates.Kernel.LyOmega.SoundB4
public import CFSG.Certificates.Kernel.SporSch.StrNl
public import CFSG.RankThree.Native.LySeedOperator
public import CFSG.LinearAlgebra.SelfAdjointRankFactorization

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm
open CertificateChecks.KernelSporSch
open CFSG.Sporadic.He.Native (toMat toMat_apply toMat_idM toMat_mulM)
open Matrix

set_option maxRecDepth 400000

theorem hBC : CFSG.KC.LyOm.bConstsOK CFSG.KD.LyOm.BC = true := by
  have h := CFSG.KD.LyOm.consts
  generalize CFSG.KD.LyOm.SC = s at h
  generalize CFSG.KD.LyOm.BC = b at h ⊢
  exact (bAnd_true h).1

theorem bigM_toMat (X : ℕ) :
    bigM X = toMat 5 111 (CFSG.KS.SporSch.LyM.unpackL 111 12 1332 X) := by
  ext i j
  rw [toMat_apply, CFSG.KS.SporSch.LyM.unpackL_get i.2 j.2]
  rfl

theorem canon_vld {X : ℕ} (h : LyBS.vld X = true) : LCanon 12 111 111 X := by
  have hc := CFSG.KS.Ord.validM_canon LyBS.consts (LyBSF.hv h)
  refine ⟨?_, fun i hi j hj => ?_⟩
  · have e : 12 * 111 * 111 = 12 * (111 * 111) := by norm_num
    rw [e]
    exact hc.1
  · have := hc.2 (111 * i + j) (by omega)
    unfold CFSG.KS.Ord.lane at this
    have e : 12 * 111 * i + 12 * j = 12 * (111 * i + j) := by ring
    rw [e]
    exact this

theorem eLF : CFSG.KD.LyOm.BC.LF = CFSG.KD.OrdLy.L := by decide +kernel
theorem eHF : CFSG.KD.LyOm.BC.HF = CFSG.KD.OrdLy.H := by decide +kernel
theorem eONE : CFSG.KD.LyOm.BC.ONEF = CFSG.KD.OrdLy.ONE := by decide +kernel

theorem fvld_canon {X : ℕ} (h : CFSG.KC.LyOm.fVld CFSG.KD.LyOm.BC X = true) :
    LCanon 12 111 111 X := by
  unfold CFSG.KC.LyOm.fVld at h
  rw [eLF, eHF] at h
  exact canon_vld h

theorem one_facts : LCanon 12 111 111 CFSG.KD.LyOm.BC.ONEF ∧ bigM CFSG.KD.LyOm.BC.ONEF = 1 := by
  rw [eONE]
  refine ⟨canon_vld LyBSF.vOne, ?_⟩
  rw [bigM_toMat, ← LyBSF.idE, toMat_idM]

theorem fmul {X Y : ℕ} (hX : LCanon 12 111 111 X) (hY : LCanon 12 111 111 Y) :
    LCanon 12 111 111 (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X Y) ∧
      bigM (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X Y) = bigM X * bigM Y :=
  fMul_sound hBC hX hY

theorem bmul {X Y : ℕ} (hX : LCanon 12 7 111 X) (hY : LCanon 12 111 111 Y) :
    LCanon 12 7 111 (CFSG.KC.LyOm.bMul CFSG.KD.LyOm.BC X Y) ∧
      blkM (CFSG.KC.LyOm.bMul CFSG.KD.LyOm.BC X Y) = blkM X * bigM Y :=
  bMul_sound hBC hX hY

theorem smul7 {X Y : ℕ} (hX : LCanon 11 7 7 X) (hY : LCanon 11 7 7 Y) :
    LCanon 11 7 7 (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC X Y) ∧
      smM (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC X Y) = smM X * smM Y :=
  sMul_sound hSC hX hY

theorem beq_eq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem allL_mem {f : ℕ → Bool} : ∀ {l : List ℕ}, CFSG.KD.LyOm.allL f l = true → ∀ x ∈ l, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    obtain ⟨h1, h2⟩ := bAnd_true (a := f y) (b := CFSG.KD.LyOm.allL f l) h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allL_mem h2 x hx

theorem vld_mem {X : ℕ} (hX : X ∈ [CFSG.KD.LyOm.T, CFSG.KD.LyOm.TI, CFSG.KD.LyOm.P0,
    CFSG.KD.LyOm.P1, CFSG.KD.LyOm.PI0, CFSG.KD.LyOm.PI1, CFSG.KD.LyOm.Gt0, CFSG.KD.LyOm.Gt1,
    CFSG.KD.LyOm.FL, CFSG.KD.LyOm.PTA, CFSG.KD.LyOm.PTB, CFSG.KD.LyOm.PYB, CFSG.KD.LyOm.PTT,
    CFSG.KD.LyOm.TTt]) : LCanon 12 111 111 X :=
  fvld_canon (allL_mem CFSG.KD.LyOm.vld X hX)

macro "memL" : tactic => `(tactic| simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

theorem aStar_zero [LySeed] : aStar 0 = a := by
  unfold aStar aStarList
  rw [extendByWords_getD_of_lt _ _ (by simp)]
  rfl

theorem aStar_one [LySeed] : aStar 1 = b := by
  unfold aStar aStarList
  rw [extendByWords_getD_of_lt _ _ (by simp)]
  rfl

theorem af_facts [LySeed] {j : ℕ}
    (hj : j < 7) :
    LCanon 12 111 111 (LySv.AF j) ∧ bigM (LySv.AF j) = mat (aStar j) ∧
      LCanon 12 111 111 (LySv.AI j) ∧ bigM (LySv.AI j) = mat (aStar j)⁻¹ := by
  obtain ⟨v1, v2⟩ := LySvF.vAFi hj
  have r := repM_asArr j
  have hp := LySvF.pairAt_rep7 LySvF.as_rep j
  unfold asArr at r
  rw [LyBSF.b4_eq, hp] at r
  unfold LySv.AFx LySv.AIx at r
  rw [LyBSF.bl hj] at r
  refine ⟨canon_vld v1, ?_, canon_vld v2, ?_⟩
  · rw [bigM_toMat]
    exact r.1
  · rw [bigM_toMat]
    exact r.2

@[expose] def Tm : Matrix (Fin 111) (Fin 111) (ZMod 5) := bigM CFSG.KD.LyOm.T

@[expose] def TIm : Matrix (Fin 111) (Fin 111) (ZMod 5) := bigM CFSG.KD.LyOm.TI

theorem t_facts : Tm * TIm = 1 ∧ TIm * Tm = 1 := by
  have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
  have cTI := vld_mem (X := CFSG.KD.LyOm.TI) (by memL)
  refine ⟨?_, ?_⟩
  · rw [Tm, TIm, ← (fmul cT cTI).2, beq_eq CFSG.KD.LyOm.tti, one_facts.2]
  · rw [Tm, TIm, ← (fmul cTI cT).2, beq_eq CFSG.KD.LyOm.tit, one_facts.2]

theorem mat_transpose_inv [LySeed] (g : J) :
    (mat g)ᵀ * (mat g⁻¹)ᵀ = 1 := by
  rw [← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one]

theorem p_of [LySeed] {g : J} {P PI Gt : ℕ} (cP : LCanon 12 111 111 P)
    (cPI : LCanon 12 111 111 PI) (cGt : LCanon 12 111 111 Gt) (hGt : bigM Gt = (mat g)ᵀ)
    (hp : Nat.beq (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC CFSG.KD.LyOm.T P)
      (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC Gt CFSG.KD.LyOm.T) = true)
    (hpi : Nat.beq (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC P PI) CFSG.KD.LyOm.BC.ONEF = true) :
    Tm * bigM P * TIm = (mat g)ᵀ ∧ Tm * bigM PI * TIm = (mat g⁻¹)ᵀ := by
  have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
  have e1 : Tm * bigM P = (mat g)ᵀ * Tm := by
    rw [Tm, ← (fmul cT cP).2, beq_eq hp, (fmul cGt cT).2, hGt]
  have e2 : bigM P * bigM PI = 1 := by
    rw [← (fmul cP cPI).2, beq_eq hpi, one_facts.2]
  have h1 : Tm * bigM P * TIm = (mat g)ᵀ := by
    rw [e1, Matrix.mul_assoc, t_facts.1, Matrix.mul_one]
  refine ⟨h1, ?_⟩
  have h2 : (Tm * bigM P * TIm) * (Tm * bigM PI * TIm) = 1 := by
    calc (Tm * bigM P * TIm) * (Tm * bigM PI * TIm)
        = Tm * bigM P * (TIm * Tm) * bigM PI * TIm := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [t_facts.2, Matrix.mul_one, Matrix.mul_assoc Tm, e2, Matrix.mul_one, t_facts.1]
  rw [h1] at h2
  calc Tm * bigM PI * TIm = (mat g⁻¹)ᵀ * ((mat g)ᵀ * (Tm * bigM PI * TIm)) := by
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one,
          Matrix.one_mul]
    _ = (mat g⁻¹)ᵀ := by rw [h2, Matrix.mul_one]

theorem p_facts [LySeed] :
    LCanon 12 111 111 CFSG.KD.LyOm.P0 ∧ LCanon 12 111 111 CFSG.KD.LyOm.P1 ∧
    LCanon 12 111 111 CFSG.KD.LyOm.PI0 ∧ LCanon 12 111 111 CFSG.KD.LyOm.PI1 ∧
    Tm * bigM CFSG.KD.LyOm.P0 * TIm = (mat (aStar 2))ᵀ ∧
    Tm * bigM CFSG.KD.LyOm.PI0 * TIm = (mat (aStar 2)⁻¹)ᵀ ∧
    Tm * bigM CFSG.KD.LyOm.P1 * TIm = (mat (aStar 3))ᵀ ∧
    Tm * bigM CFSG.KD.LyOm.PI1 * TIm = (mat (aStar 3)⁻¹)ᵀ := by
  have cP0 := vld_mem (X := CFSG.KD.LyOm.P0) (by memL)
  have cP1 := vld_mem (X := CFSG.KD.LyOm.P1) (by memL)
  have cPI0 := vld_mem (X := CFSG.KD.LyOm.PI0) (by memL)
  have cPI1 := vld_mem (X := CFSG.KD.LyOm.PI1) (by memL)
  have cG0 := vld_mem (X := CFSG.KD.LyOm.Gt0) (by memL)
  have cG1 := vld_mem (X := CFSG.KD.LyOm.Gt1) (by memL)
  have hG0 : bigM CFSG.KD.LyOm.Gt0 = (mat (aStar 2))ᵀ := by
    rw [← beq_eq CFSG.KD.LyOm.gt0, (SB2.fTr_sound (af_facts (j := 2) (by norm_num)).1).2,
      (af_facts (j := 2) (by norm_num)).2.1]
  have hG1 : bigM CFSG.KD.LyOm.Gt1 = (mat (aStar 3))ᵀ := by
    rw [← beq_eq CFSG.KD.LyOm.gt1, (SB2.fTr_sound (af_facts (j := 3) (by norm_num)).1).2,
      (af_facts (j := 3) (by norm_num)).2.1]
  obtain ⟨a0, b0⟩ := p_of cP0 cPI0 cG0 hG0 CFSG.KD.LyOm.p0 CFSG.KD.LyOm.pi0
  obtain ⟨a1, b1⟩ := p_of cP1 cPI1 cG1 hG1 CFSG.KD.LyOm.p1 CFSG.KD.LyOm.pi1
  exact ⟨cP0, cP1, cPI0, cPI1, a0, b0, a1, b1⟩

theorem lyLet_eq [LySeed] {l : ℕ} (hl : l < 4) :
    lyLet l = [aStar 2, aStar 3, (aStar 2)⁻¹, (aStar 3)⁻¹][l]'(by simpa using hl) := by
  unfold lyLet
  rw [List.getD_eq_getElem]

theorem gp_facts [LySeed] {l : ℕ}
    (hl : l < 4) : LCanon 12 111 111 (CFSG.KD.LyOm.GP2 l) ∧
      Tm * bigM (CFSG.KD.LyOm.GP2 l) * TIm = (mat (lyLet l))ᵀ := by
  obtain ⟨c0, c1, c2, c3, e0, e2, e1, e3⟩ := p_facts
  interval_cases l
  · exact ⟨c0, e0⟩
  · exact ⟨c1, e1⟩
  · exact ⟨c2, e2⟩
  · exact ⟨c3, e3⟩

theorem fWord_cons (G : ℕ → ℕ) (X l : ℕ) (w : List ℕ) :
    CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC G X (l :: w) =
      CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC G (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X (G l)) w :=
  strictN_eq' _ _

theorem fWord_append (G : ℕ → ℕ) : ∀ (u v : List ℕ) (X : ℕ),
    CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC G X (u ++ v) =
      CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC G (CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC G X u) v
  | [], v, X => rfl
  | l :: u, v, X => by
    rw [List.cons_append, fWord_cons, fWord_cons, fWord_append G u v]

theorem fWord_nil (G : ℕ → ℕ) (X : ℕ) : CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC G X [] = X := rfl

theorem pw_facts [LySeed] :
    ∀ w : List ℕ, (∀ l ∈ w, l < 4) → LCanon 12 111 111 (CFSG.KD.LyOm.PW w) ∧
      Tm * bigM (CFSG.KD.LyOm.PW w) * TIm = (mat (wordJ w))ᵀ
  | [], _ => by
    refine ⟨one_facts.1, ?_⟩
    change Tm * bigM CFSG.KD.LyOm.BC.ONEF * TIm = (mat (([] : List ℕ).map lyLet).prod)ᵀ
    rw [one_facts.2, Matrix.mul_one, t_facts.1, List.map_nil, List.prod_nil, mat_one,
      Matrix.transpose_one]
  | l :: w, hw => by
    obtain ⟨c, e⟩ := pw_facts w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨cl, el⟩ := gp_facts (hw l List.mem_cons_self)
    have hrev : CFSG.KD.LyOm.PW (l :: w) = CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC
        (CFSG.KD.LyOm.PW w) (CFSG.KD.LyOm.GP2 l) := by
      unfold CFSG.KD.LyOm.PW
      rw [List.reverse_cons, fWord_append, fWord_cons, fWord_nil]
    rw [hrev]
    refine ⟨(fmul c cl).1, ?_⟩
    rw [(fmul c cl).2]
    calc Tm * (bigM (CFSG.KD.LyOm.PW w) * bigM (CFSG.KD.LyOm.GP2 l)) * TIm
        = (Tm * bigM (CFSG.KD.LyOm.PW w) * TIm) * (Tm * bigM (CFSG.KD.LyOm.GP2 l) * TIm) := by
          rw [show (Tm * bigM (CFSG.KD.LyOm.PW w) * TIm) * (Tm * bigM (CFSG.KD.LyOm.GP2 l) * TIm)
              = Tm * bigM (CFSG.KD.LyOm.PW w) * (TIm * Tm) * bigM (CFSG.KD.LyOm.GP2 l) * TIm by
                simp only [Matrix.mul_assoc], t_facts.2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (mat (wordJ (l :: w)))ᵀ := by
          rw [e, el]
          change (mat (wordJ w))ᵀ * (mat (lyLet l))ᵀ = (mat (((l :: w).map lyLet).prod))ᵀ
          rw [List.map_cons, List.prod_cons, mat_mul, Matrix.transpose_mul]
          rfl

@[expose] def abLet [LySeed] (l : ℕ) : J := [a, b, a⁻¹, b⁻¹].getD l 1

@[expose] def abWord [LySeed] (w : List ℕ) : J := (w.map abLet).prod

theorem gab_facts [LySeed] {l : ℕ}
    (hl : l < 4) : LCanon 12 111 111 (CFSG.KD.LyOm.GAB l) ∧
      bigM (CFSG.KD.LyOm.GAB l) = mat (abLet l) := by
  obtain ⟨c0, e0, c0', e0'⟩ := af_facts (j := 0) (by norm_num)
  obtain ⟨c1, e1, c1', e1'⟩ := af_facts (j := 1) (by norm_num)
  rw [aStar_zero] at e0 e0'
  rw [aStar_one] at e1 e1'
  interval_cases l
  · exact ⟨c0, e0⟩
  · exact ⟨c1, e1⟩
  · exact ⟨c0', e0'⟩
  · exact ⟨c1', e1'⟩

theorem gab_word [LySeed] :
    ∀ (w : List ℕ) (X : ℕ), (∀ l ∈ w, l < 4) → LCanon 12 111 111 X →
      LCanon 12 111 111 (CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC CFSG.KD.LyOm.GAB X w) ∧
      bigM (CFSG.KC.LyOm.fWord CFSG.KD.LyOm.BC CFSG.KD.LyOm.GAB X w) = bigM X * mat (abWord w)
  | [], X, _, hX => ⟨hX, by
      change bigM X = bigM X * mat (([] : List ℕ).map abLet).prod
      rw [List.map_nil, List.prod_nil, mat_one, Matrix.mul_one]⟩
  | l :: w, X, hw, hX => by
    obtain ⟨cl, el⟩ := gab_facts (hw l List.mem_cons_self)
    rw [fWord_cons]
    obtain ⟨c, e⟩ := gab_word w _ (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      (fmul hX cl).1
    refine ⟨c, ?_⟩
    rw [e, (fmul hX cl).2, el, Matrix.mul_assoc, ← mat_mul]
    rfl

@[expose] def E7 : Matrix (Fin 7) (Fin 111) (ZMod 5) := fun a j => if j.val = a.val then 1 else 0

theorem up_eq : bigM LySv.UP = lyU * E7 := by
  ext i j
  rw [bigM_toMat, LySvF.up_eq, toMat_apply]
  simp only [CFSG.KS.SporSch.LySev.padU, Matrix.mul_apply, E7]
  rw [CFSG.KS.SporSch.LyM.ofFn_get! _ i.2, CFSG.KS.SporSch.LyM.ofFn_get! _ j.2]
  by_cases hj : j.val < 7
  · rw [if_pos hj, uArr_get i.val i.2 j.val hj]
    rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · simp
    · intro c _ hc
      have : j.val ≠ c.val := fun e => hc (Fin.ext e.symm)
      simp [this]
    · simp
  · rw [if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro c _
    have : j.val ≠ c.val := fun e => hj (e ▸ c.2)
    simp [this]

theorem E7_U : E7 * lyU = 1 := by
  ext a c
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨a.val, by omega⟩]
  · simp only [E7, if_true, one_mul, Matrix.one_apply]
    rw [lyU_pivot a c]
  · intro j _ hj
    have : j.val ≠ a.val := fun e => hj (Fin.ext e)
    simp [E7, this]
  · simp

theorem mul_E7_apply {m : Type*} (M : Matrix m (Fin 7) (ZMod 5)) (r : m) (c : Fin 7) :
    (M * E7) r ⟨c.val, by omega⟩ = M r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · simp [E7]
  · intro c' _ hc
    have : c.val ≠ c'.val := fun e => hc (Fin.ext e.symm)
    simp [E7, this]
  · simp

theorem fldW_eq'' (r o w : ℕ) : CFSG.KC.LL.fldW r o w = r / 2 ^ o % 2 ^ w := fldW_eq r o w

theorem fld_eq (r o : ℕ) {m w : ℕ} (hm : m = 2 ^ w - 1) :
    Nat.land (Nat.shiftRight r o) m = r / 2 ^ o % 2 ^ w := by
  subst hm
  change (r >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fl_eq : bigM CFSG.KD.LyOm.FL = lyF := by
  obtain ⟨hlen, hd⟩ := SB4.digLanesK_sound (by norm_num) CFSG.KD.LyOm.fl
  have hs : (formDigitsTxt.replace "\n" "").toList =
      CFSG.KD.LyOm.LyFDT.chars.filter (· ≠ '\n') := by
    rw [CFSG.KS.SporSch.StrNl.replace_nl, CFSG.KD.LyOm.LyFDT.eq, String.toList_ofList]
    apply List.filter_congr
    intro c _
    by_cases hc : c = '\n' <;> simp [hc]
  ext i j
  rw [lyF, toMat_apply]
  unfold bpForm CFSG.Sporadic.Ly.Native.matOfDigits CFSG.Sporadic.Ly.Native.digitsOf
  simp only
  rw [CFSG.KS.SporSch.LyM.ofFn_get! _ i.2, CFSG.KS.SporSch.LyM.ofFn_get! _ j.2, hs]
  have ht : 111 * i.val + j.val < 12321 := by omega
  have hl : 111 * i.val + j.val < (CFSG.KD.LyOm.LyFDT.chars.filter (· ≠ '\n')).length := by
    rw [hlen]
    exact ht
  rw [getElem!_pos _ _ (by simpa using hl), Array.getElem_map, List.getElem_toArray,
    ← List.getD_eq_getElem _ '0' hl, hd _ ht, Char.toNat_ofNat]
  have hv : (48 + CFSG.KD.LyOm.FL / 2 ^ (1332 * ((111 * i.val + j.val) / 111) +
      12 * ((111 * i.val + j.val) % 111)) % 2 ^ 12).isValidChar := by
    left
    have := Nat.mod_lt (CFSG.KD.LyOm.FL / 2 ^ (1332 * ((111 * i.val + j.val) / 111) +
      12 * ((111 * i.val + j.val) % 111))) (show 0 < 2 ^ 12 by norm_num)
    omega
  rw [if_pos hv]
  have e1 : (111 * i.val + j.val) / 111 = i.val := by omega
  have e2 : (111 * i.val + j.val) % 111 = j.val := by omega
  rw [e1, e2]
  simp only [bigM, ent]
  congr 1
  simp

theorem ss_facts : LCanon 11 7 7 CFSG.KD.LyOm.SS ∧ smM CFSG.KD.LyOm.SS = lySmall := by
  have h := CFSG.KD.LyOm.ss
  generalize hX : CFSG.KD.LyOm.SS = X at h
  generalize hs : CFSG.KD.LyOm.SC = s at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  subst hX hs
  refine ⟨sVld_sound hSC h1, ?_⟩
  have hr := recAnd (p := fun t => Nat.beq (CFSG.KC.LyOm.sEnt CFSG.KD.LyOm.SS (Nat.div t 7)
    (Nat.mod t 7)) (Nat.land (Nat.shiftRight LySv.DG (Nat.mul 4 (Nat.add 777 t))) 15)) 49 h2
  ext i j
  have e := beq_eq (hr (7 * i.val + j.val) (by omega))
  have d1 : Nat.div (7 * i.val + j.val) 7 = i.val := by
    change (7 * i.val + j.val) / 7 = i.val
    omega
  have d2 : Nat.mod (7 * i.val + j.val) 7 = j.val := by
    change (7 * i.val + j.val) % 7 = j.val
    omega
  rw [d1, d2] at e
  unfold CFSG.KC.LyOm.sEnt at e
  rw [fldW_eq] at e
  simp only [smM, ent, lySmall, Matrix.of_apply]
  rw [LySvF.bp_eq, LySvD.bpD_get (by omega)]
  have e3 : 77 * i.val + 11 * j.val = 11 * 7 * i.val + 11 * j.val := by ring
  rw [show Nat.mul 4 (Nat.add 777 (7 * i.val + j.val)) = 4 * (777 + 7 * i.val + j.val) by
    change 4 * (777 + (7 * i.val + j.val)) = _
    ring] at e
  rw [← e]
  rfl

theorem ut_of
    [LySeed] {UT : ℕ} {w : List ℕ} (hw : ∀ l ∈ w, l < 4)
    (h : CFSG.KD.LyOm.utOK UT w = true) :
    LCanon 12 7 111 UT ∧ blkM UT = (mat (abWord w) * lyU)ᵀ := by
  unfold CFSG.KD.LyOm.utOK at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  refine ⟨bVld_sound hBC h1, ?_⟩
  have htr := SB1.trOK_sound h2
  obtain ⟨cw, ew⟩ := gab_word w _ hw one_facts.1
  have cU : LCanon 12 111 111 LySv.UP := canon_vld LySv.vUP
  have eZ := (fmul cw cU).2
  rw [ew, one_facts.2, Matrix.one_mul, up_eq] at eZ
  ext i j
  have e := htr i.val i.2 j.val j.2
  change ent 12 1332 UT i j = _
  rw [← e]
  have e2 := congrFun (congrFun eZ j) ⟨i.val, by omega⟩
  simp only [bigM] at e2
  rw [e2, ← Matrix.mul_assoc]
  exact mul_E7_apply _ j i

theorem pp_of [LySeed] {UT PP : ℕ} {g : J}
    (cUT : LCanon 12 7 111 UT) (eUT : blkM UT = (mat g * lyU)ᵀ)
    (h : CFSG.KD.LyOm.ppOK UT PP = true) :
    LCanon 11 7 7 PP ∧ smM PP = (mat g * lyU)ᵀ * lyF * lyU := by
  unfold CFSG.KD.LyOm.ppOK at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  refine ⟨sVld_sound hSC h1, ?_⟩
  have cFL := vld_mem (X := CFSG.KD.LyOm.FL) (by memL)
  have cU : LCanon 12 111 111 LySv.UP := canon_vld LySv.vUP
  have b1 := bmul cUT cFL
  have b2 := bmul b1.1 cU
  obtain ⟨-, hr⟩ := SB1.relayOK_sound h2
  ext i j
  rw [hr i j]
  have e := congrFun (congrFun b2.2 i) ⟨j.val, by omega⟩
  simp only [blkM] at e
  rw [e, b1.2, eUT, fl_eq, up_eq, ← Matrix.mul_assoc]
  exact mul_E7_apply _ i j

theorem be_of {PP BE : ℕ} (cPP : LCanon 11 7 7 PP) (h : CFSG.KD.LyOm.beOK PP BE = true) :
    LCanon 11 7 7 BE ∧
      smM BE = (smM PP)ᵀ * (smM CFSG.KD.LyOm.SS)ᵀ * smM PP := by
  unfold CFSG.KD.LyOm.beOK at h
  have e := beq_eq h
  obtain ⟨cT, eT⟩ := CFSG.KS.LyOm.Pack.sTr_sound cPP
  obtain ⟨cS, eS⟩ := CFSG.KS.LyOm.Pack.sTr_sound ss_facts.1
  have m1 := smul7 cS cPP
  have m2 := smul7 cT m1.1
  rw [e]
  refine ⟨m2.1, ?_⟩
  rw [m2.2, m1.2, eT, eS, Matrix.mul_assoc]

theorem beta_smul_opE [LySeed] (g : J) :
    (beta (g • opE)).M = ((mat g * lyU)ᵀ * lyF * lyU)ᵀ * lySmallᵀ * ((mat g * lyU)ᵀ * lyF * lyU) := by
  change lyUᵀ * (mat g * lyE * mat g⁻¹)ᵀ * lyF * lyU = _
  have hF : (mat g)ᵀ * lyFᵀ * mat g = lyFᵀ := by
    have := congrArg Matrix.transpose (lyF_form g)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [← Matrix.mul_assoc] at this
    exact this
  have hF' : (mat g⁻¹)ᵀ * lyFᵀ = lyFᵀ * mat g := by
    calc (mat g⁻¹)ᵀ * lyFᵀ = (mat g⁻¹)ᵀ * ((mat g)ᵀ * lyFᵀ * mat g) := by rw [hF]
      _ = (mat g * mat g⁻¹)ᵀ * lyFᵀ * mat g := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = lyFᵀ * mat g := by rw [mat_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  unfold lyE
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc lyUᵀ * ((mat g⁻¹)ᵀ * (lyFᵀ * (lyU * (lySmallᵀ * lyUᵀ)) * (mat g)ᵀ)) * lyF * lyU
      = lyUᵀ * ((mat g⁻¹)ᵀ * lyFᵀ) * lyU * lySmallᵀ * (lyUᵀ * (mat g)ᵀ * lyF * lyU) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hF']
        simp only [Matrix.mul_assoc]

theorem isUnit_det_of_beta {P S B : Matrix (Fin 7) (Fin 7) (ZMod 5)} (h : B = Pᵀ * Sᵀ * P)
    (hB : IsUnit B.det) : IsUnit P.det ∧ IsUnit S.det := by
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose] at hB
  exact ⟨isUnit_of_mul_isUnit_right hB, isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hB)⟩

theorem lyF_symm : lyFᵀ = lyF := by
  have h := CFSG.KD.LyOm.formF
  generalize hX : CFSG.KD.LyOm.FL = X at h
  obtain ⟨h1, -⟩ := bAnd_true h
  subst hX
  have cFL := vld_mem (X := CFSG.KD.LyOm.FL) (by memL)
  rw [← fl_eq, ← (SB2.fTr_sound cFL).2, beq_eq h1]

theorem rep_facts
    [LySeed] {UT PP BE : ℕ} {w : List ℕ} (hw : ∀ l ∈ w, l < 4)
    (hut : CFSG.KD.LyOm.utOK UT w = true) (hpp : CFSG.KD.LyOm.ppOK UT PP = true)
    (hbe : CFSG.KD.LyOm.beOK PP BE = true) :
    LCanon 12 7 111 UT ∧ blkM UT = (mat (abWord w) * lyU)ᵀ ∧
      smM PP = (mat (abWord w) * lyU)ᵀ * lyF * lyU ∧ LCanon 11 7 7 BE ∧
      smM BE = (beta (abWord w • opE)).M := by
  obtain ⟨cUT, eUT⟩ := ut_of hw hut
  obtain ⟨cPP, ePP⟩ := pp_of cUT eUT hpp
  obtain ⟨cBE, eBE⟩ := be_of cPP hbe
  refine ⟨cUT, eUT, ePP, cBE, ?_⟩
  rw [eBE, ePP, ss_facts.2, beta_smul_opE, Matrix.mul_assoc]

theorem wg1_lt : ∀ l ∈ CFSG.KD.LyOm.WG1, l < 4 := by decide +kernel
theorem wg2_lt : ∀ l ∈ CFSG.KD.LyOm.WG2, l < 4 := by decide +kernel
theorem wg3_lt : ∀ l ∈ CFSG.KD.LyOm.WG3, l < 4 := by decide +kernel
theorem wg4_lt : ∀ l ∈ CFSG.KD.LyOm.WG4, l < 4 := by decide +kernel

@[expose] def gRep [LySeed] (c : ℕ) : J :=
  abWord ([CFSG.KD.LyOm.WG1, CFSG.KD.LyOm.WG2, CFSG.KD.LyOm.WG3, CFSG.KD.LyOm.WG4].getD (c - 1) [])

theorem rep1
    [LySeed] :
    LCanon 12 7 111 CFSG.KD.LyOm.UT1 ∧ blkM CFSG.KD.LyOm.UT1 = (mat (gRep 1) * lyU)ᵀ ∧
      smM CFSG.KD.LyOm.PP1 = (mat (gRep 1) * lyU)ᵀ * lyF * lyU ∧ LCanon 11 7 7 CFSG.KD.LyOm.BE1 ∧
      smM CFSG.KD.LyOm.BE1 = (beta (gRep 1 • opE)).M :=
  rep_facts wg1_lt CFSG.KD.LyOm.ut1 CFSG.KD.LyOm.pp1 CFSG.KD.LyOm.be1

theorem rep2
    [LySeed] :
    LCanon 12 7 111 CFSG.KD.LyOm.UT2 ∧ blkM CFSG.KD.LyOm.UT2 = (mat (gRep 2) * lyU)ᵀ ∧
      smM CFSG.KD.LyOm.PP2 = (mat (gRep 2) * lyU)ᵀ * lyF * lyU ∧ LCanon 11 7 7 CFSG.KD.LyOm.BE2 ∧
      smM CFSG.KD.LyOm.BE2 = (beta (gRep 2 • opE)).M :=
  rep_facts wg2_lt CFSG.KD.LyOm.ut2 CFSG.KD.LyOm.pp2 CFSG.KD.LyOm.be2

theorem rep3
    [LySeed] :
    LCanon 12 7 111 CFSG.KD.LyOm.UT3 ∧ blkM CFSG.KD.LyOm.UT3 = (mat (gRep 3) * lyU)ᵀ ∧
      smM CFSG.KD.LyOm.PP3 = (mat (gRep 3) * lyU)ᵀ * lyF * lyU ∧ LCanon 11 7 7 CFSG.KD.LyOm.BE3 ∧
      smM CFSG.KD.LyOm.BE3 = (beta (gRep 3 • opE)).M :=
  rep_facts wg3_lt CFSG.KD.LyOm.ut3 CFSG.KD.LyOm.pp3 CFSG.KD.LyOm.be3

theorem rep4
    [LySeed] :
    LCanon 12 7 111 CFSG.KD.LyOm.UT4 ∧ blkM CFSG.KD.LyOm.UT4 = (mat (gRep 4) * lyU)ᵀ ∧
      smM CFSG.KD.LyOm.PP4 = (mat (gRep 4) * lyU)ᵀ * lyF * lyU ∧ LCanon 11 7 7 CFSG.KD.LyOm.BE4 ∧
      smM CFSG.KD.LyOm.BE4 = (beta (gRep 4 • opE)).M :=
  rep_facts wg4_lt CFSG.KD.LyOm.ut4 CFSG.KD.LyOm.pp4 CFSG.KD.LyOm.be4

theorem beta_parts : CFSG.KD.LyOm.BE1 = 0 ∧ CFSG.KD.LyOm.BE2 ≠ CFSG.KD.LyOm.BE4 ∧
    LCanon 11 7 7 CFSG.KD.LyOm.BI2 ∧
    smM (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC CFSG.KD.LyOm.BE2 CFSG.KD.LyOm.BI2) = 1 ∧
    LCanon 11 7 7 CFSG.KD.LyOm.BI4 ∧
    smM (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC CFSG.KD.LyOm.BE4 CFSG.KD.LyOm.BI4) = 1 ∧
    CFSG.KD.LyOm.BE3 ≠ 0 ∧ LCanon 11 7 7 CFSG.KD.LyOm.X3 ∧ CFSG.KD.LyOm.X3 ≠ 0 ∧
    CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC CFSG.KD.LyOm.X3 CFSG.KD.LyOm.BE3 = 0 := by
  have h := CFSG.KD.LyOm.beta
  generalize h1 : CFSG.KD.LyOm.BE1 = e1 at h
  generalize h2 : CFSG.KD.LyOm.BE2 = e2 at h
  generalize h3 : CFSG.KD.LyOm.BE3 = e3 at h
  generalize h4 : CFSG.KD.LyOm.BE4 = e4 at h
  generalize h5 : CFSG.KD.LyOm.BI2 = i2 at h
  generalize h6 : CFSG.KD.LyOm.BI4 = i4 at h
  generalize h7 : CFSG.KD.LyOm.X3 = x3 at h
  generalize h8 : CFSG.KD.LyOm.SC = sc at h
  obtain ⟨a1, h⟩ := bAnd_true h
  obtain ⟨a2, h⟩ := bAnd_true h
  obtain ⟨a3, h⟩ := bAnd_true h
  obtain ⟨a4, h⟩ := bAnd_true h
  obtain ⟨a5, h⟩ := bAnd_true h
  obtain ⟨a6, h⟩ := bAnd_true h
  obtain ⟨a7, h⟩ := bAnd_true h
  obtain ⟨a8, h⟩ := bAnd_true h
  obtain ⟨a9, a10⟩ := bAnd_true h
  subst h1 h2 h3 h4 h5 h6 h7 h8
  have nb : ∀ {x y : ℕ}, CFSG.KC.Ord.notB (Nat.beq x y) = true → x ≠ y := by
    intro x y hxy e
    subst e
    revert hxy
    unfold CFSG.KC.Ord.notB
    rw [Nat.beq_refl]
    exact Bool.false_ne_true
  refine ⟨beq_eq a1, nb a2, sVld_sound hSC a3, ?_, sVld_sound hSC a5, ?_, nb a7, sVld_sound hSC a8,
    nb a9, beq_eq a10⟩
  · rw [beq_eq a4, smM_one]
  · rw [beq_eq a6, smM_one]

theorem imOp_opE
    [LySeed] :
    imOp opE = ⟨LinearMap.range (Matrix.mulVecLin lyU)⟩ := by
  obtain ⟨-, -, ePP, cBE, eBE⟩ := rep2
  obtain ⟨-, -, cBI, eBI, -⟩ := beta_parts
  have hB : IsUnit (smM CFSG.KD.LyOm.BE2).det := by
    rw [(smul7 cBE cBI).2] at eBI
    exact Matrix.isUnit_det_of_right_inverse eBI
  have eB : smM CFSG.KD.LyOm.BE2 = ((mat (gRep 2) * lyU)ᵀ * lyF * lyU)ᵀ * lySmallᵀ *
      ((mat (gRep 2) * lyU)ᵀ * lyF * lyU) := by
    rw [eBE, beta_smul_opE]
  obtain ⟨hP, hS⟩ := isUnit_det_of_beta eB hB
  set P := (mat (gRep 2) * lyU)ᵀ * lyF * lyU
  have hPT : lyUᵀ * lyF * (mat (gRep 2) * lyU) = Pᵀ := by
    simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, lyF_symm, Matrix.mul_assoc]
  have hPTu : IsUnit Pᵀ.det := by rw [Matrix.det_transpose]; exact hP
  ext1
  apply le_antisymm
  · change LinearMap.range (Matrix.mulVecLin (lyU * lySmall * lyUᵀ * lyF)) ≤ _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hZ : lyE * ((mat (gRep 2) * lyU) * (Pᵀ)⁻¹ * lySmall⁻¹) = lyU := by
      unfold lyE
      calc lyU * lySmall * lyUᵀ * lyF * ((mat (gRep 2) * lyU) * (Pᵀ)⁻¹ * lySmall⁻¹)
          = lyU * lySmall * (lyUᵀ * lyF * (mat (gRep 2) * lyU)) * (Pᵀ)⁻¹ * lySmall⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = lyU := by
            rw [hPT, Matrix.mul_assoc (lyU * lySmall) Pᵀ, Matrix.mul_nonsing_inv _ hPTu,
              Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
    change LinearMap.range (Matrix.mulVecLin lyU) ≤ LinearMap.range (Matrix.mulVecLin lyE)
    rw [← hZ, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _

theorem imOp_smul_opE
    [LySeed] (g : J) :
    imOp (g • opE) = ⟨rs (mat g * lyU)ᵀ⟩ := by
  rw [imOp_smul, imOp_opE]
  ext1
  change (LinearMap.range (Matrix.mulVecLin lyU)).map (Matrix.mulVecLin (mat g)) = _
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, range_eq_rs]

theorem rowU_rinv [LySeed] (g : J) :
    (mat g * lyU)ᵀ * ((mat g⁻¹)ᵀ * E7ᵀ) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mat g)ᵀ,
    ← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one, Matrix.one_mul,
    ← Matrix.transpose_mul, E7_U, Matrix.transpose_one]

theorem vecMulLinear_transpose (M : Matrix (Fin 111) (Fin 111) (ZMod 5)) :
    Matrix.vecMulLinear Mᵀ = Matrix.mulVecLin M := by
  ext v
  simp [Matrix.vecMul_transpose]

end CertificateChecks.KernelLy.Omega

end
