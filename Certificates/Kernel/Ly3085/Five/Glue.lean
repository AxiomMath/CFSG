
module

public import CFSG.Certificates.Kernel.LyFive.Sound
public import Certificates.Kernel.LyFiveL1.Checks
public import Certificates.Kernel.Ly3085.ChartGlue
public import Certificates.Kernel.Ly3085.WordFacts
public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.HN.F5Group

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega CFSG.RankThree.Native
  CFSG.RankThree.PartOne.LyFive CFSG.KS.LyOm MulAction
open CFSG.KC.LyFive (wordF powF pow5F elF elW edgeF recF posF abL hL slpF)
open CertificateChecks.KernelSporSch
open Matrix

set_option maxRecDepth 400000

theorem fiveSlpStep_map' {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (r : ℕ → M)
    (ins : FiveIns) : fiveSlpStep (f ∘ r) ins = f ∘ fiveSlpStep r ins := by
  cases ins with
  | mu i j k =>
    funext m
    simp only [fiveSlpStep, Function.comp_apply, Function.update_apply]
    split_ifs <;> simp [map_mul]
  | pwr e i k =>
    funext m
    simp only [fiveSlpStep, Function.comp_apply, Function.update_apply]
    split_ifs <;> simp [map_pow]

theorem fiveSlpRun_map' {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) :
    ∀ (prog : List FiveIns) (r : ℕ → M), fiveSlpRun prog (f ∘ r) = f ∘ fiveSlpRun prog r
  | [], _ => rfl
  | ins :: prog, r => by
    change fiveSlpRun prog (fiveSlpStep (f ∘ r) ins) = f ∘ fiveSlpRun prog (fiveSlpStep r ins)
    rw [fiveSlpStep_map', fiveSlpRun_map' f prog]

theorem bigM_inj {X Y : ℕ} (hX : LCanon 12 111 111 X) (hY : LCanon 12 111 111 Y)
    (h : bigM X = bigM Y) : X = Y := by
  have hb : (12 * 111 * 111 : ℕ) = 12 * 12321 := by norm_num
  refine lanesW_inj 12 12321 X Y (hb ▸ hX.1) (hb ▸ hY.1) fun q hq => ?_
  have hi : q / 111 < 111 := by omega
  have hj : q % 111 < 111 := Nat.mod_lt _ (by norm_num)
  have ho : 12 * 111 * (q / 111) + 12 * (q % 111) = 12 * q := by omega
  have hfX := hX.2 _ hi _ hj
  have hfY := hY.2 _ hi _ hj
  rw [ho] at hfX hfY
  have e := congrFun (congrFun h ⟨q / 111, hi⟩) ⟨q % 111, hj⟩
  simp only [bigM, ent] at e
  have ho' : 1332 * (q / 111) + 12 * (q % 111) = 12 * q := by omega
  rw [ho', ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hfX, Nat.mod_eq_of_lt hfY] at e
  exact e

theorem mat_pow' [LySeed] (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem mat_inv' [LySeed] (g : J) : mat g⁻¹ = (mat g)⁻¹ := by
  have h : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  exact (Matrix.inv_eq_right_inv h).symm

theorem matHom_apply [LySeed] (g : J) : matHom g = mat g := rfl

theorem eq_of_mat_comm [LySeed] {g u w : J} (h : mat g * mat u = mat w * mat g) :
    g * u * g⁻¹ = w := by
  have e : g * u = w * g := mat_injective (by rw [mat_mul, mat_mul, h])
  rw [e, mul_inv_cancel_right]

section

variable [LySeed]

theorem bfacts : CFSG.KC.LyOm.bConstsOK CFSG.KD.LyOm.BC = true := hBC

@[expose] def fLet (l : ℕ) : J := [fiveA, fiveB, fiveA⁻¹, fiveB⁻¹].getD l 1

@[expose] def vJ (j : ℕ) : J := if h : j < 4 then fiveV ⟨j, h⟩ else 1

@[expose] def valJ (l : ℕ) : J :=
  if l < 4 then fiveA ^ (l + 1)
  else if l < 20 then vJ ((l - 4) / 4) ^ ((l - 4) % 4 + 1)
  else if l < 24 then fiveX ^ (l - 19)
  else if l < 27 then ((CFSG.KD.LyFive.TG.getD (l - 24) []).map fLet).prod
  else if l < 34 then aStar (l - 27) else (aStar (l - 34))⁻¹

theorem and' {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := Bool.and_eq_true _ _ ▸ h

theorem lt_len : CFSG.KD.LyFive.LT.length = 27 := by decide

theorem ab_len : CFSG.KD.LyFive.AB.length = 4 := by decide

theorem ug_lt {l : ℕ} (hl : l < 27) : CFSG.KD.LyFive.UG l = CFSG.KD.LyFive.LT.getD l 0 := by
  unfold CFSG.KD.LyFive.UG
  rw [CFSG.KS.LyFive.nIf_eq, if_pos (Nat.blt_eq.mpr hl)]

theorem ug_af {l : ℕ} (h1 : 27 ≤ l) (h2 : l < 34) :
    CFSG.KD.LyFive.UG l = LySv.AF (l - 27) := by
  unfold CFSG.KD.LyFive.UG
  rw [CFSG.KS.LyFive.nIf_eq, if_neg (fun e => by have h3 : l < 27 := Nat.blt_eq.mp e; omega),
    CFSG.KS.LyFive.nIf_eq, if_pos (Nat.blt_eq.mpr h2)]
  rfl

theorem ug_ai {l : ℕ} (h1 : 34 ≤ l) :
    CFSG.KD.LyFive.UG l = LySv.AI (l - 34) := by
  unfold CFSG.KD.LyFive.UG
  rw [CFSG.KS.LyFive.nIf_eq, if_neg (fun e => by have h3 : l < 27 := Nat.blt_eq.mp e; omega),
    CFSG.KS.LyFive.nIf_eq, if_neg (fun e => by have h3 : l < 34 := Nat.blt_eq.mp e; omega)]
  rfl

theorem vld_lt {l : ℕ} (hl : l < 27) : LCanon 12 111 111 (CFSG.KD.LyFive.UG l) := by
  rw [ug_lt hl]
  refine fvld_canon (allL_mem CFSG.KD.LyFive.vld _ (List.mem_append_left _ ?_))
  rw [List.getD_eq_getElem _ _ (by rw [lt_len]; exact hl)]
  exact List.getElem_mem _

theorem vld_ab {l : ℕ} (hl : l < 4) : LCanon 12 111 111 (CFSG.KD.LyFive.GA l) := by
  unfold CFSG.KD.LyFive.GA
  refine fvld_canon (allL_mem CFSG.KD.LyFive.vld _ (List.mem_append_right _ ?_))
  rw [List.getD_eq_getElem _ _ (by rw [ab_len]; exact hl)]
  exact List.getElem_mem _

theorem r0_rep : CFSG.KS.LyFive.RegRep CFSG.KD.LyFive.R0 (matHom ∘ fiveInit a b) := by
  have hs : (List.replicate 65 CFSG.KD.LyOm.BC.ONEF).length = 65 := List.length_replicate
  have hs' : ((List.replicate 65 CFSG.KD.LyOm.BC.ONEF).set 1 (LySv.AF 0)).length = 65 := by
    rw [List.length_set, hs]
  refine ⟨by unfold CFSG.KD.LyFive.R0; rw [List.length_set, hs'], fun k hk => ?_⟩
  unfold CFSG.KD.LyFive.R0
  rw [CFSG.KS.LyFive.getD_set_eq _ _ _ _ (by rw [hs']; norm_num),
    CFSG.KS.LyFive.getD_set_eq _ _ _ _ (by rw [hs]; norm_num)]
  obtain ⟨c0, e0, -⟩ := af_facts (j := 0) (by norm_num)
  obtain ⟨c1, e1, -⟩ := af_facts (j := 1) (by norm_num)
  rw [aStar_zero] at e0
  rw [aStar_one] at e1
  simp only [Function.comp_apply, fiveInit]
  by_cases h2 : k = 2
  · subst h2
    simp only [↓reduceIte, show (2 : ℕ) ≠ 1 by decide]
    exact ⟨c1, e1⟩
  · by_cases h1 : k = 1
    · subst h1
      simp only [↓reduceIte, show (1 : ℕ) ≠ 2 by decide]
      exact ⟨c0, e0⟩
    · simp only [h1, h2, ↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by rw [hs]; exact hk), List.getElem_replicate, map_one]
      exact one_facts

theorem prog_lt : ∀ ins ∈ lyFiveProg, CFSG.KS.LyFive.InsLt ins := by
  have h : lyFiveProg.all CFSG.KS.LyFive.insLtB = true := by decide +kernel
  intro ins hins
  exact CFSG.KS.LyFive.insLt_of (List.all_eq_true.mp h ins hins)

theorem slp_rep : CFSG.KS.LyFive.RegRep (slpF CFSG.KD.LyOm.BC CFSG.KD.LyFive.R0 lyFiveProg)
    (matHom ∘ fiveSlpRun lyFiveProg (fiveInit a b)) := by
  have h := CFSG.KS.LyFive.slpF_sound bfacts one_facts lyFiveProg r0_rep prog_lt
  rwa [fiveSlpRun_map'] at h

theorem ga_facts : ∀ l < 4, LCanon 12 111 111 (CFSG.KD.LyFive.GA l) ∧
    bigM (CFSG.KD.LyFive.GA l) = mat (fLet l) := by
  obtain ⟨s1, s2⟩ := and' CFSG.KD.LyFive.slp
  obtain ⟨i1, i2⟩ := and' CFSG.KD.LyFive.inv
  have g1 : CFSG.KD.LyFive.GA 0 = (slpF CFSG.KD.LyOm.BC CFSG.KD.LyFive.R0 lyFiveProg).getD 1 0 :=
    (CFSG.KS.LyFive.beq_eq s1).symm
  have g2 : CFSG.KD.LyFive.GA 1 = (slpF CFSG.KD.LyOm.BC CFSG.KD.LyFive.R0 lyFiveProg).getD 2 0 :=
    (CFSG.KS.LyFive.beq_eq s2).symm
  have k1 := (slp_rep.2 1 (by norm_num)).2
  have k2 := (slp_rep.2 2 (by norm_num)).2
  rw [Function.comp_apply, matHom_apply] at k1 k2
  have eA : bigM (CFSG.KD.LyFive.GA 0) = mat fiveA := by
    unfold fiveA
    rw [g1, k1]
  have eB : bigM (CFSG.KD.LyFive.GA 1) = mat fiveB := by
    unfold fiveB
    rw [g2, k2]
  have inv_of {g : J} {X Y : ℕ} (hX : LCanon 12 111 111 X) (hY : LCanon 12 111 111 Y)
      (eX : bigM X = mat g) (h : Nat.beq (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X Y)
        CFSG.KD.LyOm.BC.ONEF = true) : bigM Y = mat g⁻¹ := by
    have m := fmul hX hY
    rw [CFSG.KS.LyFive.beq_eq h, one_facts.2, eX] at m
    rw [mat_inv']
    exact (Matrix.inv_eq_right_inv m.2.symm).symm
  intro l hl
  interval_cases l
  · exact ⟨vld_ab (by norm_num), eA⟩
  · exact ⟨vld_ab (by norm_num), eB⟩
  · exact ⟨vld_ab (by norm_num), inv_of (vld_ab (by norm_num)) (vld_ab (by norm_num)) eA i1⟩
  · exact ⟨vld_ab (by norm_num), inv_of (vld_ab (by norm_num)) (vld_ab (by norm_num)) eB i2⟩

theorem ga_word (w : List ℕ) (hw : ∀ l ∈ w, l < 4) :
    LCanon 12 111 111 (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.GA w) ∧
      bigM (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.GA w) = mat ((w.map fLet).prod) := by
  have h := CFSG.KS.LyFive.wordF_sound bfacts one_facts (M := fun l => mat (fLet l)) w
    (fun l hl => ga_facts l (hw l hl))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  change _ = matHom _
  rw [map_list_prod, List.map_map]
  rfl

theorem fLet_abL (z : ℤ) : fLet (abL z) =
    if z = 1 then fiveA else if z = 2 then fiveB else if z = -1 then fiveA⁻¹ else fiveB⁻¹ := by
  by_cases h1 : z = 1
  · simp [abL, fLet, h1]
  · by_cases h2 : z = 2
    · simp [abL, fLet, h2]
    · by_cases h3 : z = -1
      · simp [abL, fLet, h3]
      · simp [abL, fLet, h1, h2, h3]

theorem abL_lt (z : ℤ) : abL z < 4 := by
  unfold abL
  split_ifs <;> norm_num

theorem fiveWord_eq (w : List ℤ) : fiveWord fiveA fiveB w = ((w.map abL).map fLet).prod := by
  unfold fiveWord
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun z _ => (fLet_abL z).symm

theorem ug_step {l X Y : ℕ} {g h : J} (hl : l < 27)
    (e : Nat.beq (CFSG.KD.LyFive.UG l) (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X Y) = true)
    (cX : LCanon 12 111 111 X) (eX : bigM X = mat g) (cY : LCanon 12 111 111 Y)
    (eY : bigM Y = mat h) :
    LCanon 12 111 111 (CFSG.KD.LyFive.UG l) ∧ bigM (CFSG.KD.LyFive.UG l) = mat (g * h) := by
  rw [CFSG.KS.LyFive.beq_eq e]
  have m := fmul cX cY
  exact ⟨m.1, by rw [m.2, eX, eY, mat_mul]⟩

theorem ug_pow_a : (∀ k < 4, LCanon 12 111 111 (CFSG.KD.LyFive.UG k) ∧
      bigM (CFSG.KD.LyFive.UG k) = mat (fiveA ^ (k + 1))) ∧
    ∀ c < 4, LCanon 12 111 111 (CFSG.KD.LyFive.UG (20 + c)) ∧
      bigM (CFSG.KD.LyFive.UG (20 + c)) = mat (fiveX ^ (c + 1)) := by
  obtain ⟨p, p23⟩ := and' CFSG.KD.LyFive.pwA
  obtain ⟨p, p22⟩ := and' p
  obtain ⟨p, p21⟩ := and' p
  obtain ⟨p, p20⟩ := and' p
  obtain ⟨p, p3⟩ := and' p
  obtain ⟨p, p2⟩ := and' p
  obtain ⟨p0, p1⟩ := and' p
  obtain ⟨cA, eA'⟩ := ga_facts 0 (by norm_num)
  have eA : bigM (CFSG.KD.LyFive.GA 0) = mat fiveA := eA'
  have f0 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 0) ∧ bigM (CFSG.KD.LyFive.UG 0) = mat (fiveA ^ 1) := by
    rw [CFSG.KS.LyFive.beq_eq p0, pow_one]
    exact ⟨cA, eA⟩
  have f1 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 1) ∧
      bigM (CFSG.KD.LyFive.UG 1) = mat (fiveA ^ (1 + 1)) := by
    rw [pow_succ]; exact ug_step (by norm_num) p1 f0.1 f0.2 cA eA
  have f2 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 2) ∧
      bigM (CFSG.KD.LyFive.UG 2) = mat (fiveA ^ (2 + 1)) := by
    rw [pow_succ]; exact ug_step (by norm_num) p2 f1.1 f1.2 cA eA
  have f3 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 3) ∧
      bigM (CFSG.KD.LyFive.UG 3) = mat (fiveA ^ (3 + 1)) := by
    rw [pow_succ]; exact ug_step (by norm_num) p3 f2.1 f2.2 cA eA
  have g0 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 20) ∧
      bigM (CFSG.KD.LyFive.UG 20) = mat fiveX := by
    unfold fiveX
    rw [show fiveA ^ 5 = fiveA ^ (3 + 1) * fiveA from pow_succ fiveA (3 + 1)]
    exact ug_step (by norm_num) p20 f3.1 f3.2 cA eA
  have g1 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 21) ∧
      bigM (CFSG.KD.LyFive.UG 21) = mat (fiveX ^ (1 + 1)) := by
    rw [pow_succ, pow_one]; exact ug_step (by norm_num) p21 g0.1 g0.2 g0.1 g0.2
  have g2 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 22) ∧
      bigM (CFSG.KD.LyFive.UG 22) = mat (fiveX ^ (2 + 1)) := by
    rw [pow_succ]; exact ug_step (by norm_num) p22 g1.1 g1.2 g0.1 g0.2
  have g3 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 23) ∧
      bigM (CFSG.KD.LyFive.UG 23) = mat (fiveX ^ (3 + 1)) := by
    rw [pow_succ]; exact ug_step (by norm_num) p23 g2.1 g2.2 g0.1 g0.2
  refine ⟨fun k hk => ?_, fun c hc => ?_⟩
  · interval_cases k
    · exact f0
    · exact f1
    · exact f2
    · exact f3
  · interval_cases c
    · rw [zero_add, pow_one]; exact g0
    · exact g1
    · exact g2
    · exact g3

theorem ug_v (i : Fin 4) (h : CFSG.KD.LyFive.vOK i = true) : ∀ e < 4,
    LCanon 12 111 111 (CFSG.KD.LyFive.UG (4 + 4 * i.val + e)) ∧
      bigM (CFSG.KD.LyFive.UG (4 + 4 * i.val + e)) = mat (fiveV i ^ (e + 1)) := by
  unfold CFSG.KD.LyFive.vOK at h
  obtain ⟨h, v3⟩ := and' h
  obtain ⟨h, v2⟩ := and' h
  obtain ⟨v0, v1⟩ := and' h
  have hi := i.isLt
  have w := ga_word ((lyFiveVWords i).map abL) (fun l hl => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hl
    exact abL_lt z)
  rw [← fiveWord_eq] at w
  have f0 : LCanon 12 111 111 (CFSG.KD.LyFive.UG (4 + 4 * i.val)) ∧
      bigM (CFSG.KD.LyFive.UG (4 + 4 * i.val)) = mat (fiveV i) := by
    rw [CFSG.KS.LyFive.beq_eq v0]
    exact w
  have f1 : LCanon 12 111 111 (CFSG.KD.LyFive.UG (5 + 4 * i.val)) ∧
      bigM (CFSG.KD.LyFive.UG (5 + 4 * i.val)) = mat (fiveV i ^ (1 + 1)) := by
    rw [pow_succ, pow_one]; exact ug_step (by omega) v1 f0.1 f0.2 f0.1 f0.2
  have f2 : LCanon 12 111 111 (CFSG.KD.LyFive.UG (6 + 4 * i.val)) ∧
      bigM (CFSG.KD.LyFive.UG (6 + 4 * i.val)) = mat (fiveV i ^ (2 + 1)) := by
    rw [pow_succ]; exact ug_step (by omega) v2 f1.1 f1.2 f0.1 f0.2
  have f3 : LCanon 12 111 111 (CFSG.KD.LyFive.UG (7 + 4 * i.val)) ∧
      bigM (CFSG.KD.LyFive.UG (7 + 4 * i.val)) = mat (fiveV i ^ (3 + 1)) := by
    rw [pow_succ]; exact ug_step (by omega) v3 f2.1 f2.2 f0.1 f0.2
  intro e he
  interval_cases e
  · rw [zero_add, pow_one, add_zero]; exact f0
  · rw [show 4 + 4 * i.val + 1 = 5 + 4 * i.val by omega]; exact f1
  · rw [show 4 + 4 * i.val + 2 = 6 + 4 * i.val by omega]; exact f2
  · rw [show 4 + 4 * i.val + 3 = 7 + 4 * i.val by omega]; exact f3

theorem tg_lt : ∀ t < 3, ∀ l ∈ CFSG.KD.LyFive.TG.getD t [], l < 4 := by decide +kernel

theorem ug_facts : ∀ l < 41, LCanon 12 111 111 (CFSG.KD.LyFive.UG l) ∧
    bigM (CFSG.KD.LyFive.UG l) = mat (valJ l) := by
  obtain ⟨hA, hX⟩ := ug_pow_a
  have hV0 := ug_v 0 CFSG.KD.LyFive.pwV0
  have hV1 := ug_v 1 CFSG.KD.LyFive.pwV1
  have hV2 := ug_v 2 CFSG.KD.LyFive.pwV2
  have hV3 := ug_v 3 CFSG.KD.LyFive.pwV3
  obtain ⟨t, t2⟩ := and' CFSG.KD.LyFive.lifts
  obtain ⟨t0, t1⟩ := and' t
  have lift : ∀ t < 3, Nat.beq (CFSG.KD.LyFive.UG (24 + t))
      (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.GA (CFSG.KD.LyFive.TG.getD t [])) = true →
      LCanon 12 111 111 (CFSG.KD.LyFive.UG (24 + t)) ∧
        bigM (CFSG.KD.LyFive.UG (24 + t)) = mat (valJ (24 + t)) := by
    intro t ht e
    rw [CFSG.KS.LyFive.beq_eq e]
    have hv : valJ (24 + t) = ((CFSG.KD.LyFive.TG.getD t []).map fLet).prod := by
      unfold valJ
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 24 + t - 24 = t by omega]
    rw [hv]
    exact ga_word _ (tg_lt t ht)
  intro l hl
  by_cases h27 : l < 27
  · interval_cases l
    · exact hA 0 (by norm_num)
    · exact hA 1 (by norm_num)
    · exact hA 2 (by norm_num)
    · exact hA 3 (by norm_num)
    · exact hV0 0 (by norm_num)
    · exact hV0 1 (by norm_num)
    · exact hV0 2 (by norm_num)
    · exact hV0 3 (by norm_num)
    · exact hV1 0 (by norm_num)
    · exact hV1 1 (by norm_num)
    · exact hV1 2 (by norm_num)
    · exact hV1 3 (by norm_num)
    · exact hV2 0 (by norm_num)
    · exact hV2 1 (by norm_num)
    · exact hV2 2 (by norm_num)
    · exact hV2 3 (by norm_num)
    · exact hV3 0 (by norm_num)
    · exact hV3 1 (by norm_num)
    · exact hV3 2 (by norm_num)
    · exact hV3 3 (by norm_num)
    · exact hX 0 (by norm_num)
    · exact hX 1 (by norm_num)
    · exact hX 2 (by norm_num)
    · exact hX 3 (by norm_num)
    · exact lift 0 (by norm_num) t0
    · exact lift 1 (by norm_num) t1
    · exact lift 2 (by norm_num) t2
  · by_cases h34 : l < 34
    · obtain ⟨c, e, -⟩ := af_facts (j := l - 27) (by omega)
      rw [ug_af (by omega) h34]
      refine ⟨c, e.trans ?_⟩
      unfold valJ
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h34]
    · obtain ⟨-, -, c, e⟩ := af_facts (j := l - 34) (by omega)
      rw [ug_ai (by omega)]
      refine ⟨c, e.trans ?_⟩
      unfold valJ
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg h34]

theorem ug_word (w : List ℕ) (hw : ∀ l ∈ w, l < 41) :
    LCanon 12 111 111 (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG w) ∧
      bigM (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG w) = mat ((w.map valJ).prod) := by
  have h := CFSG.KS.LyFive.wordF_sound bfacts one_facts (M := fun l => mat (valJ l)) w
    (fun l hl => ug_facts l (hw l hl))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  change _ = matHom _
  rw [map_list_prod, List.map_map]
  rfl

theorem seg_prod {d l : ℕ} {g : J} (hd : d < 5) (hl : ∀ d', 0 < d' → d' < 5 → d = d' → valJ l = g ^ d) :
    ((if d = 0 then [] else [l]).map valJ).prod = g ^ d := by
  split_ifs with h
  · rw [h, pow_zero]; rfl
  · rw [List.map_singleton, List.prod_singleton]
    exact hl d (by omega) hd rfl

theorem digit_val (m : ℕ) : ((m % 5 : ℕ) : ZMod 5).val = m % 5 := by
  rw [ZMod.val_natCast, Nat.mod_mod]

theorem valJ_a {k : ℕ} (h0 : 0 < k) (h5 : k < 5) : valJ (k - 1) = fiveA ^ k := by
  unfold valJ
  rw [if_pos (by omega), show k - 1 + 1 = k by omega]

theorem valJ_v (i : Fin 4) {e : ℕ} (h0 : 0 < e) (h5 : e < 5) :
    valJ (4 + 4 * i.val + e - 1) = fiveV i ^ e := by
  unfold valJ
  have hi := i.isLt
  rw [if_neg (by omega), if_pos (by omega), show (4 + 4 * i.val + e - 1 - 4) / 4 = i.val by omega,
    show (4 + 4 * i.val + e - 1 - 4) % 4 + 1 = e by omega]
  unfold vJ
  rw [dif_pos hi]

theorem valJ_x {c : ℕ} (h0 : 0 < c) (h5 : c < 5) : valJ (20 + c - 1) = fiveX ^ c := by
  unfold valJ
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 20 + c - 1 - 19 = c by omega]

theorem elW_prod {n : ℕ} (hn : n < 15625) : ((elW n).map valJ).prod = fiveEl n := by
  unfold elW fiveEl fiveNF fiveDigits
  simp only [List.map_append, List.prod_append]
  have hk : n / 3125 < 5 := by omega
  rw [seg_prod (g := fiveA) hk (fun d' h0 h5 e => by rw [e]; exact valJ_a h0 h5),
    seg_prod (g := fiveV 3) (Nat.mod_lt _ (by norm_num)) (fun d' h0 h5 e => by
      rw [e, show 16 + d' - 1 = 4 + 4 * (3 : Fin 4).val + d' - 1 by simp <;> omega]
      exact valJ_v 3 h0 h5),
    seg_prod (g := fiveV 2) (Nat.mod_lt _ (by norm_num)) (fun d' h0 h5 e => by
      rw [e, show 12 + d' - 1 = 4 + 4 * (2 : Fin 4).val + d' - 1 by simp <;> omega]
      exact valJ_v 2 h0 h5),
    seg_prod (g := fiveV 1) (Nat.mod_lt _ (by norm_num)) (fun d' h0 h5 e => by
      rw [e, show 8 + d' - 1 = 4 + 4 * (1 : Fin 4).val + d' - 1 by simp <;> omega]
      exact valJ_v 1 h0 h5),
    seg_prod (g := fiveV 0) (Nat.mod_lt _ (by norm_num)) (fun d' h0 h5 e => by
      rw [e, show 4 + d' - 1 = 4 + 4 * (0 : Fin 4).val + d' - 1 by simp]
      exact valJ_v 0 h0 h5),
    seg_prod (g := fiveX) (Nat.mod_lt _ (by norm_num)) (fun d' h0 h5 e => by
      rw [e]; exact valJ_x h0 h5)]
  simp only [digit_val, Fin.val_zero, Fin.val_one, Fin.val_two]
  have ec : n % 3125 % 5 = n % 5 := by omega
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [ec]
  simp only [v3]
  norm_num only [mul_assoc]

theorem elW_lt {n : ℕ} (hn : n < 15625) : ∀ l ∈ elW n, l < 41 := by
  intro l hl
  unfold elW at hl
  simp only [List.mem_append] at hl
  have hk : n / 3125 < 5 := by omega
  have h1 := Nat.mod_lt (n % 3125 / 625) (show 0 < 5 by norm_num)
  have h2 := Nat.mod_lt (n % 3125 / 125) (show 0 < 5 by norm_num)
  have h3 := Nat.mod_lt (n % 3125 / 25) (show 0 < 5 by norm_num)
  have h4 := Nat.mod_lt (n % 3125 / 5) (show 0 < 5 by norm_num)
  have h5 := Nat.mod_lt n (show 0 < 5 by norm_num)
  split_ifs at hl <;> simp_all <;> omega

theorem el_facts {n : ℕ} (hn : n < 15625) :
    LCanon 12 111 111 (elF CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG n) ∧
      bigM (elF CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG n) = mat (fiveEl n) := by
  have h := ug_word (elW n) (elW_lt hn)
  rw [elW_prod hn] at h
  exact h

end

end CertificateChecks.KernelLy.Omega

end
