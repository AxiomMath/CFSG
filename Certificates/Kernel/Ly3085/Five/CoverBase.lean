
module

public import Certificates.Kernel.Ly3085.Five.Glue
public import Certificates.Kernel.Ly3085.Five.Checks
public import Certificates.Kernel.LyFiveL1.Tree0
public import Certificates.Kernel.LyFiveL1.Tree1
public import Certificates.Kernel.LyFiveL1.Tree2
public import Certificates.Kernel.LyFiveL1.Tree3
public import Certificates.Kernel.LyFiveL1.Base
public import Certificates.Kernel.Ly3085.SqueezeBase
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import Certificates.Kernel.Ly3085.DischargeBase
public import Certificates.Kernel.Ly3085.FactsBase
public import Certificates.Kernel.Ly3085.O1Count
public import Certificates.Kernel.Ly3085.O2Count
public import Certificates.Kernel.Ly3085.O34Count
public import Certificates.Kernel.Ly3085.SimpleBase

@[expose] public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega CFSG.RankThree.Native
  CFSG.RankThree.PartOne.LyFive CFSG.KS.LyOm MulAction
open CFSG.KC.LyFive (wordF powF pow5F elF elW edgeF recF posF abL hL)
open CertificateChecks.KernelSporSch
open Matrix

set_option maxRecDepth 400000

#kc_forall_chunks treeAll (fun k => CFSG.KD.LyFive.treeChk k = true) 88 CFSG.KD.LyFive.treeChk 1

#kc_forall_chunks baseAll (fun k => CFSG.KD.LyFive.baseChk k = true) 100 CFSG.KD.LyFive.baseChk 1

section

variable [LySeed]

theorem x_facts : LCanon 12 111 111 (CFSG.KD.LyFive.UG 20) ∧
    bigM (CFSG.KD.LyFive.UG 20) = mat fiveX := by
  have h := ug_facts 20 (by norm_num)
  have hv : valJ 20 = fiveX := by
    have := valJ_x (c := 1) (by norm_num) (by norm_num)
    rw [pow_one] at this
    exact this
  rwa [hv] at h

theorem v_facts (i : Fin 4) : LCanon 12 111 111 (CFSG.KD.LyFive.UG (4 + 4 * i.val)) ∧
    bigM (CFSG.KD.LyFive.UG (4 + 4 * i.val)) = mat (fiveV i) := by
  have h := ug_facts (4 + 4 * i.val + 1 - 1) (by omega)
  rw [valJ_v i (e := 1) (by norm_num) (by norm_num), pow_one,
    show 4 + 4 * i.val + 1 - 1 = 4 + 4 * i.val by omega] at h
  exact h

theorem y_facts : LCanon 12 111 111
      (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC (CFSG.KD.LyFive.UG 4) (CFSG.KD.LyFive.UG 8)) ∧
    bigM (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC (CFSG.KD.LyFive.UG 4) (CFSG.KD.LyFive.UG 8)) =
      mat fiveY := by
  have h0 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 4) ∧ bigM (CFSG.KD.LyFive.UG 4) = mat (fiveV 0) :=
    v_facts 0
  have h1 : LCanon 12 111 111 (CFSG.KD.LyFive.UG 8) ∧ bigM (CFSG.KD.LyFive.UG 8) = mat (fiveV 1) :=
    v_facts 1
  have m := fmul h0.1 h1.1
  exact ⟨m.1, by rw [m.2, h0.2, h1.2, ← mat_mul]; rfl⟩

theorem rel_facts : (∀ i : Fin 4, fiveX * fiveV i = fiveV i * fiveX) ∧ fiveX ^ 5 = 1 ∧
    fiveY ^ 5 = 1 := by
  obtain ⟨h, y5⟩ := and' CFSG.KD.LyFive.rel
  obtain ⟨h, x5⟩ := and' h
  obtain ⟨h, c3⟩ := and' h
  obtain ⟨h, c2⟩ := and' h
  obtain ⟨c0, c1⟩ := and' h
  have xv : ∀ i : Fin 4, CFSG.KD.LyFive.xvOK i.val = true → fiveX * fiveV i = fiveV i * fiveX := by
    intro i hi
    unfold CFSG.KD.LyFive.xvOK at hi
    have e := CFSG.KS.LyFive.beq_eq hi
    have m1 := fmul x_facts.1 (v_facts i).1
    have m2 := fmul (v_facts i).1 x_facts.1
    apply mat_injective
    rw [mat_mul, mat_mul, ← x_facts.2, ← (v_facts i).2, ← m1.2, ← m2.2, e]
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i
    · exact xv 0 c0
    · exact xv 1 c1
    · exact xv 2 c2
    · exact xv 3 c3
  · obtain ⟨c23, e23⟩ := ug_facts 23 (by norm_num)
    have hv : valJ 23 = fiveX ^ 4 := valJ_x (c := 4) (by norm_num) (by norm_num)
    rw [hv] at e23
    have m := fmul c23 x_facts.1
    rw [CFSG.KS.LyFive.beq_eq x5, one_facts.2, e23, x_facts.2, ← mat_mul] at m
    apply mat_injective
    rw [mat_one, pow_succ]
    exact m.2.symm
  · have p := CFSG.KS.LyFive.pow5F_sound bfacts y_facts.1
    rw [CFSG.KS.LyFive.beq_eq y5, one_facts.2, y_facts.2, ← mat_pow'] at p
    apply mat_injective
    rw [mat_one]
    exact p.2.symm

theorem abLet_abL {z : ℤ} (hz : z = 1 ∨ z = 2) : abLet (abL z) = letterVal seedFam z := by
  rcases hz with rfl | rfl <;> rfl

theorem abLet_inv {z : ℤ} (hz : z = 1 ∨ z = 2) :
    abLet ((abL z + 2) % 4) = (letterVal seedFam z)⁻¹ := by
  rcases hz with rfl | rfl <;> rfl

theorem gab_word' (w : List ℕ) (hw : ∀ l ∈ w, l < 4) :
    LCanon 12 111 111 (wordF CFSG.KD.LyOm.BC CFSG.KD.LyOm.GAB w) ∧
      bigM (wordF CFSG.KD.LyOm.BC CFSG.KD.LyOm.GAB w) = mat ((w.map abLet).prod) := by
  have h := CFSG.KS.LyFive.wordF_sound bfacts one_facts (M := fun l => mat (abLet l)) w
    (fun l hl => gab_facts (hw l hl))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  change _ = matHom _
  rw [map_list_prod, List.map_map]
  rfl

theorem evalWord_eq {t : List ℤ} (ht : ∀ z ∈ t, z = 1 ∨ z = 2) :
    evalWord seedFam t = ((t.map abL).map abLet).prod ∧
      (evalWord seedFam t)⁻¹ = ((((t.reverse.map abL).map fun l => (l + 2) % 4)).map abLet).prod := by
  unfold evalWord
  refine ⟨?_, ?_⟩
  · rw [List.map_map]
    congr 1
    exact (List.map_congr_left fun z hz => abLet_abL (ht z hz)).symm
  · rw [List.prod_inv_reverse, List.map_map, List.map_map, ← List.map_reverse, List.map_map]
    congr 1
    exact (List.map_congr_left fun z hz => abLet_inv (ht z (List.mem_reverse.1 hz))).symm

theorem words_12 : (∀ z ∈ xWord, z = 1 ∨ z = 2) ∧ (∀ z ∈ y3Word, z = 1 ∨ z = 2) ∧
    (∀ z ∈ y1Word, z = 1 ∨ z = 2) := by decide

theorem gx_lt : (∀ l ∈ CFSG.KD.LyFive.GX, l < 41) ∧ (∀ l ∈ CFSG.KD.LyFive.GY, l < 41) := by
  decide +kernel

theorem tw_lt : (∀ l ∈ CFSG.KD.LyFive.tAW, l < 41) ∧ (∀ l ∈ CFSG.KD.LyFive.tBW, l < 41) := by
  decide

theorem valJ_hL {l : ℕ} (hl : l < 4) : valJ (hL l) = lyLet l := by
  interval_cases l <;> rfl

theorem wordJ_eq (w : List ℕ) (hw : ∀ l ∈ w, l < 4) : wordJ w = ((w.map hL).map valJ).prod := by
  unfold wordJ
  rw [List.map_map]
  congr 1
  exact (List.map_congr_left fun l hl => valJ_hL (hw l hl)).symm

theorem conj_of_check {G : List ℕ} (hG : ∀ l ∈ G, l < 41) {w : List ℕ} (hw : ∀ l ∈ w, l < 4)
    {X : ℕ} {r : J} (cX : LCanon 12 111 111 X) (eX : bigM X = mat r)
    (h : CFSG.KC.LL.letB (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG G) (fun g =>
      Nat.beq (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC g
        (wordF CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG (w.map hL)))
        (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X g)) = true) :
    ∃ g : J, g * wordJ w * g⁻¹ = r := by
  rw [CFSG.KS.LyFive.letB_eq] at h
  obtain ⟨cg, eg⟩ := ug_word G hG
  have hw' : ∀ l ∈ w.map hL, l < 41 := fun l hl => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
    have := hw m hm
    interval_cases m <;> decide
  obtain ⟨ct, et⟩ := ug_word _ hw'
  rw [← wordJ_eq w hw] at et
  refine ⟨(G.map valJ).prod, eq_of_mat_comm ?_⟩
  have m1 := fmul cg ct
  have m2 := fmul cX cg
  rw [← eg, ← et, ← eX, ← m1.2, ← m2.2, CFSG.KS.LyFive.beq_eq h]

theorem conj_tA : ∃ g : J, g * lyTA * g⁻¹ = fiveX :=
  conj_of_check gx_lt.1 (by decide) x_facts.1 x_facts.2 CFSG.KD.LyFive.gx

theorem conj_tB : ∃ g : J, g * lyTB * g⁻¹ = fiveY :=
  conj_of_check gx_lt.2 (by decide) y_facts.1 y_facts.2 CFSG.KD.LyFive.gy

def RelF (u : J) : Prop :=
  ∃ g : J, ∃ r ∈ ({fiveX, fiveY} : Set J), ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧ g * u * g⁻¹ = r ^ m

theorem relF_conj {u v t : J} (h : t * u * t⁻¹ = v) (hu : RelF u) : RelF v := by
  obtain ⟨g, r, hr, m, h1, h4, e⟩ := hu
  refine ⟨g * t⁻¹, r, hr, m, h1, h4, ?_⟩
  rw [← e, ← h]
  group

theorem relF_pow {u v : J} {j : ℕ} (hj2 : 2 ≤ j) (hj4 : j ≤ 4) (h : u ^ j = v) (hu : RelF u) :
    RelF v := by
  obtain ⟨g, r, hr, m, h1, h4, e⟩ := hu
  have r5 : r ^ 5 = 1 := by
    rcases hr with rfl | rfl
    · exact rel_facts.2.1
    · exact rel_facts.2.2
  refine ⟨g, r, hr, m * j % 5, ?_, ?_, ?_⟩
  · interval_cases m <;> interval_cases j <;> norm_num
  · have := Nat.mod_lt (m * j) (show 0 < 5 by norm_num)
    omega
  · rw [← h, ← conj_pow, e, ← pow_mul]
    conv_lhs => rw [← Nat.div_add_mod (m * j) 5, pow_add, pow_mul, r5, one_pow, one_mul]

theorem bw_lt : ∀ j < 17, ∀ l ∈ CFSG.KD.LyFive.BW.getD j [], l < 41 := by decide +kernel

theorem cj_lt : ∀ l < 8, CFSG.KD.LyFive.CJ.getD l 0 < 41 := by decide

theorem nt_eq : CFSG.KD.LyFive.NT = 5624 := rfl

theorem root_rel {j : ℕ} (hj : j < 17) (hn : CFSG.KD.LyFive.RT.getD j 0 < 15625) :
    RelF (fiveEl (CFSG.KD.LyFive.RT.getD j 0)) := by
  have hb := List.all_eq_true.mp CFSG.KD.LyFive.bridges j (List.mem_range.2 hj)
  unfold CFSG.KD.LyFive.bridgeOK at hb
  rw [CFSG.KS.LyFive.letB_eq] at hb
  obtain ⟨cβ, eβ⟩ := ug_word _ (bw_lt j hj)
  obtain ⟨cu, eu⟩ := el_facts hn
  have hR : ∃ r ∈ ({fiveX, fiveY} : Set J), ∃ R : ℕ, LCanon 12 111 111 R ∧ bigM R = mat r ∧
      Bool.rec (motive := fun _ => ℕ) (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC (CFSG.KD.LyFive.UG 4)
        (CFSG.KD.LyFive.UG 8)) (CFSG.KD.LyFive.UG 20) (Nat.beq (CFSG.KD.LyFive.BT.getD j 0) 0) = R := by
    rw [CFSG.KS.LyFive.nIf_eq]
    split_ifs
    · exact ⟨fiveX, Or.inl rfl, _, x_facts.1, x_facts.2, rfl⟩
    · exact ⟨fiveY, Or.inr rfl, _, y_facts.1, y_facts.2, rfl⟩
  obtain ⟨r, hr, R, cR, eR, hRe⟩ := hR
  rw [hRe] at hb
  refine ⟨((CFSG.KD.LyFive.BW.getD j []).map valJ).prod, r, hr, 1, le_rfl, by norm_num, ?_⟩
  rw [pow_one]
  apply eq_of_mat_comm
  have m1 := fmul cβ cu
  have m2 := fmul cR cβ
  rw [← eβ, ← eu, ← eR, ← m1.2, ← m2.2, CFSG.KS.LyFive.beq_eq hb]

theorem tree_rel : ∀ i < CFSG.KD.LyFive.NT, CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 0 14 < 15625 ∧
    RelF (fiveEl (CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 0 14)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hk : i / 64 < 88 := by rw [nt_eq] at hi; omega
    have hblk : CFSG.KC.LyFive.treeBlk CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG CFSG.KD.LyFive.TB
        CFSG.KD.LyFive.CJ CFSG.KD.LyFive.RT CFSG.KD.LyFive.NT (i / 64) = true := treeAll (i / 64) hk
    have hr := CFSG.KS.LyFive.treeBlk_sound hblk i (by omega) (by omega) hi
    obtain ⟨ho, hr⟩ := hr
    refine ⟨ho, ?_⟩
    rcases hr with ⟨h100, h117, hroot⟩ | ⟨h100, hp, h11, he⟩
    · rw [hroot] at ho ⊢
      exact root_rel (by omega) ho
    · set p := CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 14 13
      obtain ⟨hpo, hpr⟩ := ih p hp (by omega)
      obtain ⟨cp, ep⟩ := el_facts hpo
      obtain ⟨co, eo⟩ := el_facts ho
      obtain ⟨hc, hpw⟩ := CFSG.KS.LyFive.edgeF_sound he
      by_cases h8 : CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 27 7 < 8
      · have e := hc h8
        obtain ⟨ct, et⟩ := ug_facts _ (cj_lt _ h8)
        refine relF_conj (t := valJ (CFSG.KD.LyFive.CJ.getD (CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 27 7) 0))
          (eq_of_mat_comm ?_) hpr
        have m1 := fmul ct cp
        have m2 := fmul co ct
        rw [← et, ← ep, ← eo, ← m1.2, ← m2.2, e]
      · have e := hpw h8
        have pw := CFSG.KS.LyFive.powF_sound bfacts one_facts cp
          (CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 27 7 - 6)
        rw [e, eo, ep, ← mat_pow'] at pw
        exact relF_pow (j := CFSG.KC.LyFive.recF CFSG.KD.LyFive.TB i 27 7 - 6) (by omega) (by omega)
          (mat_injective pw.2.symm) hpr

theorem fiveEl_zero : fiveEl 0 = 1 := by
  simp [fiveEl, fiveNF, fiveDigits]

theorem comm_el_gen {G : Type*} [Group G] (a x : G) (v : Fin 4 → G) (hx : x = a ^ 5)
    (hv : ∀ i, x * v i = v i * x) (k e3 e2 e1 e0 c : ℕ) :
    x * (a ^ k * (v 3 ^ e3 * v 2 ^ e2 * v 1 ^ e1 * v 0 ^ e0 * x ^ c)) =
      a ^ k * (v 3 ^ e3 * v 2 ^ e2 * v 1 ^ e1 * v 0 ^ e0 * x ^ c) * x := by
  have ha : Commute x a := by
    rw [hx]
    exact (Commute.refl a).pow_left 5
  have hv' : ∀ i, Commute x (v i) := fun i => hv i
  have h : Commute x (a ^ k * (v 3 ^ e3 * v 2 ^ e2 * v 1 ^ e1 * v 0 ^ e0 * x ^ c)) :=
    (ha.pow_right k).mul_right (((((hv' 3).pow_right e3).mul_right ((hv' 2).pow_right e2)).mul_right
      ((hv' 1).pow_right e1)).mul_right ((hv' 0).pow_right e0) |>.mul_right
      ((Commute.refl x).pow_right c))
  exact h.eq

theorem pow_comm_J (U Y : J) (h : Y * U = U * Y) : ∀ k : ℕ, Y ^ k * U = U * Y ^ k
  | 0 => by rw [pow_zero, one_mul, mul_one]
  | k + 1 => by
    rw [pow_succ, mul_assoc, h, ← mul_assoc, pow_comm_J U Y h k, mul_assoc]

theorem mul_pow_J (U Y : J) (h : Y * U = U * Y) : ∀ k : ℕ, (U * Y) ^ k = U ^ k * Y ^ k
  | 0 => by rw [pow_zero, pow_zero, pow_zero, mul_one]
  | k + 1 => by
    rw [pow_succ, mul_pow_J U Y h k, pow_succ, pow_succ, mul_assoc, ← mul_assoc (Y ^ k) U Y,
      pow_comm_J U Y h k, mul_assoc, mul_assoc]

theorem pow5_J (U X : J) (hc : X * U = U * X) (hx : X ^ 5 = 1) (c : ℕ) :
    (U * X ^ c) ^ 5 = U ^ 5 := by
  rw [mul_pow_J U (X ^ c) (pow_comm_J U X hc c), ← pow_mul, mul_comm c 5, pow_mul, hx, one_pow,
    mul_one]

theorem x_comm_el (n : ℕ) : fiveX * fiveEl n = fiveEl n * fiveX := by
  have hv := rel_facts.1
  have hx : fiveX = fiveA ^ 5 := rfl
  unfold fiveEl fiveNF
  generalize fiveV = V at hv ⊢
  generalize fiveA = A at hx ⊢
  generalize fiveX = X at hx hv ⊢
  exact comm_el_gen A X V hx hv _ _ _ _ _ _

theorem fiveEl_base {n : ℕ} (hn : n < 15625) : fiveEl n = fiveEl (n - n % 5) * fiveX ^ (n % 5) := by
  have hk : (n - n % 5) / 3125 = n / 3125 := by omega
  have hq : (n - n % 5) % 3125 = n % 3125 - n % 5 := by omega
  have hd : ∀ i : Fin 4, (n % 3125 - n % 5) / 5 ^ (i.val + 1) = n % 3125 / 5 ^ (i.val + 1) := by
    intro i
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have hc0 : (n % 3125 - n % 5) % 5 = 0 := by omega
  have hc : n % 3125 % 5 = n % 5 := by omega
  unfold fiveEl fiveNF fiveDigits
  simp only [digit_val, hk, hq, hd, hc0, hc, Nat.cast_zero, ZMod.val_zero, pow_zero, one_mul,
    mul_one, mul_assoc]

theorem not_pow5 {n : ℕ} (hn : n < 15625)
    (hpos : posF CFSG.KD.LyFive.PB n = 16383) (h1 : fiveEl n ≠ 1) : fiveEl n ^ 5 ≠ 1 := by
  obtain ⟨hq, -⟩ := CFSG.KS.LyFive.posOK_sound CFSG.KD.LyFive.pos n hn
  rcases hq hpos with h0 | ⟨h3125, hb⟩
  · subst h0
    exact absurd fiveEl_zero h1
  · intro h5
    have hc : 25 * ((n - n % 5) / 3125 - 1) + (n - n % 5) % 3125 / 5 / 25 < 100 := by omega
    have hbe : 3125 * (1 + (25 * ((n - n % 5) / 3125 - 1) + (n - n % 5) % 3125 / 5 / 25) / 25) +
        5 * (25 * ((25 * ((n - n % 5) / 3125 - 1) + (n - n % 5) % 3125 / 5 / 25) % 25) +
          (n - n % 5) % 3125 / 5 % 25) = n - n % 5 := by omega
    have hblk : CFSG.KC.LyFive.baseBlk CFSG.KD.LyOm.BC CFSG.KD.LyFive.UG CFSG.KD.LyFive.PB
        (25 * ((n - n % 5) / 3125 - 1) + (n - n % 5) % 3125 / 5 / 25) = true := baseAll _ hc
    have hne := CFSG.KS.LyFive.baseBlk_sound hblk ((n - n % 5) % 3125 / 5 % 25)
      (Nat.mod_lt _ (by norm_num)) (by rw [hbe]; exact hb)
    rw [hbe] at hne
    apply hne
    have hB : mat (fiveEl (n - n % 5)) ^ 5 = 1 := by
      have e : fiveEl n ^ 5 = fiveEl (n - n % 5) ^ 5 := by
        rw [fiveEl_base hn, pow5_J _ _ (x_comm_el (n - n % 5)) rel_facts.2.1]
      rw [← mat_pow', ← e, h5, mat_one]
    have hlt : n - n % 5 < 15625 := by omega
    obtain ⟨ce, ee⟩ := el_facts hlt
    have p := CFSG.KS.LyFive.pow5F_sound bfacts ce
    refine bigM_inj p.1 one_facts.1 ?_
    rw [p.2, ee, hB, one_facts.2]

end

end CertificateChecks.KernelLy.Omega

end
