module

public import Certificates.Kernel.J4R0.Checks
public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentDefs
public import CFSG.Certificates.Kernel.J4R0Sound
public import CFSG.Certificates.Kernel.Common.PcChain
public import CFSG.Certificates.Kernel.J4PentSound
public import Certificates.Kernel.J4Count.FixCEEltBase1

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelJ4R0

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.ZCent CFSG.Quasithin.J4ZCent
open CFSG.Quasithin.J4M2 (gE)
open CFSG.KC.J4Q (mulJ vecJ getN wordJ wordFrom letJ)
open CFSG.KC.J4R0 CFSG.KD.J4Q CFSG.KC.PcChain CFSG.KC.F2Dot
open CertificateChecks.KernelJ4Count.FixCE (PR PR_one PR_mul PR_eq PR_gE inv_smul_PR GL32)
open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)

theorem sN' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by cases y <;> rfl

theorem PR_eq' {g h : J} {a b : ℕ} (hg : PR g a) (hh : PR h b) (e : a = b) : g = h := by
  rw [e] at hg
  exact PR_eq hg hh

theorem PR_wordFrom {gens : ℕ → J} {mats invs : List Nat} :
    ∀ (w : List ℤ), (∀ l ∈ w, PR (letterOf gens l) (letJ one mats invs l)) →
      ∀ (g : J) (acc : Nat), PR g acc →
        PR (g * evalW gens w) (wordFrom c rm one mats invs w acc)
  | [], _, g, acc, h => by rw [evalW_nil, mul_one]; exact h
  | l :: w, hw, g, acc, h => by
    have h1 := PR_mul h (hw l List.mem_cons_self)
    change PR _ (CFSG.KC.Loop.strictN (mulJ c rm acc (letJ one mats invs l))
      (wordFrom c rm one mats invs w))
    rw [sN', evalW_cons, ← mul_assoc]
    exact PR_wordFrom w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _ h1

theorem PR_wordJ {gens : ℕ → J} {mats invs : List Nat} {w : List ℤ}
    (hw : ∀ l ∈ w, PR (letterOf gens l) (letJ one mats invs l)) :
    PR (evalW gens w) (wordJ c rm one mats invs w) := by
  have := PR_wordFrom w hw 1 one PR_one
  rwa [one_mul] at this

theorem letterOf_pos {G : Type*} [Group G] (gens : ℕ → G) (n : ℕ) :
    letterOf gens (Int.ofNat (n + 1)) = gens n := by
  simp [letterOf]

theorem letterOf_neg {G : Type*} [Group G] (gens : ℕ → G) (n : ℕ) :
    letterOf gens (Int.negSucc n) = (gens n)⁻¹ := by
  simp [letterOf, Int.negSucc_lt_zero, Int.neg_negSucc]

theorem GLZ_eq : GLZ = GL32 := rfl

theorem g0W_letters : ∀ i < 16, ∀ l ∈ g0W.getD i [], ∃ n < 32, l = Int.ofNat (n + 1) := by
  decide

theorem headD_mem' {O : List ℕ} (h : O ≠ []) : O.headD 0 ∈ O := by
  cases O with
  | nil => exact absurd rfl h
  | cons a l => exact List.mem_cons_self

attribute [local irreducible] b0El rEl tEl CFSG.Quasithin.J4M2.gE XS BS TS B3I B4I CT SQ SEP NA NB
  CA CB GW RL GLZ

theorem PR_b0El {i : ℕ} (hi : i < 16) : PR (b0El i) (getN one BS i) := by
  rw [(baseOK_spec base_ok).1 i hi, b0El]
  refine PR_wordJ fun l hl => ?_
  obtain ⟨n, hn, rfl⟩ := g0W_letters i hi l hl
  rw [letterOf_pos]
  change PR (gE n) (getN one GLZ n)
  rw [GLZ_eq]
  exact PR_gE hn

theorem b3_inv : (b0El 3)⁻¹ = b0El 3 * b0El 3 * b0El 3 := by
  obtain ⟨-, hB2, hB3, -⟩ := baseOK_spec base_ok
  have h3 := PR_b0El (i := 3) (by norm_num)
  have hc : PR (b0El 3 * (b0El 3 * b0El 3 * b0El 3)) one := by
    rw [← hB3, hB2]
    exact PR_mul h3 (PR_mul (PR_mul h3 h3) h3)
  have h1 : b0El 3 * (b0El 3 * b0El 3 * b0El 3) = 1 := PR_eq hc PR_one
  exact inv_eq_of_mul_eq_one_right h1

theorem b4_inv : (b0El 4)⁻¹ = b0El 4 * b0El 4 := by
  obtain ⟨-, -, -, hB4, hB5, -⟩ := baseOK_spec base_ok
  have h4 := PR_b0El (i := 4) (by norm_num)
  have hc : PR (b0El 4 * (b0El 4 * b0El 4)) one := by
    rw [← hB5, hB4]
    exact PR_mul h4 (PR_mul h4 h4)
  have h1 : b0El 4 * (b0El 4 * b0El 4) = 1 := PR_eq hc PR_one
  exact inv_eq_of_mul_eq_one_right h1

theorem PR_b3i : PR (b0El 3)⁻¹ B3I := by
  obtain ⟨-, hB2, -⟩ := baseOK_spec base_ok
  rw [b3_inv, hB2]
  have h3 := PR_b0El (i := 3) (by norm_num)
  exact PR_mul (PR_mul h3 h3) h3

theorem PR_b4i : PR (b0El 4)⁻¹ B4I := by
  obtain ⟨-, -, -, hB4, -⟩ := baseOK_spec base_ok
  rw [b4_inv, hB4]
  have h4 := PR_b0El (i := 4) (by norm_num)
  exact PR_mul h4 h4

@[expose] def LetOK (w : List ℤ) : Prop :=
  ∀ l ∈ w, (∃ n < 16, l = Int.ofNat (n + 1)) ∨ l = Int.negSucc 3 ∨ l = Int.negSucc 4

theorem rW_letters : ∀ j < 15, LetOK (rW.getD j []) := by
  unfold LetOK
  decide

theorem tW_letters : ∀ i < 60, LetOK (tW.getD i []) := by
  unfold LetOK
  decide

theorem PR_wordB {w : List ℤ} (hw : LetOK w) :
    PR (evalW b0El w) (wordJ c rm one BS [one, one, one, B3I, B4I] w) := by
  refine PR_wordJ fun l hl => ?_
  rcases hw l hl with ⟨n, hn, rfl⟩ | rfl | rfl
  · rw [letterOf_pos]
    exact PR_b0El hn
  · rw [letterOf_neg]
    exact PR_b3i
  · rw [letterOf_neg]
    exact PR_b4i

theorem PR_rEl {j : ℕ} (hj : j < 15) :
    PR (rEl j) (wordJ c rm one BS [one, one, one, B3I, B4I] (rW.getD j [])) := by
  rw [rEl]
  exact PR_wordB (rW_letters j hj)

theorem PR_tEl {i : ℕ} (hi : i < 60) : PR (tEl i) (getN one TS i) := by
  rw [(baseOK_spec base_ok).2.2.2.2.2.2 i hi, tEl]
  exact PR_wordB (tW_letters i hi)

theorem tEl_zero' : tEl 0 = 1 := by
  rw [tEl]
  rfl

@[expose] noncomputable def xE (k : ℕ) : J :=
  if k < 12 ∨ k = 14 then rEl k else if k = 12 then rEl 11 * rEl 12 else rEl 11 * rEl 13

theorem PR_xE {k : ℕ} (hk : k < 15) : PR (xE k) (getN one XS k) := by
  rw [(baseOK_spec base_ok).2.2.2.2.2.1 k hk]
  unfold xw xE
  by_cases h1 : k < 12 ∨ k = 14
  · have hb : (Nat.blt k 12 || Nat.beq k 14) = true := by
      rcases h1 with h | h
      · simp [Nat.blt_eq, h]
      · subst h; rfl
    rw [if_pos h1, hb, cond_true]
    exact PR_rEl hk
  · have hb : (Nat.blt k 12 || Nat.beq k 14) = false := by
      have : k = 12 ∨ k = 13 := by omega
      rcases this with rfl | rfl <;> rfl
    rw [if_neg h1, hb, cond_false]
    have h11 := PR_xE_11
    by_cases h2 : k = 12
    · subst h2
      rw [if_pos rfl]
      exact PR_mul h11 (PR_rEl (by norm_num))
    · have h3 : k = 13 := by omega
      subst h3
      rw [if_neg (by norm_num)]
      exact PR_mul h11 (PR_rEl (by norm_num))
where
  PR_xE_11 : PR (rEl 11) (getN one XS 11) := by
    rw [(baseOK_spec base_ok).2.2.2.2.2.1 11 (by norm_num)]
    exact PR_rEl (by norm_num)

theorem PR_wfrom : ∀ (m k e : ℕ), k + m ≤ 15 → PR (wfrom xE e k m) (wK c rm one XS e k m)
  | 0, _, _, _ => PR_one
  | m + 1, k, e, h => by
    rw [wfrom_succ]
    change PR _ (bif e.testBit k then mulJ c rm (getN one XS k) (wK c rm one XS e (k + 1) m)
      else wK c rm one XS e (k + 1) m)
    cases e.testBit k
    · exact PR_wfrom m (k + 1) e (by omega)
    · exact PR_mul (PR_xE (by omega)) (PR_wfrom m (k + 1) e (by omega))

@[expose] noncomputable def zE (a : ℕ) : J := wfrom xE (a <<< 12) 12 3

theorem PR_zE (a : ℕ) : PR (zE a) (zK c rm one XS a) := PR_wfrom 3 12 _ (by norm_num)

theorem comm_lt {k j : ℕ} (hkj : k < j) (hj : j < 12) :
    ent CT k j < 8 ∧ xE k * xE j = xE j * zE (ent CT k j) * xE k := by
  obtain ⟨hlt, he⟩ := (relOK_spec rel_ok).1 k j hkj hj
  exact ⟨hlt, PR_eq' (PR_mul (PR_xE (by omega)) (PR_xE (by omega)))
    (PR_mul (PR_mul (PR_xE (by omega)) (PR_zE _)) (PR_xE (by omega))) he⟩

theorem sq_lt {k : ℕ} (hk : k < 12) : SQ.getD k 0 < 8 ∧ xE k * xE k = zE (SQ.getD k 0) := by
  obtain ⟨hlt, he⟩ := (relOK_spec rel_ok).2.1 k hk
  exact ⟨hlt, PR_eq' (PR_mul (PR_xE (by omega)) (PR_xE (by omega))) (PR_zE _) he⟩

theorem z_inv {i : ℕ} (h1 : 12 ≤ i) (h2 : i < 15) : xE i * xE i = 1 :=
  PR_eq' (PR_mul (PR_xE h2) (PR_xE h2)) PR_one ((relOK_spec rel_ok).2.2 i h1 h2).1

theorem z_comm {i j : ℕ} (h1 : 12 ≤ i) (h2 : i < 15) (hj : j < 15) :
    xE i * xE j = xE j * xE i :=
  PR_eq' (PR_mul (PR_xE h2) (PR_xE hj)) (PR_mul (PR_xE hj) (PR_xE h2))
    (((relOK_spec rel_ok).2.2 i h1 h2).2 j hj)

theorem zE_comm (a : ℕ) {i : ℕ} (hi : i < 15) : zE a * xE i = xE i * zE a := by
  have h := comm_wfrom (x := xE) (g := xE i) (a <<< 12) 3 12 fun j h1 h2 =>
    (z_comm h1 (by omega) hi).symm
  unfold zE
  exact h.symm

theorem zE_mem (a : ℕ) {k : ℕ} (hk : k ≤ 12) :
    zE a ∈ Subgroup.closure (xE '' Set.Ico k 15) :=
  Subgroup.closure_mono (Set.image_mono fun j (hj : j ∈ Set.Ico 12 15) =>
    (⟨by have := hj.1; omega, hj.2⟩ : j ∈ Set.Ico k 15)) (wfrom_mem' xE _ (by norm_num))

theorem pcRel : PcRel xE 15 where
  sq k hk := by
    rcases Nat.lt_or_ge k 12 with h | h
    · rw [(sq_lt h).2]
      exact zE_mem _ (by omega)
    · rw [z_inv h hk]
      exact Subgroup.one_mem _
  cj k j hkj hj := by
    have hxj : xE j ∈ Subgroup.closure (xE '' Set.Ico (k + 1) 15) :=
      Subgroup.subset_closure ⟨j, ⟨hkj, hj⟩, rfl⟩
    rcases Nat.lt_or_ge j 12 with h | h
    · rw [(comm_lt hkj h).2, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ hxj (zE_mem _ (by omega))
    · rw [← z_comm h hj (by omega : k < 15), mul_inv_cancel_right]
      exact hxj

theorem vecJ_lt (x m : Nat) : vecJ rm x m < 2 ^ 112 := by
  have hrm : rm = 2 ^ 112 - 1 := (CFSG.KC.J4Q.consts_c CertificateChecks.KernelJ4Q.hK).2
  rw [hrm]
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  exact CFSG.KC.J4Pent.testBit_vecJ_ge x m hj

theorem sep {k : ℕ} (hk : k < 15) (e : ℕ) : xE k ≠ wfrom xE e (k + 1) (15 - (k + 1)) := by
  obtain ⟨h0, hlt, hcl, hnot⟩ := sep1_spec (sepOK_spec sep_ok k hk)
  set O := SEP.getD k []
  refine ne_wfrom_of_orbit (X := Row) xE {w | ∃ o ∈ O, w = toRow (toVecD 112 o)} hk ?_
    (v := toRow (toVecD 112 (O.headD 0))) ⟨O.headD 0, headD_mem' h0, rfl⟩ ?_ e
  · rintro _ ⟨o, ho, rfl⟩ j hkj hj
    exact ⟨_, hcl o ho j hkj hj, inv_smul_PR (PR_xE hj) (hlt o ho)⟩
  · rintro ⟨o, ho, he⟩
    rw [inv_smul_PR (PR_xE hk) (hlt _ (headD_mem' h0))] at he
    have := toVecD_injective (vecJ_lt _ _) (hlt o ho) he
    exact hnot (this ▸ ho)

theorem rEl_mem_R0 {j : ℕ} (hj : j < 15) : rEl j ∈ R0 :=
  Subgroup.subset_closure (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

theorem R0_eq : R0 = Subgroup.closure (xE '' Set.Ico 0 15) := by
  have hx : ∀ k < 15, xE k ∈ Subgroup.closure (xE '' Set.Ico 0 15) := fun k hk =>
    Subgroup.subset_closure ⟨k, ⟨Nat.zero_le _, hk⟩, rfl⟩
  apply le_antisymm
  · rw [R0, Subgroup.closure_le]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hj' := List.mem_range.1 hj
    by_cases h1 : j < 12 ∨ j = 14
    · have := hx j hj'
      rwa [xE, if_pos h1] at this
    · have h12 := hx 12 (by norm_num)
      have h13 := hx 13 (by norm_num)
      have h11 := hx 11 (by norm_num)
      rw [xE, if_neg (by norm_num), if_pos rfl] at h12
      rw [xE, if_neg (by norm_num), if_neg (by norm_num)] at h13
      rw [xE, if_pos (Or.inl (by norm_num))] at h11
      have : j = 12 ∨ j = 13 := by omega
      rcases this with rfl | rfl
      · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h11) h12
        rwa [inv_mul_cancel_left] at this
      · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h11) h13
        rwa [inv_mul_cancel_left] at this
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, ⟨-, hk⟩, rfl⟩
    unfold xE
    split_ifs
    · exact rEl_mem_R0 hk
    · exact Subgroup.mul_mem _ (rEl_mem_R0 (by norm_num)) (rEl_mem_R0 (by norm_num))
    · exact Subgroup.mul_mem _ (rEl_mem_R0 (by norm_num)) (rEl_mem_R0 (by norm_num))

theorem card_R0 : Nat.card R0 = 2 ^ 15 := by
  rw [R0_eq]
  exact card_closure pcRel fun k hk e => sep hk e

theorem zE_zero : zE 0 = 1 := by
  unfold zE
  rw [Nat.zero_shiftLeft]
  exact wfrom_zero_e xE 3 12

theorem shift_xor (a b j : ℕ) :
    ((a <<< 12) ^^^ (b <<< 12)).testBit j = ((a ^^^ b) <<< 12).testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_xor]
  cases decide (j ≥ 12) <;> simp

theorem zE_mul {a b : ℕ} : zE a * zE b = zE (a ^^^ b) := by
  have hc : ∀ i j, 12 ≤ i → i < 12 + 3 → 12 ≤ j → j < 12 + 3 → xE i * xE j = xE j * xE i :=
    fun i j h1 h2 _ h4 => z_comm h1 h2 (by omega)
  have hi : ∀ i, 12 ≤ i → i < 12 + 3 → xE i * xE i = 1 := fun i h1 h2 => z_inv h1 h2
  have h := wfrom_mul_xor (x := xE) (a <<< 12) (b <<< 12) 3 12 hc hi
  have h2 : wfrom xE ((a <<< 12) ^^^ (b <<< 12)) 12 3 = wfrom xE ((a ^^^ b) <<< 12) 12 3 :=
    wfrom_congr xE 3 12 fun j _ _ => shift_xor a b j
  exact h.trans h2

theorem zE_eq_one {a : ℕ} (ha : a < 8) (h : zE a = 1) : a = 0 := by
  have h1 : wfrom xE (a <<< 12) (15 - 3) 3 = wfrom xE 0 (15 - 3) 3 := by
    rw [wfrom_zero_e]
    exact h
  have hb := testBit_eq_of_wfrom_eq pcRel (fun k hk e => sep hk e) 3 (by norm_num) _ _ h1
  apply Nat.eq_of_testBit_eq
  intro t
  rcases Nat.lt_or_ge t 3 with ht | ht
  · have := hb (t + 12) (by omega) (by omega)
    rw [Nat.testBit_shiftLeft, Nat.zero_testBit] at this
    simpa [show 12 ≤ t + 12 by omega] using this
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht))

theorem zE_sq (a : ℕ) : zE a * zE a = 1 := by
  rw [zE_mul, Nat.xor_self, zE_zero]

theorem csym_lt (k j : ℕ) : csym CT k j < 8 := by
  unfold csym
  split_ifs with h1 h2 h3
  · exact (comm_lt h2 h1.2).1
  · exact (comm_lt h3 h1.1).1
  · norm_num
  · norm_num

theorem comm_sym {j : ℕ} (hj : j < 12) {i : ℕ} (hi : i < 15) :
    csym CT i j < 2 ^ 3 ∧ xE i * xE j = xE j * xE i * zE (csym CT i j) := by
  refine ⟨csym_lt i j, ?_⟩
  unfold csym
  by_cases h12 : i < 12
  · rw [if_pos ⟨h12, hj⟩]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, (comm_lt h hj).2, mul_assoc, zE_comm _ (by omega), ← mul_assoc]
    · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), zE_zero, mul_one]
    · rw [if_neg (by omega), if_pos h]
      have e := (comm_lt h h12).2
      rw [e, mul_assoc (xE i) (zE _) (xE j), zE_comm _ (show j < 15 by omega)]
      simp only [mul_assoc, zE_sq, mul_one]
  · rw [if_neg (fun h => h12 h.1), zE_zero, mul_one]
    exact z_comm (by omega) hi (by omega)

theorem mem_z_of_central {x : J} (hx : x ∈ R0) (hc : ∀ j < 12, x * xE j = xE j * x) :
    x ∈ Subgroup.closure (xE '' Set.Ico 12 15) := by
  rw [R0_eq] at hx
  obtain ⟨e, he⟩ := exists_wfrom pcRel 15 le_rfl x (by simpa using hx)
  rw [Nat.sub_self] at he
  subst he
  have hphi : ∀ j < 12, phi (csym CT) j e 0 15 = 0 := by
    intro j hj
    obtain ⟨h1, h2⟩ := wfrom_mul_comm (x := xE) (z := zE) (w := 3) (n := 15) zE_zero
      (fun a b _ _ => zE_mul) (fun a _ i hi => zE_comm a hi) (fun i hi => comm_sym hj hi) e 15 0
      (by norm_num)
    rw [hc j hj] at h1
    have h3 : xE j * wfrom xE e 0 15 * zE (phi (csym CT) j e 0 15) =
        xE j * wfrom xE e 0 15 * 1 := by
      rw [mul_one]
      exact h1.symm
    exact zE_eq_one h2 (mul_left_cancel h3)
  have hdot : ∀ q < 36, dotFrom e (colK CT q) 0 15 = false := by
    intro q hq
    rw [colK, ← phi_testBit, hphi (q / 3) (by omega), Nat.zero_testBit]
  have hbits : ∀ p < 12, e.testBit p = false := by
    intro p hp
    obtain ⟨hq, hx⟩ := radOK_spec rad_ok p hp
    exact testBit_eq_false_of_xorL (k := 0) (m := 15) hx (by omega) (by omega) fun a ha => by
      obtain ⟨q, hq', rfl⟩ := List.mem_map.1 ha
      exact hdot q (hq q hq')
  rw [show (15 : ℕ) = 12 + 3 by rfl, wfrom_skip xE e 12 0 3 fun j _ hj => hbits j hj]
  exact wfrom_mem' xE e (by norm_num)

theorem center (x : J) (hx : x ∈ R0) (hc : ∀ r ∈ R0, x * r = r * x) :
    ∀ b ∈ B0, x * b = b * x := by
  have hxR : ∀ j < 15, xE j ∈ R0 := fun j hj => by
    rw [R0_eq]
    exact Subgroup.subset_closure ⟨j, ⟨Nat.zero_le _, hj⟩, rfl⟩
  have hz := mem_z_of_central hx fun j hj => hc _ (hxR j (by omega))
  have hgen : ∀ i < 16, x * b0El i = b0El i * x := by
    intro i hi
    have hzi : ∀ y ∈ Subgroup.closure (xE '' Set.Ico 12 15), y * b0El i = b0El i * y := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hy
        exact PR_eq' (PR_mul (PR_xE hk2) (PR_b0El hi)) (PR_mul (PR_b0El hi) (PR_xE hk2))
          (zbOK_spec zb_ok k hk1 hk2 i hi)
      | one => simp
      | mul y y' _ _ ihy ihy' => rw [mul_assoc, ihy', ← mul_assoc, ihy, mul_assoc]
      | inv y _ ihy =>
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ihy, mul_inv_cancel_right]
    exact hzi x hz
  have hB : B0 ≤ Subgroup.centralizer ({x} : Set J) := by
    rw [B0, Subgroup.closure_le]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hgen i (List.mem_range.1 hi)).symm
  intro b hb
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hB hb)).symm

theorem PR_posFold {a b : J} {A B : ℕ} (ha : PR a A) (hb : PR b B) :
    ∀ (u : List ℕ) (g : J) (acc : ℕ), PR g acc →
      PR (u.foldl (fun acc l => acc * (if l = 0 then a else b)) g)
        (u.foldl (fun acc l => mulJ c rm acc (bif Nat.beq l 0 then A else B)) acc)
  | [], _, _, h => h
  | l :: u, g, acc, h => by
    simp only [List.foldl_cons]
    refine PR_posFold ha hb u _ _ (PR_mul h ?_)
    cases l with
    | zero => exact ha
    | succ n =>
      change PR (if n + 1 = 0 then a else b) B
      rw [if_neg (Nat.succ_ne_zero n)]
      exact hb

theorem posFold_mem {a b : J} {H : Subgroup J} (ha : a ∈ H) (hb : b ∈ H) :
    ∀ (u : List ℕ) (g : J), g ∈ H → u.foldl (fun acc l => acc * (if l = 0 then a else b)) g ∈ H
  | [], _, h => h
  | l :: u, g, h => by
    simp only [List.foldl_cons]
    refine posFold_mem ha hb u _ (Subgroup.mul_mem _ h ?_)
    split
    · exact ha
    · exact hb

theorem wfrom_mem_R0 (e : ℕ) : wfrom xE e 0 15 ∈ R0 := by
  rw [R0_eq]
  exact wfrom_mem' xE e (by norm_num)

theorem conj_mem_R0 {g : J} {G : ℕ} (hg : PR g G) {N : List ℕ}
    (hN : normOK c rm one XS G N = true) : g ∈ Subgroup.normalizer (R0 : Set J) := by
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  rw [R0_eq] at hr ⊢
  induction hr using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, ⟨-, hj⟩, rfl⟩ := hy
    have e := PR_eq' (PR_mul hg (PR_xE hj)) (PR_mul (PR_wfrom 15 0 _ (by norm_num)) hg)
      (normOK_spec hN j hj)
    rw [e, mul_inv_cancel_right]
    exact wfrom_mem' xE _ (by norm_num)
  | one => simp
  | mul y y' _ _ ihy ihy' =>
    have e1 : g * (y * y') * g⁻¹ = (g * y * g⁻¹) * (g * y' * g⁻¹) := by group
    rw [e1]
    exact Subgroup.mul_mem _ ihy ihy'
  | inv y _ ihy =>
    have e1 : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e1]
    exact Subgroup.inv_mem _ ihy

@[expose] noncomputable def Bp : Subgroup J :=
  Subgroup.closure (insert (b0El 4) (insert (b0El 15) (R0 : Set J)))

theorem ha_norm : b0El 4 ∈ Subgroup.normalizer (R0 : Set J) :=
  conj_mem_R0 (PR_b0El (by norm_num)) na_ok

theorem hb_norm : b0El 15 ∈ Subgroup.normalizer (R0 : Set J) :=
  conj_mem_R0 (PR_b0El (by norm_num)) nb_ok

theorem Bp_le_normalizer : Bp ≤ Subgroup.normalizer (R0 : Set J) := by
  rw [Bp, Subgroup.closure_le]
  rintro y (rfl | rfl | hy)
  · exact ha_norm
  · exact hb_norm
  · exact Subgroup.le_normalizer hy

theorem B0_le_Bp : B0 ≤ Bp := by
  rw [B0, Subgroup.closure_le]
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  have hj' := List.mem_range.1 hj
  obtain ⟨-, he⟩ := gwOK_spec gw_ok j hj'
  have hp := PR_posFold (PR_b0El (i := 4) (by norm_num)) (PR_b0El (i := 15) (by norm_num))
    (GW.getD j ([], 0)).1 1 one PR_one
  have e := PR_eq' (PR_b0El hj') (PR_mul hp (PR_wfrom 15 0 _ (by norm_num))) he
  rw [SetLike.mem_coe, e]
  refine Subgroup.mul_mem _ (posFold_mem (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) _ _
    (Subgroup.one_mem _)) ?_
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (wfrom_mem_R0 _)))

theorem cover_step {g : J} {G : ℕ} (hg : PR g G) (hgN : g ∈ Subgroup.normalizer (R0 : Set J))
    {CV : List (ℕ × ℕ)} (hCV : coverOK c rm one XS TS G CV = true) {i : ℕ} (hi : i < 60) {r : J}
    (hr : r ∈ R0) : ∃ i' < 60, ∃ r' ∈ R0, tEl i * r * g = tEl i' * r' := by
  obtain ⟨hlt, he⟩ := coverOK_spec hCV i hi
  have e := PR_eq' (PR_mul (PR_tEl hi) hg) (PR_mul (PR_tEl hlt) (PR_wfrom 15 0 _ (by norm_num))) he
  have hr' : g⁻¹ * r * g ∈ R0 := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgN) r).1 hr
    rwa [inv_inv] at this
  refine ⟨_, hlt, wfrom xE (CV.getD i (0, 0)).2 0 15 * (g⁻¹ * r * g),
    Subgroup.mul_mem _ (wfrom_mem_R0 _) hr', ?_⟩
  calc tEl i * r * g = tEl i * g * (g⁻¹ * r * g) := by group
    _ = _ := by rw [e, mul_assoc]

theorem Bp_cover : ∀ y ∈ Bp, ∃ i < 60, ∃ r ∈ R0, y = tEl i * r := by
  refine closure_sub_of_mul ⟨0, by norm_num, 1, Subgroup.one_mem _, by rw [tEl_zero', mul_one]⟩ ?_
  rintro _ ⟨i, hi, r, hr, rfl⟩ g hg
  rcases hg with rfl | rfl | hg
  · obtain ⟨i', hi', r', hr', e⟩ := cover_step (PR_b0El (by norm_num)) ha_norm ca_ok hi hr
    exact ⟨i', hi', r', hr', e⟩
  · obtain ⟨i', hi', r', hr', e⟩ := cover_step (PR_b0El (by norm_num)) hb_norm cb_ok hi hr
    exact ⟨i', hi', r', hr', e⟩
  · exact ⟨i, hi, r * g, Subgroup.mul_mem _ hr hg, by rw [mul_assoc]⟩

theorem r0Facts : R0Facts where
  card_R0 := card_R0
  normal b hb r hr :=
    (Subgroup.mem_normalizer_iff.1 (Bp_le_normalizer (B0_le_Bp hb)) r).1 hr
  cover x hx := Bp_cover x (B0_le_Bp hx)
  center := center

end CertificateChecks.KernelJ4R0
