module

public import CFSG.Certificates.Kernel.U62PairSound
public import CFSG.Certificates.Kernel.U62PairMat
public import Certificates.Kernel.U62Pair.Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses
import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Kernel.UnitarySix.LettersBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU62P

open CFSG.KC.U62P CFSG.ComponentClassification.RankTwoHypIICover.U62
open CFSG.Sporadic.Schreier (evalCodes tab_eq)

theorem u62Let_eq :
    u62Let = CFSG.EvenSmallLie.UnitarySix.u62Letters := by
  unfold u62Let CFSG.EvenSmallLie.UnitarySix.u62Letters
  refine List.map_congr_left fun (k : Fin 46) _ => ?_
  exact (CFSG.EvenSmallLie.UnitarySix.letter_eq k.val k.isLt).symm

theorem sbWords_eq :
    u62SbWords = CFSG.EvenSmallLie.UnitarySix.aWords ++ CFSG.EvenSmallLie.UnitarySix.tWords := rfl

theorem rWords_eq : u62RWords = CFSG.EvenSmallLie.UnitarySix.sRepWords := rfl

theorem sbG_eq :
    u62SbG = CFSG.EvenSmallLie.UnitarySix.sGens := by
  rw [u62SbG, CFSG.EvenSmallLie.UnitarySix.sGens, CFSG.EvenSmallLie.UnitarySix.aGens,
    CFSG.EvenSmallLie.UnitarySix.tGens, ← List.map_append, ← sbWords_eq, u62Let_eq]
  refine List.map_congr_left fun w _ => ?_
  rw [CFSG.EvenSmallLie.UnitarySix.u62W, tab_eq]

theorem sb_eq :
    u62Sb = CFSG.EvenSmallLie.UnitarySix.uS := by
  rw [CFSG.EvenSmallLie.UnitarySix.uS_closure, ← sbG_eq]
  rfl

theorem card_sb :
    Nat.card u62Sb = 32768 := by
  rw [sb_eq]
  exact CFSG.EvenSmallLie.UnitarySix.card_uS

theorem mem_sReps
    {r : Equiv.Perm (Fin 693)} (hr : r ∈ CFSG.EvenSmallLie.UnitarySix.sReps) :
    ∃ j < 43, r = u62R j := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
  have hj' : j < 43 := hj
  refine ⟨j, hj', ?_⟩
  rw [u62R, sbG_eq, rWords_eq, List.getD_eq_getElem _ _ hj]

theorem classes_sb :
    ∀ u ∈ u62Sb, orderOf u = 2 → ∃ j < 43, ∃ c ∈ u62Sb, u = c * u62R j * c⁻¹ := by
  intro u hu ho
  rw [sb_eq] at hu ⊢
  obtain ⟨r, hr, c, hc, e⟩ := CFSG.EvenSmallLie.UnitarySix.sylow_facts.1 u hu ho
  obtain ⟨j, hj, rfl⟩ := mem_sReps hr
  exact ⟨j, hj, c, hc, e⟩

section PoolDet

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.F4M.Aux CFSG.KC.U62P.Snd Matrix

theorem bAndU62 {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := CFSG.KS.bAnd_iff a b

theorem ent_zero_of_land {U M : ℕ} (h : Nat.land U M = 0) (i j : ℕ)
    (h0 : M.testBit (2 * (6 * i + j)) = true) (h1 : M.testBit (2 * (6 * i + j) + 1) = true) :
    CFSG.KC.F4M.ent U i j = 0 := by
  have hb : ∀ n, M.testBit n = true → U.testBit n = false := by
    intro n hn
    have := congrArg (fun x => x.testBit n) h
    simp only [Nat.zero_testBit] at this
    change (U &&& M).testBit n = false at this
    rw [Nat.testBit_and, hn, Bool.and_true] at this
    exact this
  apply eq_of_bits (ent_lt U i j) (by decide)
  · change (fget U (6 * i + j) 2).testBit 0 = _
    rw [testBit_fget2_zero, hb _ h0]
    rfl
  · change (fget U (6 * i + j) 2).testBit 1 = _
    rw [testBit_fget2_one, hb _ h1]
    rfl

theorem cF4_dgN (L U : ℕ) : ∀ n, cF4 (dgN L U n) =
    (∏ i ∈ Finset.range n, cF4 (CFSG.KC.F4M.ent L i i) * cF4 (CFSG.KC.F4M.ent U i i)) ∧
      dgN L U n < 4
  | 0 => ⟨by rw [Finset.prod_range_zero]; rfl, by change 1 < 4; decide⟩
  | n + 1 => by
    obtain ⟨e, lt⟩ := cF4_dgN L U n
    change cF4 (fm (fm (CFSG.KC.F4M.ent L n n) (CFSG.KC.F4M.ent U n n)) (dgN L U n)) = _ ∧
      fm (fm (CFSG.KC.F4M.ent L n n) (CFSG.KC.F4M.ent U n n)) (dgN L U n) < 4
    refine ⟨?_, fm_lt _ _⟩
    rw [fm_spec (fm_lt _ _) lt, fm_spec (ent_lt _ _ _) (ent_lt _ _ _), e, Finset.prod_range_succ]
    ring

theorem det_lt4 (P : ℕ) : CFSG.KC.F4M.det P < 4 := by
  unfold CFSG.KC.F4M.det
  rw [strictN_eq]
  exact fget2_lt _ _

theorem det_of_detLU {P R L U : ℕ} (h : detLU P R L U = true) (hR : CFSG.KC.F4M.det R = 1) :
    CFSG.KC.F4M.det P = 1 := by
  unfold detLU at h
  obtain ⟨hL, h⟩ := bAndU62.1 h
  obtain ⟨hU, h⟩ := bAndU62.1 h
  obtain ⟨hm, hd⟩ := bAndU62.1 h
  have hL' := Nat.eq_of_beq_eq_true hL
  have hU' := Nat.eq_of_beq_eq_true hU
  have hm' := Nat.eq_of_beq_eq_true hm
  have hd' := Nat.eq_of_beq_eq_true hd
  have hLt : (decM L).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    rw [← cF4_ent]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | (rw [ent_zero_of_land hL' _ _ (by decide) (by decide)]; rfl)
  have hUt : (decM U).BlockTriangular id := by
    intro i j hij
    change j < i at hij
    rw [← cF4_ent]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | (rw [ent_zero_of_land hU' _ _ (by decide) (by decide)]; rfl)
  have e := congrArg (fun M => (decM M).det) hm'
  simp only [decM_mulK, Matrix.det_mul] at e
  rw [det_sound R, hR, Matrix.det_of_isLowerTriangular _ hLt, Matrix.det_of_isUpperTriangular hUt,
    det_sound P, ← Finset.prod_mul_distrib] at e
  have hp : ∏ i : Fin 6, decM L i i * decM U i i =
      ∏ i ∈ Finset.range 6, cF4 (CFSG.KC.F4M.ent L i i) * cF4 (CFSG.KC.F4M.ent U i i) := by
    rw [Finset.prod_range (fun i =>
      cF4 (CFSG.KC.F4M.ent L i i) * cF4 (CFSG.KC.F4M.ent U i i))]
    simp only [cF4_ent]
  have h1 : cF4 (dgN L U 6) = 1 := by rw [hd']; rfl
  rw [(cF4_dgN L U 6).1, ← hp] at h1
  rw [h1, cF4_one, mul_one] at e
  exact cF4_inj (det_lt4 P) (by decide) (e.trans cF4_one.symm)

theorem poolAt_of_poolL {PV LW UW RI RT NR p : ℕ}
    (hR : ∀ r < NR, CFSG.KC.F4M.det (f72 RT r) = 1)
    (h : poolL PV LW UW RI RT NR p = true) : poolAt PV p = true := by
  unfold poolL at h
  rw [strictB_eq, strictB_eq] at h
  obtain ⟨h1, h⟩ := bAndU62.1 h
  obtain ⟨h2, h3⟩ := bAndU62.1 h
  have hr : f8 RI p < NR := by rwa [Nat.blt_eq] at h2
  have hdet := det_of_detLU h3 (hR _ hr)
  unfold poolAt
  rw [strictB_eq]
  refine bAndU62.2 ⟨h1, ?_⟩
  rw [hdet]
  rfl

end PoolDet

theorem blocks {f : Nat → Bool} {B n : Nat}
    (h : ∀ s < n, CFSG.KC.Enum.allBlk (B * s) f B = true) : ∀ i < B * n, f i = true := by
  intro i hi
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hs : i / B < n := (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact hi)
  have e := CFSG.KS.allBlk_spec (h (i / B) hs) (i % B) (Nat.mod_lt _ hB)
  have e2 : Nat.add (B * (i / B)) (i % B) = i := Nat.div_add_mod i B
  rwa [e2] at e

theorem below {f : Nat → Bool} {b n : Nat} (h : CFSG.KC.Enum.allBlk b f n = true) :
    ∀ i, b ≤ i → i < b + n → f i = true := by
  intro i h1 h2
  have e := CFSG.KS.allBlk_spec h (i - b) (by omega)
  have e2 : Nat.add b (i - b) = i := by change b + (i - b) = i; omega
  rwa [e2] at e

theorem lst_all : ∀ i < 32768, lst i = true := by
  have h : ∀ s < 16, CFSG.KC.Enum.allBlk (2048 * s) lst 2048 = true := by
    intro s hs
    interval_cases s
    exacts [kLst_0, kLst_1, kLst_2, kLst_3, kLst_4, kLst_5, kLst_6, kLst_7, kLst_8, kLst_9,
      kLst_10, kLst_11, kLst_12, kLst_13, kLst_14, kLst_15]
  exact blocks h

theorem ent_all : ∀ q < 512, ent q = true := by
  have h : ∀ s < 16, CFSG.KC.Enum.allBlk (32 * s) ent 32 = true := by
    intro s hs
    interval_cases s
    exacts [kEnt_0, kEnt_1, kEnt_2, kEnt_3, kEnt_4, kEnt_5, kEnt_6, kEnt_7, kEnt_8, kEnt_9,
      kEnt_10, kEnt_11, kEnt_12, kEnt_13, kEnt_14, kEnt_15]
  exact blocks h

theorem pool_all : ∀ p < 1771, pool p = true := by
  have h : ∀ s < 6, CFSG.KC.Enum.allBlk (256 * s) poolCU 256 = true := by
    intro s hs
    interval_cases s
    exacts [kPool_0, kPool_1, kPool_2, kPool_3, kPool_4, kPool_5]
  have hR : ∀ r < 63, CFSG.KC.F4M.det (f72 D.RT r) = 1 := fun r hr =>
    Nat.eq_of_beq_eq_true (below kRTU r (Nat.zero_le _) (by omega))
  intro p hp
  refine poolAt_of_poolL (LW := D.LW) (UW := D.UW) (RI := D.RI) hR ?_
  rcases Nat.lt_or_ge p 1536 with h1 | h1
  · exact blocks h p h1
  · exact below kPool_6 p h1 (by omega)

theorem rec_all : ∀ g < 896, rec g = true := by
  have h : ∀ s < 2, CFSG.KC.Enum.allBlk (448 * s) rec 448 = true := by
    intro s hs
    interval_cases s
    exacts [kRec_0, kRec_1]
  exact blocks h

theorem bAnd_iff' {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := CFSG.KS.bAnd_iff a b

theorem f72_blk (T W n k j : ℕ) (hW : W = 72 * n) (hj : j < n) :
    f72 (Nat.land (Nat.shiftRight T (Nat.mul W k)) (Nat.sub (Nat.shiftLeft 1 W) 1)) j =
      f72 T (n * k + j) := by
  subst hW
  have hm : (4722366482869645213695 : ℕ) = 2 ^ 72 - 1 := by norm_num
  unfold f72
  change (((T >>> (72 * n * k)) &&& ((1 <<< (72 * n)) - 1)) >>> (72 * j)) &&&
      4722366482869645213695 = (T >>> (72 * (n * k + j))) &&& 4722366482869645213695
  rw [hm, Nat.one_shiftLeft]
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < 72
  · have e : 72 * n * k + (72 * j + t) = 72 * (n * k + j) + t := by ring
    have e2 : 72 * j + t < 72 * n := by omega
    simp [ht, e, e2]
  · simp [ht]

theorem lvFU_eq : lvFU = f72 D.LV := by
  funext i
  unfold lvFU
  rcases Nat.lt_or_ge i 32768 with hi | hi
  · have hb : Nat.blt i 32768 = true := by rw [Nat.blt_eq]; exact hi
    rw [hb]
    have hs : Nat.shiftRight i 8 = i / 256 := Nat.shiftRight_eq_div_pow i 8
    have hl : Nat.land i 255 = i % 256 := Nat.and_two_pow_sub_one_eq_mod i 8
    have hk : Nat.shiftRight i 8 < 128 := by rw [hs]; omega
    have e : lvBlk (0 + Nat.shiftRight i 8) = true := CFSG.KS.allBlk_spec kLVB _ hk
    rw [Nat.zero_add] at e
    unfold lvBlk at e
    have e2 := Nat.eq_of_beq_eq_true e
    change f72 (D.LVB (Nat.shiftRight i 8)) (Nat.land i 255) = f72 D.LV i
    rw [e2, f72_blk D.LV 18432 256 _ _ (by norm_num) (by rw [hl]; omega), hs, hl]
    congr 1
    omega
  · have hb : Nat.blt i 32768 = false := by
      cases h : Nat.blt i 32768
      · rfl
      · rw [Nat.blt_eq] at h
        omega
    rw [hb]
    have hlt : D.LV < 2 ^ (72 * i) := by
      have h1 : D.LV < 1 <<< 2359296 := by
        have h2 := kLVlt
        rwa [Nat.blt_eq] at h2
      have hmono : ∀ e, e ≤ 72 * i → 1 <<< e ≤ 2 ^ (72 * i) := fun e he => by
        rw [Nat.one_shiftLeft]
        exact Nat.pow_le_pow_right (by norm_num) he
      exact lt_of_lt_of_le h1 (hmono _ (by omega))
    have h0 : Nat.shiftRight D.LV (Nat.mul 72 i) = 0 := by
      change D.LV >>> (72 * i) = 0
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hlt
    change 0 = Nat.land (Nat.shiftRight D.LV (Nat.mul 72 i)) 4722366482869645213695
    rw [h0]
    rfl

theorem lst_parts {i : Nat} (hi : i < 32768) :
    treeAt D.GV D.LV D.PT D.LB i = true ∧ sortAt D.LV D.SO 32768 i = true ∧
      scanAt D.LV D.PO D.EI D.NO i = true := by
  have h := lst_all i hi
  unfold lst at h
  rw [lvFU_eq] at h
  obtain ⟨h1, h⟩ := bAnd_iff'.1 h
  obtain ⟨h2, h3⟩ := bAnd_iff'.1 h
  exact ⟨h1, h2, h3⟩

theorem tv_D : D.TV = CertificateChecks.KernelU6.U.TV := rfl

theorem up_D : D.UP = CertificateChecks.KernelU6.U.UP := rfl

theorem facts :
    U62Facts := by
  have hNO : D.NO = 512 := Nat.eq_of_beq_eq_true kNO
  have hNG : D.NG = 896 := Nat.eq_of_beq_eq_true kNG
  have hNP : D.NP = 1771 := Nat.eq_of_beq_eq_true kNP
  have hK := kFacts_of_K (TV := D.TV) (UP := D.UP) (GV := D.GV) (RV := D.RV) (LV := D.LV)
    (PT := D.PT) (LB := D.LB) (SO := D.SO) (NI := D.NI) (XP := D.XP) (NXP := D.NXP) (PO := D.PO)
    (NO := D.NO) (NP := D.NP) (T := ET0)
    (by rw [tv_D]; exact CertificateChecks.KernelU6.tv_eq)
    (by rw [up_D]; exact CertificateChecks.KernelU6.up_eq) card_sb
    (fun k hk => below kGen k (Nat.zero_le _) (by omega))
    (fun j hj => below kRep j (Nat.zero_le _) (by omega))
    (fun i hi => (lst_parts hi).1) (fun i hi => (lst_parts hi).2.1)
    (fun q hq => below kPhi q (Nat.zero_le _) (Nat.lt_of_lt_of_eq hq hNO))
    (fun k hk => below kNorm k (Nat.zero_le _) (by omega))
    (fun q hq => below kFix q (Nat.zero_le _) (by omega)) (fun i hi => (lst_parts hi).2.2) rfl rfl
    (fun p hp => pool_all p (hNP ▸ hp)) (fun g hg => rec_all g (hNG ▸ hg))
    (fun q hq => ent_all q (hNO ▸ hq))
  obtain ⟨h1, h3, h4, h6⟩ := hK
  exact ⟨h1, card_sb, h3, h4, classes_sb, h6⟩

end CertificateChecks.KernelU62P

end
