module

public import Certificates.Kernel.Sporadic.HeK.Checks
public import Certificates.Kernel.Sporadic.HeK.ChecksW
public import Certificates.Kernel.Sporadic.HeK.ChecksR
public import Certificates.Kernel.Sporadic.HeK.ChecksT
public import Certificates.Kernel.He27143.Final
public import CFSG.Certificates.Kernel.Spor.SlpCard
public import CFSG.Certificates.Kernel.Spor.HeVOrbOK
public import CFSG.Certificates.Kernel.Spor.He3168Sound
public import CFSG.Certificates.Kernel.Orders.He.RelsBind
public import Certificates.Certificate9118
import CFSG.Certificates.Kernel.Spor.F3R
import CFSG.Certificates.Kernel.Spor.VOrbSound
import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.TabWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.HeK.wordsAll CertificateChecks.KernelSpor.HeK.wordsSl 72
#kon_join CertificateChecks.KernelSpor.HeK.relAll CertificateChecks.KernelSpor.HeK.relSl 35
#kon_join CertificateChecks.KernelSpor.HeK.treesAll CertificateChecks.KernelSpor.HeK.treesSl 45

namespace CertificateChecks.KernelSpor.HeK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.SC
  CFSG.KC.Ord CFSG.KC.HeOrb CFSG.KS.HeVO CFSG.KS.SporSch.LyM CFSG.KD.HeOrb
open CFSG.Sporadic.He.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sl_spec {lo len n : Nat} {p : Nat → Bool}
    (h : allN len (fun d => strictB (Nat.add lo d) fun i => bIf(Nat.blt i n, p i, true)) = true) :
    ∀ i, lo ≤ i → i < lo + len → i < n → p i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem allN_eq_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KD.HeTab.allN_iff

theorem consts : constsOK 7 12 600 50 8 cL cH cCM cRM cONE cLV cHV = true := mat_parts.1

theorem mat_facts : validM 7 (50 * 600) cL cH MAK = true ∧ validM 7 (50 * 600) cL cH MBK = true ∧
    validM 7 (50 * 600) cL cH QK = true ∧ validM 7 (50 * 600) cL cH YK = true ∧
    Nat.beq (mulR 7 12 600 50 8 cL cH cCM cRM MAK MAK) cONE = true ∧
    Nat.beq (powR 7 12 600 50 8 cL cH cCM cRM cONE MBK 7) cONE = true ∧
    Nat.beq (mulR 7 12 600 50 8 cL cH cCM cRM QK YK) cONE = true ∧
    ∀ t < 50, CFSG.KC.He3168.colK QK t (PH t) = true := by
  have h : matOK = true := matOK_ok
  unfold matOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, allN_spec h8⟩

theorem matrix_ok : matrixChecks () = true := by
  obtain ⟨vA, vB, -, -, hAA, hB7, -⟩ := mat_facts
  unfold matrixChecks
  rw [CFSG.KD.HeOrb.matA_eq, CFSG.KD.HeOrb.matB_eq]
  change (mulM 7 50 (unpackL 50 12 600 MAK) (unpackL 50 12 600 MAK) == idM 50 &&
    powM 7 50 (unpackL 50 12 600 MBK) 7 == idM 50) = true
  rw [(mulR_eq consts vA vA).1, (powM_eq consts vB 7).1, (idM_eq consts).1,
    beq_eq consts (mulR_eq consts vA vA).2 (idM_eq consts).2,
    beq_eq consts (powM_eq consts vB 7).2 (idM_eq consts).2, hAA, hB7]
  rfl

theorem canon_T {i : Nat} (hi : i < 8330) : canonV 7 50 (T i) = true := by
  have hv := (blkK_spec (blk (s := i / 32) (by omega))).1
  have hC := CFSG.KS.Ord.validM_canon consts (vld_eq hv)
  have hr : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  unfold canonV
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simp [T, keyOf], fun j hj => ?_⟩
  have hj' : j < 50 := by simpa [T, keyOf] using hj
  simp only [T, keyOf, Array.getElem_ofFn, decide_eq_true_eq]
  rw [code_eq, div_mod_mod (by omega : 12 * j + 12 ≤ 600), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have e : 600 * (i % 32) + 12 * j = 12 * (50 * (i % 32) + j) := by ring
  have h := hC.2 (50 * (i % 32) + j) (by omega)
  unfold CFSG.KS.Ord.lane at h
  rw [e]
  exact h

theorem orb_ok (chunks : Nat) :
    vecOrbitOK 7 50 (matA ()) (matB ()) (rootVec ()) OJ chunks = true := by
  rw [← T_zero]
  exact vecOrbitOK_of (N := 8330) (T := T) (by norm_num) (by norm_num) T_inj (fun i hi => canon_T hi)
    (fun i hi => pt_facts hi) (Nat.eq_of_beq_eq_true hd_parts.2.2.1) chunks

theorem invA_spec {x : Nat} (hx : x < 8330) : r32 AL (r32 AL x) = x :=
  Nat.eq_of_beq_eq_true (allN_spec invA_ok x hx)

theorem al_lt {x : Nat} (hx : x < 8330) : r32 AL x < 8330 := (pt_facts hx).1

theorem be_lt {x : Nat} (hx : x < 8330) : r32 BE x < 8330 := (pt_facts hx).2.1

theorem keys_get {q : Nat} (hq : q < 8330) : OJ.keys[q]! = T q :=
  TBfs.ofFn_get (f := fun i => T i) hq

theorem slpGK_eq : slpGK = slpG GJ LJ := by
  funext z v
  rcases z with k | k
  · have e : slpGK (Int.ofNat k) v =
        Bool.rec (LJ (2 * (k - 3)) v) (GJ (Int.ofNat k) v) (Nat.ble k 2) := rfl
    have ha : (Int.ofNat k).natAbs = k := rfl
    rw [e]
    unfold slpG
    rw [ha]
    cases hb : Nat.ble k 2
    · have hk : ¬ k ≤ 2 := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
      have hp : (0 : Int) < Int.ofNat k := by rw [Int.ofNat_eq_natCast]; omega
      simp only [hk, hp, ↓reduceIte]
    · simp [Nat.le_of_ble_eq_true hb]
  · have e : slpGK (Int.negSucc k) v = Bool.rec (LJ (2 * (k + 1 - 3) + 1) v)
        (GJ (Int.negSucc k) v) (Nat.ble (k + 1) 2) := rfl
    have ha : (Int.negSucc k).natAbs = k + 1 := rfl
    rw [e]
    unfold slpG
    rw [ha]
    cases hb : Nat.ble (k + 1) 2
    · have hk : ¬ k + 1 ≤ 2 := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
      have hp : ¬ (0 : Int) < Int.negSucc k := by
        have := Int.negSucc_lt_zero k
        omega
      simp only [hk, hp, ↓reduceIte]
    · simp [Nat.le_of_ble_eq_true hb]

theorem gens_get (z : Int) {x : Nat} (hx : x < 8330) :
    ap (genTables OJ z) x = GJ z x ∧ GJ z x < 8330 :=
  CFSG.KD.HeTab.gens_get z hx

theorem inv_spec {j x : Nat} (hj : j < 8) (hx : x < 8330) : LJ (2 * j) x < 8330 ∧
    LJ (2 * j + 1) x < 8330 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 8330 16 = true := invL_ok
  unfold invK at h0
  have hj' : j < Nat.div 16 2 := by change j < 16 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem word_spec {j x : Nat} (hj : j < 8) (hx : x < 8330) :
    LJ (2 * j) x = List.foldr (slpG GJ LJ) x (chainWords ())[j]! := by
  rw [← slpGK_eq]
  have hs : 9 * j + x / 1000 < 72 := by omega
  have h := wordsAll (9 * j + x / 1000) hs
  unfold wordsSl at h
  rw [strictB_eq, strictB_eq] at h
  have e1 : Nat.div (9 * j + x / 1000) 9 = j := by
    change (9 * j + x / 1000) / 9 = j
    omega
  have e2 : Nat.mul (Nat.mod (9 * j + x / 1000) 9) 1000 = x / 1000 * 1000 := by
    change (9 * j + x / 1000) % 9 * 1000 = x / 1000 * 1000
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  have h1 : x / 1000 * 1000 ≤ x := by omega
  have h2 : x < x / 1000 * 1000 + 1000 := by omega
  exact Nat.eq_of_beq_eq_true (sl_spec h x h1 h2 hx)

theorem words_ok : ∀ j < (chainWords ()).size, ∀ z ∈ (chainWords ())[j]!,
    z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
  decide

theorem wsize : (chainWords ()).size = 8 := rfl

noncomputable abbrev LT16 : Array Table := chainLetters OJ

theorem letters_get : LT16.size = 16 ∧ ∀ l < 16, ∀ x < 8330, ap LT16[l]! x = LJ l x := by
  have h := slpLetters_get (n := 8330) (gens := genTables OJ) (G := GJ) (L := LJ)
    (by norm_num) (fun z x hx => gens_get z hx) words_ok
    (fun j hj x hx => word_spec (by rw [wsize] at hj; exact hj) hx)
    (fun j hj x hx => inv_spec (by rw [wsize] at hj; exact hj) hx)
  rw [wsize] at h
  exact h

theorem lt_range {l x : Nat} (hl : l < 16) (hx : x < 8330) : LJ l x < 8330 := by
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · exact (inv_spec (by omega) hx).1
  · exact (inv_spec (by omega) hx).2.1

theorem tree_spec {i : Nat} (hi : i < 5) :
    tbfsHdK 8330 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 8330 (CNTJ i) (lvK LJ BJ 16 i).length LJ (lvAt LJ BJ 16 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  have hs0 : 9 * i < 45 := by omega
  have h0 := treesAll (9 * i) hs0
  unfold treesSl treeSl at h0
  have e1 : Nat.div (9 * i) 9 = i := by change 9 * i / 9 = i; omega
  rw [e1, bAnd_iff] at h0
  refine ⟨h0.1, fun k hk => ?_⟩
  have hc : CNTJ i ≤ 8330 := by interval_cases i <;> decide
  have hs : 9 * i + k / 1000 < 45 := by omega
  have h := treesAll (9 * i + k / 1000) hs
  unfold treesSl treeSl at h
  have e2 : Nat.div (9 * i + k / 1000) 9 = i := by change (9 * i + k / 1000) / 9 = i; omega
  have e3 : Nat.mod (9 * i + k / 1000) 9 = k / 1000 := by
    change (9 * i + k / 1000) % 9 = k / 1000
    omega
  rw [e2, e3, bAnd_iff] at h
  have h2 := h.2
  unfold tbfsSlK at h2
  exact sl_spec (n := CNTJ i) h2 k (by simp only [Nat.mul_eq]; omega)
    (by simp only [Nat.mul_eq]; omega) hk

theorem q_eq : (chainQ ()).toList = List.range 50 := by simp [chainQ]

theorem chain_hyp : ChainHyp 8330 16 5 LT16 chainBase (chainQ ()) (chainQb ()) LJ BJ
    (List.range 50) (fun i => List.getD [0, 1, 3, 4, 2] i 0) CNTJ PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_get.1, letters_get.2⟩
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨q_eq, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, by decide⟩⟩
  tree := fun i hi => tree_spec hi

theorem rels_spec : ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters, ∀ x < 8330,
    List.foldr (letV (r32 AL) (r32 AL) (r32 BE) (r32 CFSG.KD.HeTab.BI)) x v = x := by
  intro v hv x hx
  rw [CFSG.KD.OrdHe.rels_eq] at hv
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hv
  have hl : CFSG.KD.OrdHe.rels.length = 7 := rfl
  have hs : 5 * r + x / 1700 < 35 := by omega
  have h := relAll (5 * r + x / 1700) hs
  unfold relSl at h
  rw [strictB_eq, strictB_eq] at h
  have e1 : Nat.div (5 * r + x / 1700) 5 = r := by
    change (5 * r + x / 1700) / 5 = r
    omega
  have e2 : Nat.mul (Nat.mod (5 * r + x / 1700) 5) 1700 = x / 1700 * 1700 := by
    change (5 * r + x / 1700) % 5 * 1700 = x / 1700 * 1700
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  have h1 : x / 1700 * 1700 ≤ x := by omega
  have h2 : x < x / 1700 * 1700 + 1700 := by omega
  have h' := Nat.eq_of_beq_eq_true (sl_spec h x h1 h2 hx)
  rw [List.getD_eq_getElem _ _ hr] at h'
  have e : letK = letV (r32 AL) (r32 AL) (r32 BE) (r32 CFSG.KD.HeTab.BI) := by
    funext l v
    obtain ⟨i, b⟩ := l
    unfold letK letV
    rcases i with _ | i <;> cases b <;> rfl
  rw [e] at h'
  exact h'

theorem permAL : PermF 8330 (r32 AL) := by
  unfold PermF
  exact ⟨fun x hx => al_lt hx, fun x hx y hy e => by
    rw [← invA_spec hx, ← invA_spec hy, e]⟩

theorem permBE : PermF 8330 (r32 BE) := by
  unfold PermF
  exact ⟨fun x hx => be_lt hx, fun x hx y hy e => by
    rw [← (CFSG.KD.HeTab.inv_facts hx).2, ← (CFSG.KD.HeTab.inv_facts hy).2, e]⟩

theorem card_le : Nat.card (Subgroup.closure (Set.range fun l : Fin 16 => permOfT 8330 LT16[l.val]!)) ≤
    ((List.range 5).map CNTJ).prod := by
  have hf : Finite TauCeti.Sporadic.hePresentation.Group :=
    Certificates.certificate9118.1
  have hcard : Nat.card TauCeti.Sporadic.hePresentation.Group ≤ 4030387200 :=
    Certificates.certificate9118.2
  have hP : TauCeti.Sporadic.hePresentation.generatorCount = 2 := by
    simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.hePresentation_generatorNames]
  set K := Subgroup.closure ({permF 8330 (r32 AL), permF 8330 (r32 BE)} :
    Set (Equiv.Perm (Fin 8330)))
  have iB := permF_inv permBE (fun x hx => (CFSG.KD.HeTab.inv_facts hx).1)
    fun x hx => (CFSG.KD.HeTab.inv_facts hx).2
  have hA : permF 8330 (r32 AL) ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : permF 8330 (r32 BE) ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hG : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → PermF 8330 (GJ z) ∧ permF 8330 (GJ z) ∈ K := by
    intro z hz ha
    rcases (by omega : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) with rfl | rfl | rfl | rfl
    · have e : GJ 1 = r32 AL := by funext x; rfl
      rw [e]
      exact ⟨permAL, hA⟩
    · have e : GJ (-1) = r32 AL := by funext x; rfl
      rw [e]
      exact ⟨permAL, hA⟩
    · have e : GJ 2 = r32 BE := by funext x; rfl
      rw [e]
      exact ⟨permBE, hB⟩
    · have e : GJ (-2) = r32 CFSG.KD.HeTab.BI := by funext x; rfl
      rw [e]
      refine ⟨iB.1, ?_⟩
      rw [iB.2]
      exact K.inv_mem hB
  have hmem := slp_mem (K := K) (G := GJ) (L := LJ) (words := chainWords ()) hG words_ok
    (fun j hj x hx => word_spec (by rw [wsize] at hj; exact hj) hx)
    (fun j hj x hx => have hj' : j < 8 := by rw [wsize] at hj; exact hj
      ⟨(inv_spec hj' hx).2.1, (inv_spec hj' hx).2.2⟩)
  rw [wsize] at hmem
  refine le_trans (card_letters_le (L := LJ) TauCeti.Sporadic.hePresentation hP permAL permBE
    (fun x hx => ⟨al_lt hx, invA_spec hx⟩)
    (fun x hx => CFSG.KD.HeTab.inv_facts hx) rels_spec letters_get.2 hmem) ?_
  refine le_trans hcard ?_
  decide

theorem chain_eq : chainTrees 8330 LT16 chainBase =
      Array.ofFn (n := 5) (fun i => tbfsRec 8330 (CNTJ i.val) (PTSJ i.val) (POSJ i.val)
        (PARJ i.val) (LABJ i.val)) ∧
    ∀ chunks, chainOK 8330 LT16 chainBase (chainQ ()) (chainQb ())
      (chainTrees 8330 LT16 chainBase) chunks = true :=
  pchain_of_card chain_hyp card_le

theorem sizes : (orbitSizes (chainTrees 8330 LT16 chainBase) == [8330, 4480, 27, 2, 2]) = true := by
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  rfl

theorem lv1_eq : levelLetters LT16 chainBase 1 = (lvK LJ BJ 16 1).toArray := by
  rw [← Array.toList_inj]
  simp only [levelLetters, Array.toList_filter, Array.toList_range, letters_get.1, lvK]
  apply List.filter_congr
  intro l hl
  have hl' : l < 16 := List.mem_range.1 hl
  have e : chainBase[0]! = 0 := rfl
  rw [e, letters_get.2 l hl' 0 (by norm_num), Bool.eq_iff_iff, allN_eq_iff]
  simp [BJ]

theorem lab_facts : (∀ z < 8330, r32 LBL z < 7 ∧ r32 (SPOSJ (r32 LBL z)) z < SCNTJ (r32 LBL z) ∧
    r32 (SPTSJ (r32 LBL z)) (r32 (SPOSJ (r32 LBL z)) z) = z) ∧
    ∀ l < 7, ∀ q < SCNTJ l, r32 LBL (r32 (SPTSJ l) q) = l := by
  have h : labOK = true := labOK_ok
  unfold labOK at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun z hz => ?_, fun l hl q hq => ?_⟩
  · have h1 := allN_spec h.1 z hz
    rw [strictB_eq] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    exact ⟨h1.1.1, h1.1.2, h1.2⟩
  · have h2 := allN_spec (allN_spec h.2 l hl) q hq
    simpa using h2

theorem sub_ok : subChecks LT16 (levelLetters LT16 chainBase 1)
      (subTrees LT16 (levelLetters LT16 chainBase 1))
      (labelsOf (subTrees LT16 (levelLetters LT16 chainBase 1))) = true ∧
    ∀ z < 8330, (labelsOf (subTrees LT16 (levelLetters LT16 chainBase 1)))[z]! = r32 LBL z :=
  CFSG.KS.HeSub.heSub_sound (L := LJ) (B := BJ) (SCNT := SCNTJ) (SPTS := SPTSJ) (SPOS := SPOSJ)
    (SPAR := SPARJ) (SLAB := SLABJ) (STI := STIJ) ⟨letters_get.1, fun l hl x hx =>
      ⟨letters_get.2 l hl x hx, lt_range hl hx⟩⟩ lv1_eq
    (fun l hl => by
      have h := allN_spec subTree_ok l hl
      unfold subTree at h
      rw [bAnd_iff] at h
      exact ⟨h.1, allN_spec h.2⟩) rfl lab_facts.1 lab_facts.2

theorem allIn_iff' {n : Nat} {p : Nat → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true :=
  CFSG.KS.TW.allIn_iff

theorem isIdT_iff {T : Table} {f : Nat → Nat} (hT : ∀ x < 8330, ap T x = f x) :
    isIdT T = allN 8330 (fun x => f x == x) := by
  rw [Bool.eq_iff_iff, isIdT, allIn_iff', allN_eq_iff]
  constructor
  · intro h x hx
    have := h x hx
    rw [hT x hx] at this
    exact this
  · intro h x hx
    rw [hT x hx]
    exact h x hx

theorem itv_eq (f : Nat → Nat) : ∀ e x, itv f e x = f^[e] x
  | 0, x => rfl
  | e + 1, x => by
    have h : itv f (e + 1) x = itv f e (f x) := by
      change CFSG.KC.Enum.strictN (f x) (itv f e) = _
      cases f x <;> rfl
    rw [h, itv_eq f e (f x), Function.iterate_succ_apply]

theorem powT_ap {P : Table} {f : Nat → Nat} (hf : ∀ x < 8330, ap P x = f x ∧ f x < 8330) :
    ∀ (e x : Nat), x < 8330 → ap (powT 8330 e P) x = f^[e] x ∧ f^[e] x < 8330 := by
  intro e
  induction e with
  | zero =>
    intro x hx
    exact ⟨CFSG.KD.HeTab.idT_ap hx, hx⟩
  | succ e ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih x hx
    have e1 : powT 8330 (e + 1) P = compT 8330 P (powT 8330 e P) := rfl
    rw [e1, Function.iterate_succ_apply']
    have hc : ap (compT 8330 P (powT 8330 e P)) x = ap P (ap (powT 8330 e P) x) := by
      unfold ap compT
      rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    rw [hc, h1]
    exact hf _ h2

theorem foldr_lt (w : List Int) {x : Nat} (hx : x < 8330) : List.foldr GJ x w < 8330 := by
  induction w with
  | nil => exact hx
  | cons z w ih => exact (gens_get z ih).2

theorem misc_facts : r32 LBL (WJ 0) = 5 ∧ r32 LBL 21 = 3 ∧ r32 LBL (WJ 21) = 1 ∧
    r32 LBL 24 = 4 ∧ r32 LBL (WJ 24) = 3 ∧
    allN 8330 (fun x => r32 AL x == x) = false ∧
    allN 8330 (fun x => itv (r32 BE) 7 x == x) = true ∧
    allN 8330 (fun x => r32 BE x == x) = false ∧
    allN 8330 (fun x => itv (fun y => r32 AL (r32 BE y)) 17 x == x) = true ∧
    allN 8330 (fun x => r32 AL (r32 BE x) == x) = false := by
  have h : miscOK = true := miscOK_ok
  unfold miscOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem basis_ok : basisCheck OJ = true := by
  obtain ⟨-, -, vQ, vY, -, -, hQY, hcol⟩ := mat_facts
  unfold basisCheck
  have hM : colsMat 50 OJ.keys = unpackL 50 12 600 QK :=
    CFSG.KS.HeSub.colsMat_eq (c := PH) (fun t ht => keys_get (by omega)) hcol
  rw [hM]
  dsimp only
  rw [invM_eq (by norm_num) consts vQ vY hQY, (mulR_eq consts vQ vY).1, (idM_eq consts).1,
    beq_eq consts (mulR_eq consts vQ vY).2 (idM_eq consts).2, hQY]

theorem he_cert : heCertificate 3 = true := by
  unfold heCertificate
  simp only [Bool.and_eq_true]
  rw [orbitData_eq]
  refine ⟨matrix_ok, orb_ok 3, ?_⟩
  unfold actionChecks
  simp only [Bool.and_eq_true]
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := misc_facts
  have hlab := sub_ok.2
  have hW : ∀ x < 8330, ap (wordT 8330 (genTables OJ) (witWord ())) x = WJ x :=
    fun x hx => (((CFSG.KS.VO.wordT_ap (n := 8330) (by norm_num)
      (fun z y hy => gens_get z hy)) (witWord ())).2 x hx).1
  have hAB : ∀ x < 8330, ap (compT 8330 OJ.alpha OJ.beta) x = r32 AL (r32 BE x) := by
    intro x hx
    rw [CFSG.KD.HeTab.compT_ap hx (by simp [OJ, vRec]) (by rw [beta_ap hx]; exact be_lt hx),
      beta_ap hx, alpha_ap (be_lt hx)]
  have hAB' : ∀ x < 8330, ap (compT 8330 OJ.alpha OJ.beta) x = r32 AL (r32 BE x) ∧
      r32 AL (r32 BE x) < 8330 := fun x hx => ⟨hAB x hx, al_lt (be_lt hx)⟩
  have hBf : ∀ x < 8330, ap OJ.beta x = r32 BE x ∧ r32 BE x < 8330 :=
    fun x hx => ⟨beta_ap hx, be_lt hx⟩
  have hP7 : ∀ x < 8330, ap (powT 8330 7 OJ.beta) x = itv (r32 BE) 7 x := by
    intro x hx
    rw [(powT_ap hBf 7 x hx).1, itv_eq]
  have hP17 : ∀ x < 8330, ap (powT 8330 17 (compT 8330 OJ.alpha OJ.beta)) x =
      itv (fun y => r32 AL (r32 BE y)) 17 x := by
    intro x hx
    rw [(powT_ap hAB' 17 x hx).1, itv_eq]
  have w0 : WJ 0 < 8330 := foldr_lt _ (by norm_num)
  have w21 : WJ 21 < 8330 := foldr_lt _ (by norm_num)
  have w24 : WJ 24 < 8330 := foldr_lt _ (by norm_num)
  have invB1 : invOK 8330 OJ.beta (invT 8330 OJ.beta) = true :=
    (CFSG.KS.VO.invT_get (f := r32 BE) (g := r32 CFSG.KD.HeTab.BI) (by norm_num) fun x hx =>
      ⟨beta_ap hx, be_lt hx, (CFSG.KD.HeTab.inv_facts hx).2⟩).1
  rw [isIdT_iff (fun x hx => alpha_ap hx), isIdT_iff (fun x hx => beta_ap hx), isIdT_iff hP7,
    isIdT_iff hP17, isIdT_iff hAB, hW 0 (by norm_num), hW 21 (by norm_num), hW 24 (by norm_num),
    hlab _ w0, hlab 21 (by norm_num), hlab _ w21, hlab 24 (by norm_num), hlab _ w24,
    m1, m2, m3, m4, m5, m6, m7, m8, m9, m10]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by simp [OJ, vRec], by simp [OJ, vRec]⟩, by simp [OJ, vRec]⟩, ?_⟩,
    invB1⟩, basis_ok⟩, ?_⟩, by decide⟩, by decide⟩, by decide⟩, chain_eq.2 3⟩, sizes⟩, sub_ok.1⟩,
    rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  · unfold CFSG.Sporadic.Th.Native.invoOK
    rw [allIn_iff']
    intro i hi
    rw [alpha_ap hi, alpha_ap (al_lt hi), invA_spec hi]
    simp
  · unfold CFSG.Sporadic.Fi23.Native.slpOK allIn
    rw [CFSG.KS.F3R.all_eq]
    decide +kernel

end CertificateChecks.KernelSpor.HeK

end
