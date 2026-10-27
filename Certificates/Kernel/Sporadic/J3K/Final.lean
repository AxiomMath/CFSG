module

public import Certificates.Kernel.Sporadic.J3K.Checks
public import Certificates.Kernel.Sporadic.J3K.ChecksP
public import Certificates.Kernel.Sporadic.J3K.ChecksS
public import Certificates.Kernel.Sporadic.J3K.ChecksW
public import Certificates.Kernel.Sporadic.J3K.ChecksR
public import CFSG.Certificates.Kernel.Spor.SlpCard
public import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Bounds.J3Alt.RelsTC
public import Certificates.Certificate9119
public import CFSG.Certificates.Kernel.Spor.F3R
import CFSG.Certificates.Kernel.LocalCompSPCode
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Mathlib
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.J3K.ptAll CertificateChecks.KernelSpor.J3K.ptSl 42
#kon_join CertificateChecks.KernelSpor.J3K.wordsAll CertificateChecks.KernelSpor.J3K.wordsSl 40
#kon_join CertificateChecks.KernelSpor.J3K.relAll CertificateChecks.KernelSpor.J3K.relSl 80
#kon_join CertificateChecks.KernelSpor.J3K.tree0All CertificateChecks.KernelSpor.J3K.tree0Sl 10
#kon_join CertificateChecks.KernelSpor.J3K.labAll CertificateChecks.KernelSpor.J3K.labSl 10
#kon_join CertificateChecks.KernelSpor.J3K.subAll CertificateChecks.KernelSpor.J3K.subTree 22

namespace CertificateChecks.KernelSpor.J3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.SC CFSG.KS.J3S
open CFSG.Sporadic.J3.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem ap_ofFn {N : Nat} {f : Nat → Nat} {x : Nat} (hx : x < N) (hf : f x < 2 ^ 32) :
    ap (Array.ofFn (n := N) fun i => UInt32.ofNat (f i.val)) x = f x := by
  unfold ap
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hf

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

theorem pt_spec {i : Nat} (hi : i < 20520) : PJ i < 2 ^ 80 ∧ r32 TA i < 20520 ∧ r32 TB i < 20520 ∧
    vecMulN 80 CAJ (PJ i) = PJ (r32 TA i) ∧ vecMulN 80 CBJ (PJ i) = PJ (r32 TB i) ∧
    (i + 1 < 20520 → PJ i < PJ (i + 1)) := by
  have hs : i / 500 < 42 := by omega
  have h := ptAll (i / 500) hs
  unfold ptSl at h
  have h' := sl_spec (lo := Nat.mul (i / 500) 500) (len := 500) (n := 20520) h i (by
    simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h'
  exact ⟨a1, a2, a3, a4, a5, fun hh => a6.resolve_left (by omega)⟩

theorem inv_facts {x : Nat} (hx : x < 20520) : r32 AI x < 20520 ∧ r32 AI (r32 TA x) = x ∧
    r32 BI x < 20520 ∧ r32 BI (r32 TB x) = x := by
  have h := allN_spec invAB_ok x hx
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem bfs_facts : (r32 BO 0 < 20520 ∧ PJ (r32 BO 0) = 16561281922307987041) ∧
    (∀ i < 20520, r32 BOI i < 20520 ∧ r32 BO (r32 BOI i) = i) ∧
    ∀ k < 20520, 0 < k → r32 BO k < 20520 ∧ r32 BQ k < k ∧
      (r32 BO k = r32 TA (r32 BO (r32 BQ k)) ∨ r32 BO k = r32 TB (r32 BO (r32 BQ k))) := by
  have h : bfs = true := bfs_ok
  unfold bfs at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨h1, h2⟩, fun i hi => ?_, fun k hk hk0 => ?_⟩
  · have := allN_spec h3 i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.1
  · have := allN_spec h3 k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at this
    obtain ⟨-, h4⟩ := this
    rcases h4 with h4 | h4
    · omega
    · exact ⟨h4.1.1, h4.1.2, h4.2⟩

noncomputable abbrev PTS : Array Nat := Array.ofFn (n := 20520) fun i => PJ i.val
noncomputable abbrev TAt : Table := Array.ofFn (n := 20520) fun i => UInt32.ofNat (r32 TA i.val)
noncomputable abbrev TBt : Table := Array.ofFn (n := 20520) fun i => UInt32.ofNat (r32 TB i.val)

theorem orb_eq : orbitSorted 80 CAJ CBJ 16561281922307987041 20520 = PTS ∧
    imageTable 80 (posMap PTS) PTS CAJ = TAt ∧ imageTable 80 (posMap PTS) PTS CBJ = TBt :=
  sorted_sound (by norm_num) (fun i hi => (pt_spec (by omega)).2.2.2.2.2 hi)
    (fun i hi => ⟨(pt_spec hi).1, (pt_spec hi).2.1, (pt_spec hi).2.2.1, (pt_spec hi).2.2.2.1,
      (pt_spec hi).2.2.2.2.1⟩) bfs_facts.1 bfs_facts.2.1 bfs_facts.2.2

theorem ta_get {x : Nat} (hx : x < 20520) : ap TAt x = r32 TA x :=
  ap_ofFn hx (by have := (pt_spec hx).2.1; omega)

theorem tb_get {x : Nat} (hx : x < 20520) : ap TBt x = r32 TB x :=
  ap_ofFn hx (by have := (pt_spec hx).2.2.1; omega)

theorem pts_get {q : Nat} (hq : q < 20520) : PTS[q]! = PJ q := by
  rw [getElem!_pos _ q (by simpa using hq)]
  simp

theorem invA : invOK 20520 TAt (invT 20520 TAt) = true ∧
    ∀ y < 20520, ap (invT 20520 TAt) y = r32 AI y :=
  invT_get (f := r32 TA) (by norm_num) fun x hx =>
    ⟨ta_get hx, (pt_spec hx).2.1, (inv_facts hx).2.1⟩

theorem invB : invOK 20520 TBt (invT 20520 TBt) = true ∧
    ∀ y < 20520, ap (invT 20520 TBt) y = r32 BI y :=
  invT_get (f := r32 TB) (by norm_num) fun x hx =>
    ⟨tb_get hx, (pt_spec hx).2.2.1, (inv_facts hx).2.2.2⟩

theorem orbitOK_ok : CFSG.Sporadic.J3.Native.orbitOK 80 20520 CAJ CBJ PTS TAt TBt = true := by
  unfold CFSG.Sporadic.J3.Native.orbitOK
  simp only [Bool.and_eq_true, CFSG.KS.TW.allIn_iff]
  refine ⟨⟨by simp, fun i hi => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, -⟩ := pt_spec hi
    rw [pts_get hi, ta_get hi, tb_get hi, pts_get a2, pts_get a3]
    simp [a2, a3, a4, a5]
    exact lt_of_lt_of_eq a1 (by norm_num)
  · have hi' : i < 20520 := by omega
    rw [pts_get hi', pts_get (by omega)]
    simp [(pt_spec hi').2.2.2.2.2 (by omega)]

theorem GJ_eq (z : Int) (x : Nat) : GJ z x =
    if z = 1 then r32 TA x else if z = -1 then r32 AI x else if z = 2 then r32 TB x else r32 BI x := by
  rcases z with ((_ | _ | _ | k) | (_ | k)) <;> rfl

theorem gens_get (z : Int) {x : Nat} (hx : x < 20520) :
    ap (genT 20520 TAt TBt z) x = GJ z x ∧ GJ z x < 20520 := by
  have hf := inv_facts hx
  have hp := pt_spec hx
  rw [GJ_eq]
  have e : genT 20520 TAt TBt z = if z = 1 then TAt else if z = -1 then invT 20520 TAt
      else if z = 2 then TBt else invT 20520 TBt := rfl
  rw [e]
  split_ifs
  · exact ⟨ta_get hx, hp.2.1⟩
  · exact ⟨invA.2 x hx, hf.1⟩
  · exact ⟨tb_get hx, hp.2.2.1⟩
  · exact ⟨invB.2 x hx, hf.2.2.1⟩

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

theorem inv_spec {j x : Nat} (hj : j < 4) (hx : x < 20520) : LJ (2 * j) x < 20520 ∧
    LJ (2 * j + 1) x < 20520 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 20520 8 = true := invL_ok
  unfold invK at h0
  have hj' : j < Nat.div 8 2 := by change j < 8 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem word_spec {j x : Nat} (hj : j < 4) (hx : x < 20520) :
    LJ (2 * j) x = List.foldr (slpG GJ LJ) x ((j3Data ()).words)[j]! := by
  rw [← slpGK_eq]
  have hs : 10 * j + x / 2052 < 40 := by omega
  have h := wordsAll (10 * j + x / 2052) hs
  unfold wordsSl at h
  rw [strictB_eq, strictB_eq] at h
  have e1 : Nat.div (10 * j + x / 2052) 10 = j := by
    change (10 * j + x / 2052) / 10 = j
    omega
  have e2 : Nat.mul (Nat.mod (10 * j + x / 2052) 10) 2052 = x / 2052 * 2052 := by
    change (10 * j + x / 2052) % 10 * 2052 = x / 2052 * 2052
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  have h1 : x / 2052 * 2052 ≤ x := by omega
  have h2 : x < x / 2052 * 2052 + 2052 := by omega
  exact Nat.eq_of_beq_eq_true (sl_spec h x h1 h2 hx)

theorem words_ok : ∀ j < (j3Data ()).words.size, ∀ z ∈ ((j3Data ()).words)[j]!,
    z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
  decide

noncomputable abbrev LT8 : Array Table :=
  CFSG.Sporadic.Fi23.Native.slpLetters 20520 (genT 20520 TAt TBt) (j3Data ()).words

theorem letters_get : LT8.size = 8 ∧ ∀ l < 8, ∀ x < 20520, ap LT8[l]! x = LJ l x := by
  have hs : (j3Data ()).words.size = 4 := rfl
  have h := slpLetters_get (n := 20520) (gens := genT 20520 TAt TBt) (G := GJ) (L := LJ)
    (by norm_num) (fun z x hx => gens_get z hx) words_ok (fun j hj x hx => word_spec (by omega) hx)
    (fun j hj x hx => inv_spec (by omega) hx)
  rw [hs] at h
  exact h

theorem lt_range {l x : Nat} (hl : l < 8) (hx : x < 20520) : LJ l x < 20520 := by
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · exact (inv_spec (by omega) hx).1
  · exact (inv_spec (by omega) hx).2.1

theorem tree_spec {i : Nat} (hi : i < 2) :
    tbfsHdK 20520 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 20520 (CNTJ i) (lvK LJ BJ 8 i).length LJ (lvAt LJ BJ 8 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  interval_cases i
  · have h0 := tree0All 0 (by norm_num)
    unfold tree0Sl at h0
    rw [bAnd_iff] at h0
    refine ⟨h0.1, fun k hk => ?_⟩
    have hc : CNTJ 0 = 20520 := rfl
    have hs : k / 2052 < 10 := by rw [hc] at hk; omega
    have h := tree0All (k / 2052) hs
    unfold tree0Sl at h
    rw [bAnd_iff] at h
    have h2 := h.2
    unfold tbfsSlK at h2
    exact sl_spec (n := CT0.cnt) h2 k (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hk
  · have h : tree1 = true := tree1_ok
    unfold tree1 at h
    rw [bAnd_iff] at h
    exact ⟨h.1, allN_spec h.2⟩

theorem chain_hyp : ChainHyp 20520 8 2 LT8 (j3Data ()).base (j3Data ()).basis (j3Data ()).qb LJ BJ
    (j3Data ()).basis.toList (fun i => i) CNTJ PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_get.1, letters_get.2⟩
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem rels_spec : ∀ v ∈ TauCeti.Sporadic.j3Presentation.relatorLetters, ∀ x < 20520,
    List.foldr (letV (r32 TA) (r32 AI) (r32 TB) (r32 BI)) x v = x := by
  intro v hv x hx
  rw [CFSG.KC.J3A.rels_eq] at hv
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hv
  have hl : CFSG.KC.J3A.rels.length = 8 := rfl
  have hs : 10 * r + x / 2052 < 80 := by omega
  have h := relAll (10 * r + x / 2052) hs
  unfold relSl at h
  rw [strictB_eq, strictB_eq] at h
  have e1 : Nat.div (10 * r + x / 2052) 10 = r := by
    change (10 * r + x / 2052) / 10 = r
    omega
  have e2 : Nat.mul (Nat.mod (10 * r + x / 2052) 10) 2052 = x / 2052 * 2052 := by
    change (10 * r + x / 2052) % 10 * 2052 = x / 2052 * 2052
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  have h1 : x / 2052 * 2052 ≤ x := by omega
  have h2 : x < x / 2052 * 2052 + 2052 := by omega
  have h' := Nat.eq_of_beq_eq_true (sl_spec h x h1 h2 hx)
  rw [List.getD_eq_getElem _ _ hr] at h'
  have e : letK = letV (r32 TA) (r32 AI) (r32 TB) (r32 BI) := by
    funext l v
    obtain ⟨i, b⟩ := l
    unfold letK letV
    rcases i with _ | i <;> cases b <;> rfl
  rw [e] at h'
  exact h'

theorem permTA : PermF 20520 (r32 TA) := by
  unfold PermF
  exact ⟨fun x hx => (pt_spec hx).2.1, fun x hx y hy e => by
    rw [← (inv_facts hx).2.1, ← (inv_facts hy).2.1, e]⟩

theorem permTB : PermF 20520 (r32 TB) := by
  unfold PermF
  exact ⟨fun x hx => (pt_spec hx).2.2.1, fun x hx y hy e => by
    rw [← (inv_facts hx).2.2.2, ← (inv_facts hy).2.2.2, e]⟩

theorem card_le : Nat.card (Subgroup.closure (Set.range fun l : Fin 8 => permOfT 20520 LT8[l.val]!)) ≤
    ((List.range 2).map CNTJ).prod := by
  have hf : Finite TauCeti.Sporadic.j3Presentation.Group := Certificates.certificate9119.1
  have hP : TauCeti.Sporadic.j3Presentation.generatorCount = 2 := by
    simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.j3Presentation_generatorNames]
  set K := Subgroup.closure ({permF 20520 (r32 TA), permF 20520 (r32 TB)} :
    Set (Equiv.Perm (Fin 20520)))
  have iA := permF_inv permTA (fun x hx => (inv_facts hx).1) fun x hx => (inv_facts hx).2.1
  have iB := permF_inv permTB (fun x hx => (inv_facts hx).2.2.1) fun x hx => (inv_facts hx).2.2.2
  have hA : permF 20520 (r32 TA) ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : permF 20520 (r32 TB) ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hG : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → PermF 20520 (GJ z) ∧ permF 20520 (GJ z) ∈ K := by
    intro z hz ha
    rcases (by omega : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) with rfl | rfl | rfl | rfl
    · have e : GJ 1 = r32 TA := by funext x; rfl
      rw [e]
      exact ⟨permTA, hA⟩
    · have e : GJ (-1) = r32 AI := by funext x; rfl
      rw [e, iA.2]
      exact ⟨iA.1, K.inv_mem hA⟩
    · have e : GJ 2 = r32 TB := by funext x; rfl
      rw [e]
      exact ⟨permTB, hB⟩
    · have e : GJ (-2) = r32 BI := by funext x; rfl
      rw [e]
      refine ⟨iB.1, ?_⟩
      rw [iB.2]
      exact K.inv_mem hB
  have hmem := slp_mem (K := K) (G := GJ) (L := LJ) (words := (j3Data ()).words) hG words_ok
    (fun j hj x hx => word_spec (by have : (j3Data ()).words.size = 4 := rfl; omega) hx)
    (fun j hj x hx => have hj' : j < 4 := by have : (j3Data ()).words.size = 4 := rfl; omega
      ⟨(inv_spec hj' hx).2.1, (inv_spec hj' hx).2.2⟩)
  have hs : (j3Data ()).words.size = 4 := rfl
  rw [hs] at hmem
  refine le_trans (card_letters_le (L := LJ) TauCeti.Sporadic.j3Presentation hP permTA permTB
    (fun x hx => ⟨(inv_facts hx).1, (inv_facts hx).2.1⟩)
    (fun x hx => ⟨(inv_facts hx).2.2.1, (inv_facts hx).2.2.2⟩) rels_spec letters_get.2 hmem) ?_
  refine le_trans Certificates.certificate9119.2 ?_
  decide

theorem chain_eq : chainTrees 20520 LT8 (j3Data ()).base =
      Array.ofFn (n := 2) (fun i => tbfsRec 20520 (CNTJ i.val) (PTSJ i.val) (POSJ i.val)
        (PARJ i.val) (LABJ i.val)) ∧
    ∀ chunks, chainOK 20520 LT8 (j3Data ()).base (j3Data ()).basis (j3Data ()).qb
      (chainTrees 20520 LT8 (j3Data ()).base) chunks = true :=
  pchain_of_card chain_hyp card_le

theorem trees0 : (chainTrees 20520 LT8 (j3Data ()).base)[0]! =
    tbfsRec 20520 CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB := by
  rw [chain_eq.1, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  rfl

theorem sizes : (orbitSizes (chainTrees 20520 LT8 (j3Data ()).base) == (j3Data ()).orbSizes) =
    true := by
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  rfl

theorem lv1_eq : levelLetters LT8 (j3Data ()).base 1 = (lvK LJ BJ 8 1).toArray := by
  rw [← Array.toList_inj]
  simp only [levelLetters, Array.toList_filter, Array.toList_range, letters_get.1, lvK]
  apply List.filter_congr
  intro l hl
  have hl' : l < 8 := List.mem_range.1 hl
  have e : (j3Data ()).base[0]! = 0 := rfl
  rw [e, letters_get.2 l hl' 0 (by norm_num), Bool.eq_iff_iff, CFSG.KLC.E8.allN_iff]
  simp [BJ]

theorem lab_spec {z : Nat} (hz : z < 20520) : r32 LBL z < 22 ∧
    r32 (SPOSJ (r32 LBL z)) z < SCNTJ (r32 LBL z) ∧
    r32 (SPTSJ (r32 LBL z)) (r32 (SPOSJ (r32 LBL z)) z) = z := by
  have hs : z / 2052 < 10 := by omega
  have h := labAll (z / 2052) hs
  unfold labSl at h
  have h' := sl_spec (lo := Nat.mul (z / 2052) 2052) (len := 2052) (n := 20520) h z (by
    simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hz
  rw [strictB_eq] at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

theorem labOK_spec : ∀ l < 22, (r32 CT0.POS (REPJ l) < CT0.cnt ∧
    r32 CT0.PTS (r32 CT0.POS (REPJ l)) = REPJ l) ∧ ∀ q < SCNTJ l, r32 LBL (r32 (SPTSJ l) q) = l := by
  intro l hl
  have h := allN_spec labOK_ok l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1, fun q hq => by
    have := allN_spec h.2 q hq
    simpa using this⟩

noncomputable abbrev SJ : Array Tree := (j3Data ()).subReps.map fun r =>
  treeBFS (j3Data ()).n r LT8 (levelLetters LT8 (j3Data ()).base 1)

theorem sub_ok : subChecks (j3Data ()) LT8 (levelLetters LT8 (j3Data ()).base 1) SJ
      (labelsOf (j3Data ()).n SJ) = true ∧
    derivChecks (j3Data ()) LT8 (tbfsRec (j3Data ()).n CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB)
      (labelsOf (j3Data ()).n SJ) = true := j3sub_sound (NL := 8) (k := 22) (cnt0 := CT0.cnt) (j3Data ()) (letters := LT8)
    (lv := levelLetters LT8 (j3Data ()).base 1) (L := LJ) (B := BJ) (PTS0 := CT0.PTS)
    (POS0 := CT0.POS) (PAR0 := CT0.PAR) (LAB0 := CT0.LAB) (LBL := r32 LBL) (REP := REPJ)
    (SCNT := SCNTJ) (SPTS := SPTSJ) (SPOS := SPOSJ) (SPAR := SPARJ) (SLAB := SLABJ) (STI := STIJ)
    ⟨letters_get.1, fun l hl x hx => ⟨letters_get.2 l hl x hx, lt_range hl hx⟩⟩ lv1_eq
    ⟨by decide, rfl⟩ ⟨rfl, by norm_num, rfl, fun _ _ => rfl⟩ ⟨rfl, rfl⟩
    (fun l hl => (labOK_spec l hl).1)
    (fun q hq h0 => (letter_facts chain_hyp
      (mem_lvK.1 (lab_mem chain_hyp (i := 0) (by norm_num) hq h0)).1).1)
    (fun l hl => by
      have h := subAll l hl
      unfold subTree at h
      rw [bAnd_iff] at h
      exact ⟨h.1, allN_spec h.2⟩)
    (fun z hz => lab_spec hz) (fun l hl q hq => (labOK_spec l hl).2 q hq)
    (fun c h1 h2 => by
      obtain ⟨c', rfl⟩ : ∃ c', c = Nat.succ c' := ⟨c - 1, by omega⟩
      have hc : c' < 21 := by omega
      exact allN_spec der_ok c' hc)

theorem rowsA_D : (j3Data ()).rowsA = RAL.toArray := by
  unfold Data.rowsA
  have e : (j3Data ()).seedA = String.ofList J3SeedA.chars := J3SeedA.eq
  rw [e, payRun_eq, rowsA_eq]

theorem rowsB_D : (j3Data ()).rowsB = RBL.toArray := by
  unfold Data.rowsB
  have e : (j3Data ()).seedB = String.ofList J3SeedB.chars := J3SeedB.eq
  rw [e, payRun_eq, rowsB_eq]

theorem orbit_ok : orbitChecks (j3Data ()) CAJ CBJ PTS TAt TBt = true := by
  unfold orbitChecks
  have hn : (j3Data ()).n = 20520 := rfl
  simp only [hn, Bool.and_eq_true]
  have hb : r32 TB 0 < 20520 := (pt_spec (by norm_num)).2.2.1
  rw [ta_get (by norm_num), tb_get (by norm_num), ta_get hb]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨orbitOK_ok, ?_⟩, ?_⟩, invA.1⟩, invB.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide
  · rw [← Array.all_toList]
    decide
  · have hb : ∀ i ∈ (j3Data ()).basis, i < 20520 := by
      intro i hi
      have h := Array.all_eq_true_iff_forall_mem.1 (by rw [← Array.all_toList]; decide :
        (j3Data ()).basis.all (fun i => decide (i < 20520)) = true) i hi
      simpa using h
    rw [Array.map_congr_left (g := PJ) fun i hi => pts_get (hb i hi)]
    decide +kernel

theorem j3_cert : check (j3Data ()) 3 = true := by
  unfold check
  simp only [Bool.and_eq_true]
  have hv : (j3Data ()).v0 = 16561281922307987041 := rfl
  have hn : (j3Data ()).n = 20520 := rfl
  rw [rowsA_D, rowsB_D, colsA_eq, colsB_eq, hv, hn, orb_eq.1, orb_eq.2.1, orb_eq.2.2]
  refine ⟨⟨⟨⟨mat_ok, orbit_ok⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold chainChecks
    simp only [Bool.and_eq_true, hn]
    refine ⟨⟨⟨⟨⟨?_, by decide⟩, by decide⟩, by decide⟩, chain_eq.2 3⟩, sizes⟩
    unfold CFSG.Sporadic.Fi23.Native.slpOK allIn
    rw [CFSG.KS.F3R.all_eq]
    decide +kernel
  · exact sub_ok.1
  · rw [trees0]
    exact sub_ok.2

end CertificateChecks.KernelSpor.J3K

end
