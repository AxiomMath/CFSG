module

public import Certificates.Kernel.Fi22Core.ChainChecks
public import Certificates.Kernel.Fi22.Letters
public import CFSG.Certificates.Kernel.Spor.PChainSound
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22C.t0All CertificateChecks.KernelFi22C.t0Sl 55
#kon_join CertificateChecks.KernelFi22C.t1All CertificateChecks.KernelFi22C.t1Sl 44
#kon_join CertificateChecks.KernelFi22C.t2All CertificateChecks.KernelFi22C.t2Sl 27
#kon_join CertificateChecks.KernelFi22C.u2All CertificateChecks.KernelFi22C.u2Sl 11

namespace CertificateChecks.KernelFi22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.Fi22L CFSG.KS.TW
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem sl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := allN_spec h (k - lo) (by omega)
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem cnts : CNTJ 0 = 3510 ∧ CNTJ 1 = 2816 ∧ CNTJ 2 = 1680 ∧ CNTJ 3 = 108 ∧ CNTJ 4 = 36 ∧
    T2.cnt = 693 := by
  have h := sizes_ok
  unfold sizesK at h
  simp only [bAnd_iff, Nat.beq_eq] at h
  exact h

theorem pt_of {i c : Nat} (h : ptSl i c = true) : ∀ k, 64 * c ≤ k → k < 64 * c + 64 → k < CNTJ i →
    tbfsPtK 3510 (CNTJ i) (lvK LJ BJ 32 i).length LJ (lvAt LJ BJ 32 i) (PTSJ i) (POSJ i) (PARJ i)
      (LABJ i) (TIJ i) k = true := by
  intro k h1 h2 h3
  unfold ptSl at h
  exact sl_spec h k (by change c * 64 ≤ k; omega) (by change k < c * 64 + 64; omega) h3

theorem tree_spec {i : Nat} (hi : i < 5) :
    tbfsHdK 3510 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 3510 (CNTJ i) (lvK LJ BJ 32 i).length LJ (lvAt LJ BJ 32 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  refine ⟨allN_spec hd_ok i hi, fun k hk => ?_⟩
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := cnts
  have h34 := t34_ok
  unfold t34K at h34
  rw [bAnd_iff, bAnd_iff] at h34
  interval_cases i
  · rw [c0] at hk
    have hs : k / 64 < 55 := by omega
    exact pt_of (t0All (k / 64) hs) k (by omega) (by omega) (by rw [c0]; exact hk)
  · rw [c1] at hk
    have hs : k / 64 < 44 := by omega
    exact pt_of (t1All (k / 64) hs) k (by omega) (by omega) (by rw [c1]; exact hk)
  · rw [c2] at hk
    have hs : k / 64 < 27 := by omega
    exact pt_of (t2All (k / 64) hs) k (by omega) (by omega) (by rw [c2]; exact hk)
  · rw [c3] at hk
    rcases (by omega : k < 64 ∨ 64 ≤ k) with hk' | hk'
    · exact pt_of h34.1 k (by change 64 * 0 ≤ k; omega) (by change k < 64 * 0 + 64; omega)
        (by rw [c3]; exact hk)
    · exact pt_of h34.2.1 k (by change 64 * 1 ≤ k; omega) (by change k < 64 * 1 + 64; omega)
        (by rw [c3]; exact hk)
  · rw [c4] at hk
    exact pt_of h34.2.2 k (by change 64 * 0 ≤ k; omega) (by change k < 64 * 0 + 64; omega)
      (by rw [c4]; exact hk)

theorem letters_TR {l : Nat} (hl : l < 32) : TR 3510 (chainLetters orbL)[l]! (LJ l) :=
  CertificateChecks.KernelFi22.Letters.letters.2.1 l hl

theorem inv_ok : invK LJ 3510 32 = true := by
  unfold invK
  rw [Raw.Orb.allN_iff]
  intro j hj
  change j < 16 at hj
  rw [Raw.Orb.allN_iff]
  intro x hx
  rw [Raw.Orb.strictB_eq, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
  have e0 : Nat.mul 2 j = 2 * j := rfl
  have e1 : Nat.succ (Nat.mul 2 j) = 2 * j + 1 := rfl
  rw [e1, e0]
  have t0 := (letters_TR (l := 2 * j) (by omega)).2 x hx
  have t1 := (letters_TR (l := 2 * j + 1) (by omega)).2 x hx
  refine ⟨t0.2, t1.2, ?_⟩
  have f := inv_facts (CertificateChecks.KernelFi22.Letters.ivAll j hj) hx
  unfold LJ
  rw [LJk_eq, LJk_eq]
  have m0 : 2 * j % 2 = 0 := by omega
  have m1 : (2 * j + 1) % 2 = 1 := by omega
  have d0 : 2 * j / 2 = j := by omega
  have d1 : (2 * j + 1) / 2 = j := by omega
  simp only [m0, m1, d0, d1, ↓reduceIte, Nat.one_ne_zero]
  exact f.2.1

theorem chain_hyp : ChainHyp 3510 32 5 (chainLetters orbL) chainBase chainQ chainQb LJ BJ QL QB CNTJ
    PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨CertificateChecks.KernelFi22.Letters.letters.1, fun l hl x hx => ((letters_TR hl).2 x hx).1⟩
  inv := ⟨rfl, inv_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem prod_cnt : ((List.range 5).map CNTJ).prod = 64561751654400 := by
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := cnts
  change CNTJ 0 * (CNTJ 1 * (CNTJ 2 * (CNTJ 3 * (CNTJ 4 * 1)))) = _
  rw [c0, c1, c2, c3, c4]

abbrev Hcard : Prop :=
  Nat.card (Subgroup.closure (Set.range fun l : Fin 32 => permOfT 3510 (chainLetters orbL)[l.val]!)) ≤
    64561751654400

theorem chain_eq (hcard : Hcard) : chainTrees 3510 (chainLetters orbL) chainBase =
      Array.ofFn (n := 5) (fun i => tbfsRec 3510 (CNTJ i.val) (PTSJ i.val) (POSJ i.val)
        (PARJ i.val) (LABJ i.val)) ∧
    ∀ chunks, chainOK 3510 (chainLetters orbL) chainBase chainQ chainQb
      (chainTrees 3510 (chainLetters orbL) chainBase) chunks = true :=
  pchain_of_card chain_hyp (hcard.trans (le_of_eq prod_cnt.symm))

theorem sizes (hcard : Hcard) : (orbitSizes (chainTrees 3510 (chainLetters orbL) chainBase) ==
    [3510, 2816, 1680, 108, 36]) = true := by
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := cnts
  rw [(chain_eq hcard).1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  decide +kernel

theorem lv1_eq : levelLetters (chainLetters orbL) chainBase 1 = (lvK LJ BJ 32 1).toArray :=
  levelLetters_eq chain_hyp 1 (by norm_num)

theorem u2_pts : ∀ k < T2.cnt, tbfsPtK 3510 T2.cnt (lvK LJ BJ 32 1).length LJ (lvAt LJ BJ 32 1)
    T2.PTS T2.POS T2.PAR T2.LAB T2.TI k = true := by
  intro k hk
  have c := cnts.2.2.2.2.2
  have hs : k / 64 < 11 := by rw [c] at hk; omega
  have h := u2All (k / 64) hs
  unfold u2Sl at h
  exact sl_spec h k (by change k / 64 * 64 ≤ k; omega) (by change k < k / 64 * 64 + 64; omega) hk

theorem t2_eq : treeBFS 3510 (subRoot ()) (chainLetters orbL)
      (levelLetters (chainLetters orbL) chainBase 1) = tbfsRec 3510 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB ∧
    treeOK 3510 (subRoot ()) (tbfsRec 3510 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB) (chainLetters orbL)
      (levelLetters (chainLetters orbL) chainBase 1) = true := by
  rw [lv1_eq]
  refine tbfsK_sound (L := LJ) (LV := lvAt LJ BJ 32 1) ⟨by simp, fun t ht => ?_⟩ u2hd_ok u2_pts
  have ht' : t < (lvK LJ BJ 32 1).length := by simpa using ht
  have hm := List.getElem_mem ht'
  have hlt : (lvK LJ BJ 32 1)[t] < 32 := by
    unfold lvK at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have e : (lvK LJ BJ 32 1).toArray[t]! = lvAt LJ BJ 32 1 t := by
    rw [getElem!_pos _ t (by simpa using ht')]
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e]
  have e2 : lvAt LJ BJ 32 1 t = (lvK LJ BJ 32 1)[t] := by
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e2]
  exact ⟨rfl, by rw [CertificateChecks.KernelFi22.Letters.letters.1]; exact hlt,
    fun x hx => ((letters_TR hlt).2 x hx).1⟩

theorem cover (hcard : Hcard) : allIn 0 3510 (fun p => p == 0 ||
    (ap (chainTrees 3510 (chainLetters orbL) chainBase)[1]!.pos p <
        (chainTrees 3510 (chainLetters orbL) chainBase)[1]!.pts.size &&
      ap (chainTrees 3510 (chainLetters orbL) chainBase)[1]!.pts
        (ap (chainTrees 3510 (chainLetters orbL) chainBase)[1]!.pos p) == p) ||
    (ap (tbfsRec 3510 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB).pos p < 693 &&
      ap (tbfsRec 3510 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB).pts
        (ap (tbfsRec 3510 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB).pos p) == p)) = true := by
  obtain ⟨-, c1, -, -, -, c5⟩ := cnts
  rw [(chain_eq hcard).1, CFSG.KS.TW.allIn_iff]
  have e1 : (Array.ofFn (n := 5) (fun i => tbfsRec 3510 (CNTJ i.val) (PTSJ i.val) (POSJ i.val)
      (PARJ i.val) (LABJ i.val)))[1]! = tbfsRec 3510 CT1.cnt CT1.PTS CT1.POS CT1.PAR CT1.LAB := by
    rw [getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
    rfl
  rw [e1]
  intro p hp
  have h := allN_spec cover_ok p hp
  have hpos : ∀ {cnt : Nat} {PTS POS PAR LAB : Nat → Nat},
      ap (tbfsRec 3510 cnt PTS POS PAR LAB).pos p = r32 POS p := by
    intro cnt PTS POS PAR LAB
    unfold tbfsRec
    exact ap_ofFn hp
  have hpts : ∀ {cnt : Nat} {PTS POS PAR LAB : Nat → Nat} {q : Nat}, q < cnt →
      ap (tbfsRec 3510 cnt PTS POS PAR LAB).pts q = r32 PTS q := by
    intro cnt PTS POS PAR LAB q hq
    unfold tbfsRec
    exact ap_ofFn hq
  have hs1 : (tbfsRec 3510 CT1.cnt CT1.PTS CT1.POS CT1.PAR CT1.LAB).pts.size = CT1.cnt := by
    simp [tbfsRec]
  rw [hs1, hpos, hpos]
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h0 : p = 0
  · exact Or.inl (Or.inl h0)
  have e0 : Nat.beq p 0 = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact h0 (Nat.eq_of_beq_eq_true e)
  by_cases h1 : r32 CT1.POS p < CT1.cnt ∧ r32 CT1.PTS (r32 CT1.POS p) = p
  · exact Or.inl (Or.inr ⟨h1.1, by rw [hpts h1.1]; exact h1.2⟩)
  have e1 : bAnd(Nat.blt (r32 CT1.POS p) CT1.cnt, Nat.beq (r32 CT1.PTS (r32 CT1.POS p)) p) = false := by
    rw [Bool.eq_false_iff]
    intro e
    rw [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at e
    exact h1 e
  rw [e0, e1] at h
  change bAnd(Nat.blt (r32 T2.POS p) 693, Nat.beq (r32 T2.PTS (r32 T2.POS p)) p) = true at h
  rw [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  refine Or.inr ⟨h.1, ?_⟩
  rw [hpts (by rw [c5]; exact h.1)]
  exact h.2

end CertificateChecks.KernelFi22C

end
