module

public import Certificates.Kernel.Sporadic.J2K.Checks
public import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Certificates.Kernel.Spor.PrimKSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.LocalCompSPCode
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Perm.Basic
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.J2K.sch0All CertificateChecks.KernelSpor.J2K.sch0 7

namespace CertificateChecks.KernelSpor.J2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.PR
open CFSG.Sporadic.J2.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.J1.Native (Orb orbBFS orbOK eqRel vecSep genTables colMat gaussInv wfM mulL idL
  primOK primData)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

noncomputable abbrev OJ : Orb := vorbRec 14 315 PJ2 AL BE PA LA

theorem pt_spec {i : Nat} (hi : i < 315) :
    vorbPtK 5 14 315 id (mA ()) (mB ()) PJ2 AL BE i = true :=
  allN_spec orbPt_ok i hi

theorem orb_eq : orbitData () = OJ ∧ orbOK 5 14 eqRel (mA ()) (mB ()) (root ()) OJ = true := by
  have hp := allN_spec orbPt_ok
  have hs := allN_spec orbSort_ok
  have h := vorb_sound (cap := 400) orbHd_ok hp hs
  exact ⟨h.1, h.2 _ fun w _ => by simp [eqRel]⟩

theorem ap_ofFn {N : Nat} {f : Nat → Nat} {x : Nat} (hx : x < N) (hf : f x < 2 ^ 32) :
    ap (Array.ofFn (n := N) fun i => UInt32.ofNat (f i.val)) x = f x := by
  unfold ap
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hf

theorem inv_facts {x : Nat} (hx : x < 315) : r32 AL x < 315 ∧ r32 AI (r32 AL x) = x ∧
    r32 BE x < 315 ∧ r32 BI (r32 BE x) = x ∧ r32 AI x < 315 ∧ r32 BI x < 315 := by
  have h := allN_spec invAB_ok x hx
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem al_get {x : Nat} (hx : x < 315) : ap OJ.alpha x = r32 AL x :=
  ap_ofFn hx (by have := (inv_facts hx).1; omega)

theorem be_get {x : Nat} (hx : x < 315) : ap OJ.beta x = r32 BE x :=
  ap_ofFn hx (by have := (inv_facts hx).2.2.1; omega)

theorem invA : invOK 315 OJ.alpha (invT 315 OJ.alpha) = true ∧
    ∀ y < 315, ap (invT 315 OJ.alpha) y = r32 AI y :=
  invT_get (f := r32 AL) (by norm_num) fun x hx =>
    ⟨al_get hx, (inv_facts hx).1, (inv_facts hx).2.1⟩

theorem invB : invOK 315 OJ.beta (invT 315 OJ.beta) = true ∧
    ∀ y < 315, ap (invT 315 OJ.beta) y = r32 BI y :=
  invT_get (f := r32 BE) (by norm_num) fun x hx =>
    ⟨be_get hx, (inv_facts hx).2.2.1, (inv_facts hx).2.2.2.1⟩

theorem size_OJ : OJ.pts.size = 315 := by simp [vorbRec]

theorem GJ_eq (z : Int) (x : Nat) : GJ z x =
    if z = 1 then r32 AL x else if z = -1 then r32 AI x else if z = 2 then r32 BE x else r32 BI x := by
  rcases z with ((_ | _ | _ | k) | (_ | k)) <;> rfl

theorem gens_get (z : Int) {x : Nat} (hx : x < 315) :
    ap (genTables OJ z) x = GJ z x ∧ GJ z x < 315 := by
  have hf := inv_facts hx
  rw [GJ_eq]
  unfold genTables
  rw [size_OJ]
  by_cases h1 : z = 1
  · simp only [h1, ↓reduceIte]
    exact ⟨al_get hx, hf.1⟩
  by_cases h2 : z = -1
  · simp only [h2, ↓reduceIte]
    exact ⟨invA.2 x hx, hf.2.2.2.2.1⟩
  by_cases h3 : z = 2
  · simp only [h3, ↓reduceIte]
    exact ⟨be_get hx, hf.2.2.1⟩
  · simp only [h1, h2, h3, ↓reduceIte]
    exact ⟨invB.2 x hx, hf.2.2.2.2.2⟩

theorem inv_spec {j x : Nat} (hj : j < 8) (hx : x < 315) : LJ (2 * j) x < 315 ∧
    LJ (2 * j + 1) x < 315 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 315 16 = true := invL_ok
  unfold invK at h0
  have hj' : j < Nat.div 16 2 := by change j < 16 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem word_spec {j x : Nat} (hj : j < 8) (hx : x < 315) :
    LJ (2 * j) x = List.foldr GJ x (chainWords ())[j]! :=
  Nat.eq_of_beq_eq_true (allN_spec (allN_spec wordsOK_ok j hj) x hx)

theorem letters_get : (chainLetters OJ).size = 16 ∧
    ∀ l < 16, ∀ x < 315, ap (chainLetters OJ)[l]! x = LJ l x ∧ LJ l x < 315 := by
  have hb := buildLetters_get (n := 315) (gens := genTables OJ) (words := chainWords ()) (G := GJ)
    (H := fun j => LJ (2 * j + 1)) (by norm_num) (fun z x hx => gens_get z hx)
    (fun j hj x hx => by
      have hj' : j < 8 := hj
      rw [← word_spec hj' hx]
      exact (inv_spec hj' hx).2.2)
  have e : chainLetters OJ = buildLetters 315 (genTables OJ) (chainWords ()) := rfl
  rw [e]
  refine ⟨hb.1, fun l hl x hx => ?_⟩
  have hs : (chainWords ()).size = 8 := rfl
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · have hj : j < 8 := by omega
    exact ⟨by rw [(hb.2 j (by rw [hs]; exact hj) x hx).1, word_spec hj hx], (inv_spec hj hx).1⟩
  · have hj : j < 8 := by omega
    exact ⟨(hb.2 j (by rw [hs]; exact hj) x hx).2, (inv_spec hj hx).2.1⟩

theorem tree_spec {i : Nat} (hi : i < 3) :
    tbfsHdK 315 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 315 (CNTJ i) (lvK LJ BJ 16 i).length LJ (lvAt LJ BJ 16 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  have h := allN_spec tree_ok i hi
  unfold tree at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, allN_spec h2⟩

theorem schSl_spec {i lo len : Nat}
    (h : schSlK LJ BJ 16 PTSJ POSJ PARJ LABJ CNTJ QB QL 3 i lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < CNTJ i → ∀ t < (lvK LJ BJ 16 i).length,
      schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 3 i (lvAt LJ BJ 16 i t) k = true := by
  intro k h1 h2 h3 t ht
  unfold schSlK at h
  rw [strictB_eq] at h
  have h' := allN_spec h (k - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact allN_spec h' t ht

theorem cnt0 : CNTJ 0 = 315 := rfl
theorem cnt1 : CNTJ 1 = 160 := rfl
theorem cnt2 : CNTJ 2 = 12 := rfl

theorem sch_spec : ∀ i < 3, ∀ k < CNTJ i, ∀ t < (lvK LJ BJ 16 i).length,
    schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 3 i (lvAt LJ BJ 16 i t) k = true := by
  intro i hi k hk
  have h12 : sch12 = true := sch12_ok
  unfold sch12 at h12
  rw [bAnd_iff] at h12
  interval_cases i
  · have hs : k / 45 < 7 := by rw [cnt0] at hk; omega
    exact schSl_spec (sch0All (k / 45) hs) k (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hk
  · exact schSl_spec h12.1 k (Nat.zero_le _) (by rw [cnt1] at hk; omega) hk
  · exact schSl_spec h12.2 k (Nat.zero_le _) (by rw [cnt2] at hk; omega) hk

theorem chain_hyp : ChainHyp 315 16 3 (chainLetters OJ) chainBase chainQ chainQb LJ BJ QL QB CNTJ
    PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_get.1, fun l hl x hx => (letters_get.2 l hl x hx).1⟩
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem chain_eq : chainTrees 315 (chainLetters OJ) chainBase =
      Array.ofFn (n := 3) (fun i => tbfsRec 315 (CNTJ i.val) (PTSJ i.val) (POSJ i.val) (PARJ i.val)
        (LABJ i.val)) ∧
    ∀ chunks, chainOK 315 (chainLetters OJ) chainBase chainQ chainQb
      (chainTrees 315 (chainLetters OJ) chainBase) chunks = true :=
  pchainK_sound chain_hyp sch_spec term_ok

theorem trees0 : (chainTrees 315 (chainLetters OJ) chainBase)[0]! =
    tbfsRec 315 CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB := by
  rw [chain_eq.1, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  rfl

theorem sizes : (orbitSizes (chainTrees 315 (chainLetters OJ) chainBase) == [315, 160, 12]) = true := by
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  rfl

theorem lv1_eq : levelLetters (chainLetters OJ) chainBase 1 = (lvK LJ BJ 16 1).toArray := by
  rw [← Array.toList_inj]
  simp only [levelLetters, Array.toList_filter, Array.toList_range, letters_get.1, lvK]
  apply List.filter_congr
  intro l hl
  have hl' : l < 16 := List.mem_range.1 hl
  have e : chainBase[0]! = 0 := rfl
  rw [e, (letters_get.2 l hl' 0 (by norm_num)).1, Bool.eq_iff_iff, CFSG.KLC.E8.allN_iff]
  simp [BJ]

theorem der_spec {i : Nat} (hi : i < 6) (hne : i ≠ r32 LBL 0) :
    derK 315 6 LBL IM DS DOFF DLEN i = true := by
  have h := allN_spec der_ok i hi
  revert h
  cases hb : Nat.beq i (r32 LBL 0)
  · intro h
    exact h
  · exact absurd (Nat.eq_of_beq_eq_true hb) hne

theorem subLbl_ok : CFSG.KC.Enum.allN 6 (fun l => CFSG.KC.Enum.allN (SCNTJ l) (subLblK LBL SPTSJ l)) =
    true := by quickRfl

theorem lab0_lt {q : Nat} (hq : q < CT0.cnt) (h0 : 0 < q) : r32 CT0.LAB q < 16 := by
  have hp := (CFSG.KS.TBfs.pt_spec ((tree_spec (i := 0) (by norm_num)).2 q hq)).tree h0
  change r32 (LABJ 0) q < 16
  rw [hp.2.2.1]
  exact (CFSG.KS.PC.mem_lvK.1 (CFSG.KS.PC.lvAt_mem hp.2.1)).1

theorem prim_ok : primOK 315 (chainLetters OJ) (levelLetters (chainLetters OJ) chainBase 1)
    (chainTrees 315 (chainLetters OJ) chainBase)[0]!
    (primData 315 (chainLetters OJ) (levelLetters (chainLetters OJ) chainBase 1)
      (chainTrees 315 (chainLetters OJ) chainBase)[0]!) = true := by
  rw [trees0]
  exact prim_sound (k := 6) (B := BJ) (SPTS := SPTSJ) (SPOS := SPOSJ) (SPAR := SPARJ)
    (SLAB := SLABJ) (STI := STIJ) (SCNT := SCNTJ) (IM := IM) (DS := DS) (DOFF := DOFF)
    (DLEN := DLEN) letters_get lv1_eq (by norm_num) (fun q hq h0 _ => lab0_lt hq h0)
    (allN_spec subPt_ok) (allN_spec subRep_ok)
    (fun l hl => by
      have h := allN_spec subTree_ok l hl
      unfold subTree at h
      rw [bAnd_iff] at h
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, allN_spec h2⟩)
    (fun l hl q hq => allN_spec (allN_spec subLbl_ok l hl) q hq)
    (fun l hl x hx => allN_spec (allN_spec imAt_ok l hl) x hx) fun i hi hne => der_spec hi hne

noncomputable abbrev PM : List (List Nat) := colMat 14 [[0, 0, 0, 1, 1, 2, 3, 3, 0, 4, 3, 1, 1, 3],
  [0, 0, 1, 0, 3, 3, 4, 0, 0, 3, 1, 3, 1, 4], [1, 3, 3, 2, 1, 3, 4, 0, 1, 1, 3, 4, 1, 3],
  [0, 0, 1, 0, 2, 1, 3, 3, 4, 0, 1, 3, 4, 1], [0, 0, 0, 1, 3, 3, 0, 4, 2, 3, 3, 1, 3, 1],
  [3, 1, 2, 3, 3, 1, 0, 4, 3, 3, 4, 3, 4, 4], [3, 1, 0, 1, 0, 4, 1, 1, 3, 3, 0, 1, 3, 4],
  [1, 3, 3, 3, 0, 4, 0, 3, 3, 1, 0, 1, 4, 3], [2, 1, 2, 3, 3, 0, 3, 3, 1, 4, 4, 4, 4, 3],
  [1, 3, 1, 0, 4, 0, 1, 1, 0, 0, 1, 0, 3, 0], [3, 1, 3, 3, 4, 0, 3, 0, 1, 1, 1, 0, 0, 3],
  [3, 1, 0, 0, 0, 0, 3, 1, 4, 0, 3, 4, 3, 1], [1, 2, 3, 2, 0, 3, 3, 3, 1, 0, 4, 4, 1, 2],
  [1, 0, 4, 4, 3, 1, 0, 0, 0, 1, 1, 3, 0, 0]]

noncomputable abbrev YM : List (List Nat) := [[3, 2, 0, 4, 4, 4, 4, 0, 2, 3, 2, 0, 3, 4],
  [0, 2, 0, 4, 1, 1, 1, 4, 2, 0, 2, 1, 1, 0], [4, 0, 0, 2, 3, 2, 3, 2, 1, 2, 4, 2, 0, 3],
  [4, 0, 3, 3, 1, 2, 4, 3, 0, 1, 1, 0, 2, 4], [4, 0, 3, 4, 4, 3, 0, 0, 2, 3, 3, 4, 3, 1],
  [2, 4, 1, 0, 1, 4, 0, 3, 1, 0, 0, 4, 1, 4], [1, 4, 3, 0, 4, 2, 1, 3, 3, 2, 4, 4, 0, 2],
  [2, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 2, 4, 3], [3, 3, 1, 0, 4, 1, 0, 0, 4, 3, 3, 3, 1, 3],
  [4, 3, 1, 2, 1, 0, 3, 2, 2, 1, 4, 2, 3, 2], [0, 2, 4, 3, 2, 2, 3, 2, 0, 4, 3, 4, 3, 3],
  [2, 0, 4, 2, 1, 4, 2, 2, 3, 0, 1, 2, 0, 4], [1, 3, 0, 1, 1, 4, 4, 0, 2, 2, 1, 0, 2, 0],
  [4, 2, 3, 3, 0, 0, 1, 0, 4, 0, 0, 1, 2, 2]]

theorem pts_get {q : Nat} (hq : q < 315) : OJ.pts[q]! = decV 14 (PJ2 q) := by
  rw [getElem!_pos _ q (by simpa [vorbRec] using hq)]
  simp [vorbRec]

theorem qMat_eq : qMat OJ = PM := by
  unfold qMat qVecs
  simp only [chainQ, List.map_cons, List.map_nil]
  rw [pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num),
    pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num),
    pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num),
    pts_get (by norm_num), pts_get (by norm_num)]
  decide +kernel

theorem gauss_eq : gaussInv 5 14 PM = YM :=
  gaussInv_eq (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem moves : (ap OJ.alpha 0 != 0) = true ∧ (ap OJ.beta 0 != 0) = true ∧
    (ap OJ.alpha (ap OJ.beta 0) != 0) = true := by
  have hb : r32 BE 0 < 315 := (inv_facts (by norm_num)).2.2.1
  rw [be_get (by norm_num), al_get (by norm_num), al_get hb]
  decide +kernel

theorem j2_cert : j2Certificate 3 = true := by
  unfold j2Certificate
  rw [orb_eq.1]
  unfold actionChecks
  simp only [Bool.and_eq_true]
  rw [qMat_eq, gauss_eq]
  refine ⟨by decide +kernel, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨orb_eq.2, by rw [size_OJ]; rfl⟩, ?_⟩, invA.1⟩, invB.1⟩,
    chain_eq.2 3⟩, sizes⟩, by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩, moves.1⟩,
    moves.2.1⟩, moves.2.2⟩, prim_ok⟩⟩
  exact vecSep_of_sort (fun i hi => by
      have h := pt_spec hi
      unfold vorbPtK at h
      simp only [strictB_eq, bAnd_iff, Nat.blt_eq] at h
      have e : Nat.shiftLeft 1 (Nat.mul 4 14) = 2 ^ (4 * 14) := by norm_num
      rw [← e]
      exact h.1)
    (allN_spec orbSort_ok)

end CertificateChecks.KernelSpor.J2K

end
