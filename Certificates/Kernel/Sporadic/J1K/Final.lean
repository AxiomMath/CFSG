module

public import Certificates.Kernel.Sporadic.J1K.Checks
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

#kon_join CertificateChecks.KernelSpor.J1K.sch0All CertificateChecks.KernelSpor.J1K.sch0 28

namespace CertificateChecks.KernelSpor.J1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.PR
open CFSG.Sporadic.J1.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

noncomputable abbrev OJ : Orb := vorbRec 7 1540 (r32 PT) AL BE PA LA

theorem pm_key (w : List Nat) (hw : ∀ x ∈ w, x < 11) : pmRel 11 w (sgnKey 11 w) = true := by
  unfold pmRel sgnKey
  split
  · simp
  · have e : negL 11 (negL 11 w) = w := by
      unfold negL
      rw [List.map_map]
      conv_rhs => rw [← List.map_id w]
      apply List.map_congr_left
      intro x hx
      have := hw x hx
      simp only [Function.comp_apply, id_eq]
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rfl
      · rw [Nat.mod_eq_of_lt (by omega : 11 - x < 11)]
        rw [Nat.mod_eq_of_lt (by omega : 11 - (11 - x) < 11)]
        omega
    simp [e]

theorem orb_eq : orbitData () = OJ ∧ orbOK 11 7 (pmRel 11) (mA ()) (mB ()) (root ()) OJ = true := by
  have hp := allN_spec orbPt_ok
  have hs := allN_spec orbSort_ok
  have h := vorb_sound (cap := 2000) orbHd_ok hp hs
  exact ⟨h.1, h.2 _ pm_key⟩

theorem pt_spec {i : Nat} (hi : i < 1540) :
    vorbPtK 11 7 1540 (sgnKey 11) (mA ()) (mB ()) (r32 PT) AL BE i = true :=
  allN_spec orbPt_ok i hi

theorem ap_ofFn {N : Nat} {f : Nat → Nat} {x : Nat} (hx : x < N) (hf : f x < 2 ^ 32) :
    ap (Array.ofFn (n := N) fun i => UInt32.ofNat (f i.val)) x = f x := by
  unfold ap
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hf

theorem inv_facts {x : Nat} (hx : x < 1540) : r32 AL x < 1540 ∧ r32 AI (r32 AL x) = x ∧
    r32 BE x < 1540 ∧ r32 BI (r32 BE x) = x ∧ r32 AI x < 1540 ∧ r32 BI x < 1540 := by
  have h := allN_spec invAB_ok x hx
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem al_get {x : Nat} (hx : x < 1540) : ap OJ.alpha x = r32 AL x :=
  ap_ofFn hx (by have := (inv_facts hx).1; omega)

theorem be_get {x : Nat} (hx : x < 1540) : ap OJ.beta x = r32 BE x :=
  ap_ofFn hx (by have := (inv_facts hx).2.2.1; omega)

theorem invA : invOK 1540 OJ.alpha (invT 1540 OJ.alpha) = true ∧
    ∀ y < 1540, ap (invT 1540 OJ.alpha) y = r32 AI y :=
  invT_get (f := r32 AL) (by norm_num) fun x hx =>
    ⟨al_get hx, (inv_facts hx).1, (inv_facts hx).2.1⟩

theorem invB : invOK 1540 OJ.beta (invT 1540 OJ.beta) = true ∧
    ∀ y < 1540, ap (invT 1540 OJ.beta) y = r32 BI y :=
  invT_get (f := r32 BE) (by norm_num) fun x hx =>
    ⟨be_get hx, (inv_facts hx).2.2.1, (inv_facts hx).2.2.2.1⟩

theorem size_OJ : OJ.pts.size = 1540 := by simp [vorbRec]

theorem GJ_eq (z : Int) (x : Nat) : GJ z x =
    if z = 1 then r32 AL x else if z = -1 then r32 AI x else if z = 2 then r32 BE x else r32 BI x := by
  rcases z with ((_ | _ | _ | k) | (_ | k)) <;> rfl

theorem gens_get (z : Int) {x : Nat} (hx : x < 1540) :
    ap (genTables OJ z) x = GJ z x ∧ GJ z x < 1540 := by
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

theorem inv_spec {j x : Nat} (hj : j < 5) (hx : x < 1540) : LJ (2 * j) x < 1540 ∧
    LJ (2 * j + 1) x < 1540 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 1540 10 = true := invL_ok
  unfold invK at h0
  have hj' : j < Nat.div 10 2 := by change j < 10 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem word_spec {j x : Nat} (hj : j < 5) (hx : x < 1540) :
    LJ (2 * j) x = List.foldr GJ x (chainWords ())[j]! :=
  Nat.eq_of_beq_eq_true (allN_spec (allN_spec wordsOK_ok j hj) x hx)

theorem letters_get : (chainLetters OJ).size = 10 ∧
    ∀ l < 10, ∀ x < 1540, ap (chainLetters OJ)[l]! x = LJ l x ∧ LJ l x < 1540 := by
  have hb := buildLetters_get (n := 1540) (gens := genTables OJ) (words := chainWords ()) (G := GJ)
    (H := fun j => LJ (2 * j + 1)) (by norm_num) (fun z x hx => gens_get z hx)
    (fun j hj x hx => by
      have hj' : j < 5 := hj
      rw [← word_spec hj' hx]
      exact (inv_spec hj' hx).2.2)
  have e : chainLetters OJ = buildLetters 1540 (genTables OJ) (chainWords ()) := rfl
  rw [e]
  refine ⟨hb.1, fun l hl x hx => ?_⟩
  have hs : (chainWords ()).size = 5 := rfl
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · have hj : j < 5 := by omega
    exact ⟨by rw [(hb.2 j (by rw [hs]; exact hj) x hx).1, word_spec hj hx], (inv_spec hj hx).1⟩
  · have hj : j < 5 := by omega
    exact ⟨(hb.2 j (by rw [hs]; exact hj) x hx).2, (inv_spec hj hx).2.1⟩

theorem tree_spec {i : Nat} (hi : i < 2) :
    tbfsHdK 1540 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 1540 (CNTJ i) (lvK LJ BJ 10 i).length LJ (lvAt LJ BJ 10 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  interval_cases i
  · have h : tree0 = true := tree0_ok
    unfold tree0 at h
    rw [bAnd_iff] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, allN_spec h2⟩
  · have h : tree1 = true := tree1_ok
    unfold tree1 at h
    rw [bAnd_iff] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, allN_spec h2⟩

theorem schSl_spec {i lo len : Nat}
    (h : schSlK LJ BJ 10 PTSJ POSJ PARJ LABJ CNTJ QB QL 2 i lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < CNTJ i → ∀ t < (lvK LJ BJ 10 i).length,
      schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 2 i (lvAt LJ BJ 10 i t) k = true := by
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

theorem cnt0 : CNTJ 0 = 1540 := rfl
theorem cnt1 : CNTJ 1 = 114 := rfl

theorem sch_spec : ∀ i < 2, ∀ k < CNTJ i, ∀ t < (lvK LJ BJ 10 i).length,
    schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 2 i (lvAt LJ BJ 10 i t) k = true := by
  intro i hi k hk
  interval_cases i
  · have hs : k / 55 < 28 := by rw [cnt0] at hk; omega
    exact schSl_spec (sch0All (k / 55) hs) k (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hk
  · exact schSl_spec sch1_ok k (Nat.zero_le _) (by rw [cnt1] at hk; omega) hk

theorem chain_hyp : ChainHyp 1540 10 2 (chainLetters OJ) chainBase chainQ chainQb LJ BJ QL QB CNTJ
    PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_get.1, fun l hl x hx => (letters_get.2 l hl x hx).1⟩
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem chain_eq : chainTrees 1540 (chainLetters OJ) chainBase =
      Array.ofFn (n := 2) (fun i => tbfsRec 1540 (CNTJ i.val) (PTSJ i.val) (POSJ i.val) (PARJ i.val)
        (LABJ i.val)) ∧
    ∀ chunks, chainOK 1540 (chainLetters OJ) chainBase chainQ chainQb
      (chainTrees 1540 (chainLetters OJ) chainBase) chunks = true :=
  pchainK_sound chain_hyp sch_spec term_ok

theorem trees0 : (chainTrees 1540 (chainLetters OJ) chainBase)[0]! =
    tbfsRec 1540 CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB := by
  rw [chain_eq.1, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  rfl

theorem sizes : (orbitSizes (chainTrees 1540 (chainLetters OJ) chainBase) == [1540, 114]) = true := by
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  rfl

theorem lv1_eq : levelLetters (chainLetters OJ) chainBase 1 = (lvK LJ BJ 10 1).toArray := by
  rw [← Array.toList_inj]
  simp only [levelLetters, Array.toList_filter, Array.toList_range, letters_get.1, lvK]
  apply List.filter_congr
  intro l hl
  have hl' : l < 10 := List.mem_range.1 hl
  have e : chainBase[0]! = 0 := rfl
  rw [e, (letters_get.2 l hl' 0 (by norm_num)).1, Bool.eq_iff_iff, CFSG.KLC.E8.allN_iff]
  simp [BJ]

theorem der_spec {i : Nat} (hi : i < 21) (hne : i ≠ r32 LBL 0) :
    derK 1540 21 LBL IM DS DOFF DLEN i = true := by
  have h := allN_spec der_ok i hi
  revert h
  cases hb : Nat.beq i (r32 LBL 0)
  · intro h
    exact h
  · exact absurd (Nat.eq_of_beq_eq_true hb) hne

theorem subLbl_ok : CFSG.KC.Enum.allN 21 (fun l => CFSG.KC.Enum.allN (SCNTJ l) (subLblK LBL SPTSJ l)) =
    true := by quickRfl

theorem lab0_lt {q : Nat} (hq : q < CT0.cnt) (h0 : 0 < q) : r32 CT0.LAB q < 10 := by
  have h := tree0_ok
  unfold tree0 at h
  rw [bAnd_iff] at h
  have hp := (CFSG.KS.TBfs.pt_spec (allN_spec h.2 q hq)).tree h0
  rw [hp.2.2.1]
  exact (CFSG.KS.PC.mem_lvK.1 (CFSG.KS.PC.lvAt_mem hp.2.1)).1

theorem prim_ok : primOK 1540 (chainLetters OJ) (levelLetters (chainLetters OJ) chainBase 1)
    (chainTrees 1540 (chainLetters OJ) chainBase)[0]!
    (primData 1540 (chainLetters OJ) (levelLetters (chainLetters OJ) chainBase 1)
      (chainTrees 1540 (chainLetters OJ) chainBase)[0]!) = true := by
  rw [trees0]
  exact prim_sound (k := 21) (B := BJ) (SPTS := SPTSJ) (SPOS := SPOSJ) (SPAR := SPARJ)
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

noncomputable abbrev PJ : List (List Nat) := colMat 7 [[1, 2, 7, 7, 2, 9, 10], [5, 5, 7, 1, 8, 0, 5],
  [2, 1, 5, 8, 7, 3, 2], [5, 4, 8, 6, 6, 10, 0], [2, 1, 9, 1, 10, 8, 9], [4, 4, 4, 0, 9, 2, 1],
  [5, 5, 4, 10, 8, 0, 5]]

noncomputable abbrev YJ : List (List Nat) := [[0, 6, 7, 6, 2, 7, 4], [10, 5, 9, 9, 3, 5, 10],
  [4, 4, 0, 0, 9, 2, 4], [8, 2, 6, 2, 10, 2, 7], [0, 10, 1, 4, 5, 3, 4], [9, 5, 6, 2, 1, 10, 2],
  [2, 2, 7, 0, 0, 8, 6]]

theorem pts_get {q : Nat} (hq : q < 1540) : OJ.pts[q]! = decV 7 (r32 PT q) := by
  rw [getElem!_pos _ q (by simpa [vorbRec] using hq)]
  simp [vorbRec]

theorem qVecs_eq : qVecs OJ = [decV 7 (r32 PT 0), decV 7 (r32 PT 1), decV 7 (r32 PT 489),
    decV 7 (r32 PT 1215), decV 7 (r32 PT 1116), decV 7 (r32 PT 269), decV 7 (r32 PT 759),
    decV 7 (r32 PT 2)] := by
  simp only [qVecs, chainQ, List.map_cons, List.map_nil]
  rw [pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num),
    pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num), pts_get (by norm_num)]

theorem qMat_eq : qMat OJ = PJ := by
  unfold qMat
  rw [qVecs_eq]
  decide +kernel

theorem q7_eq : (qVecs OJ).getD 7 [] = [3, 8, 2, 6, 7, 2, 1] := by
  rw [qVecs_eq]
  decide +kernel

theorem gauss_eq : gaussInv 11 7 PJ = YJ :=
  gaussInv_eq (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem j1_cert : j1Certificate 3 = true := by
  unfold j1Certificate
  rw [orb_eq.1]
  unfold actionChecks
  simp only [Bool.and_eq_true]
  rw [qMat_eq, q7_eq, gauss_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨orb_eq.2, by rw [size_OJ]; rfl⟩, ?_⟩, invA.1⟩, invB.1⟩, chain_eq.2 3⟩, sizes⟩,
    by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩, prim_ok⟩
  exact pmSep_of_proj (by norm_num)
    (fun i hi => by
      have h := pt_spec hi
      unfold vorbPtK at h
      simp only [strictB_eq, bAnd_iff] at h
      exact lt_of_lt_of_eq (Nat.blt_eq.mp h.1) (by decide))
    (fun i hi => by
      have h := pt_spec hi
      unfold vorbPtK at h
      simp only [strictB_eq, bAnd_iff] at h
      exact h.2.1)
    (allN_spec projSort_ok) 3

end CertificateChecks.KernelSpor.J1K

end
