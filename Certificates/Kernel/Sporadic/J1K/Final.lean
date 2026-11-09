module

public import Certificates.Kernel.Sporadic.J1K.Checks
public import Certificates.Kernel.Sporadic.J1K.Sep
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

#kon_join CertificateChecks.KernelSpor.J1K.schG0All CertificateChecks.KernelSpor.J1K.schG0 5

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

theorem gt1 : genTables OJ 1 = OJ.alpha := if_pos rfl

theorem gt2 : genTables OJ (-1) = invT 1540 OJ.alpha := by
  rw [← size_OJ]
  exact (if_neg (by decide : ¬((-1 : Int) = 1))).trans (if_pos rfl)

theorem gt3 : genTables OJ 2 = OJ.beta :=
  (if_neg (by decide : ¬((2 : Int) = 1))).trans
    ((if_neg (by decide : ¬((2 : Int) = -1))).trans (if_pos rfl))

theorem gt4 {z : Int} (h1 : ¬z = 1) (h2 : ¬z = -1) (h3 : ¬z = 2) :
    genTables OJ z = invT 1540 OJ.beta := by
  rw [← size_OJ]
  exact (if_neg h1).trans ((if_neg h2).trans (if_neg h3))

theorem gj4 {z : Int} {x : Nat} (h1 : ¬z = 1) (h2 : ¬z = -1) (h3 : ¬z = 2) :
    GJ z x = r32 BI x := by
  rw [GJ_eq, if_neg h1, if_neg h2, if_neg h3]

theorem gens_get1 {x : Nat} (hx : x < 1540) :
    ap (genTables OJ 1) x = GJ 1 x ∧ GJ 1 x < 1540 := by
  rw [gt1]
  exact ⟨al_get hx, (inv_facts hx).1⟩

theorem gens_get2 {x : Nat} (hx : x < 1540) :
    ap (genTables OJ (-1)) x = GJ (-1) x ∧ GJ (-1) x < 1540 := by
  rw [gt2]
  exact ⟨invA.2 x hx, (inv_facts hx).2.2.2.2.1⟩

theorem gens_get3 {x : Nat} (hx : x < 1540) :
    ap (genTables OJ 2) x = GJ 2 x ∧ GJ 2 x < 1540 := by
  rw [gt3]
  exact ⟨be_get hx, (inv_facts hx).2.2.1⟩

theorem gens_get4 {z : Int} {x : Nat} (hx : x < 1540) (h1 : ¬z = 1) (h2 : ¬z = -1) (h3 : ¬z = 2) :
    ap (genTables OJ z) x = GJ z x ∧ GJ z x < 1540 := by
  rw [gt4 h1 h2 h3, gj4 h1 h2 h3]
  exact ⟨invB.2 x hx, (inv_facts hx).2.2.2.2.2⟩

theorem gens_get (z : Int) {x : Nat} (hx : x < 1540) :
    ap (genTables OJ z) x = GJ z x ∧ GJ z x < 1540 := by
  by_cases h1 : z = 1
  · subst h1
    exact gens_get1 hx
  by_cases h2 : z = -1
  · subst h2
    exact gens_get2 hx
  by_cases h3 : z = 2
  · subst h3
    exact gens_get3 hx
  · exact gens_get4 hx h1 h2 h3

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

theorem sch_spec : ∀ i < 2, 0 < i → ∀ k < CNTJ i, ∀ t < (lvK LJ BJ 10 i).length,
    schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 2 i (lvAt LJ BJ 10 i t) k = true := by
  intro i hi hi0 k hk
  have e : i = 1 := by omega
  subst e
  exact schSl_spec sch1_ok k (Nat.zero_le _) (by rw [cnt1] at hk; omega) hk

theorem sch0_spec : ∀ s ∈ [0, 2], ∀ k < CNTJ 0,
    schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 2 0 s k = true := by
  intro s hs k hk
  rw [cnt0] at hk
  have hs5 : k / 308 < 5 := by omega
  have h := allN_spec (schG0All (k / 308) hs5) (k % 308) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h
  have e : Nat.add (Nat.mul (k / 308) 308) (k % 308) = k := by
    change k / 308 * 308 + k % 308 = k
    omega
  rw [e, bAnd_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h.1
  · exact h.2

theorem chain_hyp : ChainHyp 1540 10 2 (chainLetters OJ) chainBase chainQ chainQb LJ BJ QL QB CNTJ
    PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_get.1, fun l hl x hx => (letters_get.2 l hl x hx).1⟩
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem lj0 {x : Nat} (hx : x < 1540) : LJ 0 x = r32 AL x := by
  have h := word_spec (j := 0) (by norm_num) hx
  rw [h]
  change GJ 1 x = r32 AL x
  rw [GJ_eq]
  simp

theorem lj2 {x : Nat} (hx : x < 1540) : LJ 2 x = r32 BE x := by
  have h := word_spec (j := 1) (by norm_num) hx
  rw [h]
  change GJ 2 x = r32 BE x
  rw [GJ_eq]
  simp

theorem lj1 {y : Nat} (hy : y < 1540) : LJ 1 y = r32 AI y := by
  have hs := pair_inv (f := fun x => r32 AL x) (g := fun x => r32 AI x)
    (fun x hx => (inv_facts hx).1) (fun x hx => (inv_facts hx).2.1) y hy
  have ha := (inv_facts hy).2.2.2.2.1
  have h := (inv_spec (j := 0) (by norm_num) ha).2.2
  rw [lj0 ha] at h
  calc LJ 1 y = LJ 1 (r32 AL (r32 AI y)) := by rw [hs]
    _ = r32 AI y := h

theorem lj3 {y : Nat} (hy : y < 1540) : LJ 3 y = r32 BI y := by
  have hs := pair_inv (f := fun x => r32 BE x) (g := fun x => r32 BI x)
    (fun x hx => (inv_facts hx).2.2.1) (fun x hx => (inv_facts hx).2.2.2.1) y hy
  have hb := (inv_facts hy).2.2.2.2.2
  have h := (inv_spec (j := 1) (by norm_num) hb).2.2
  rw [lj2 hb] at h
  calc LJ 3 y = LJ 3 (r32 BE (r32 BI y)) := by rw [hs]
    _ = r32 BI y := h

noncomputable abbrev genSet : Set (Equiv.Perm (Fin 1540)) :=
  {g | ∃ s ∈ [0, 2], sig 1540 (chainLetters OJ) s = g}

noncomputable def genP (z : Int) : Equiv.Perm (Fin 1540) :=
  if z = 1 then sig 1540 (chainLetters OJ) 0 else if z = -1 then (sig 1540 (chainLetters OJ) 0)⁻¹
    else if z = 2 then sig 1540 (chainLetters OJ) 2 else (sig 1540 (chainLetters OJ) 2)⁻¹

theorem genP_mem (z : Int) : genP z ∈ Subgroup.closure genSet := by
  have h0 : sig 1540 (chainLetters OJ) 0 ∈ Subgroup.closure genSet :=
    Subgroup.subset_closure ⟨0, by simp, rfl⟩
  have h2 : sig 1540 (chainLetters OJ) 2 ∈ Subgroup.closure genSet :=
    Subgroup.subset_closure ⟨2, by simp, rfl⟩
  unfold genP
  split_ifs
  · exact h0
  · exact Subgroup.inv_mem _ h0
  · exact h2
  · exact Subgroup.inv_mem _ h2

theorem genP_act (z : Int) {y : Nat} (hy : y < 1540) : actN (genP z) y = GJ z y := by
  rw [GJ_eq]
  unfold genP
  split_ifs
  · rw [actN_sig chain_hyp (by norm_num) hy, lj0 hy]
  · rw [actN_sig_inv chain_hyp (by norm_num) hy]
    exact lj1 hy
  · rw [actN_sig chain_hyp (by norm_num) hy, lj2 hy]
  · rw [actN_sig_inv chain_hyp (by norm_num) hy]
    exact lj3 hy

theorem word_act (w : List Int) {x : Nat} (hx : x < 1540) :
    actN (w.foldr (fun z g => genP z * g) 1) x = List.foldr GJ x w := by
  induction w with
  | nil => exact actN_one x
  | cons z w ih =>
    rw [List.foldr_cons, List.foldr_cons, actN_mul, ih,
      genP_act z (by rw [← ih]; exact actN_lt _ hx)]

theorem word_mem (w : List Int) :
    w.foldr (fun z g => genP z * g) 1 ∈ Subgroup.closure genSet := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons z w ih => exact Subgroup.mul_mem _ (genP_mem z) ih

theorem grp_le : grp 1540 10 (chainLetters OJ) ≤ Subgroup.closure genSet := by
  rw [Subgroup.closure_le]
  rintro _ ⟨⟨l, hl⟩, rfl⟩
  change sig 1540 (chainLetters OJ) l ∈ _
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · have hj : j < 5 := by omega
    have e : sig 1540 (chainLetters OJ) (2 * j) =
        ((chainWords ())[j]!).foldr (fun z g => genP z * g) 1 := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      rw [← actN_fin, ← actN_fin, actN_sig chain_hyp hl x.isLt, word_act _ x.isLt,
        word_spec hj x.isLt]
    rw [e]
    exact word_mem _
  · have hj : j < 5 := by omega
    have e : sig 1540 (chainLetters OJ) (2 * j + 1) = (sig 1540 (chainLetters OJ) (2 * j))⁻¹ := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      have hi : CFSG.Perm.Native.invL (2 * j) = 2 * j + 1 := by
        unfold CFSG.Perm.Native.invL
        rw [ite_eq_left (by omega)]
      rw [← actN_fin, ← actN_fin, actN_sig chain_hyp hl x.isLt,
        actN_sig_inv chain_hyp (by omega) x.isLt, hi]
    rw [e]
    refine Subgroup.inv_mem _ ?_
    have e2 : sig 1540 (chainLetters OJ) (2 * j) =
        ((chainWords ())[j]!).foldr (fun z g => genP z * g) 1 := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      rw [← actN_fin, ← actN_fin, actN_sig chain_hyp (by omega) x.isLt, word_act _ x.isLt,
        word_spec hj x.isLt]
    rw [e2]
    exact word_mem _

theorem chain_eq : chainTrees 1540 (chainLetters OJ) chainBase =
      Array.ofFn (n := 2) (fun i => tbfsRec 1540 (CNTJ i.val) (PTSJ i.val) (POSJ i.val) (PARJ i.val)
        (LABJ i.val)) ∧
    ∀ chunks, chainOK 1540 (chainLetters OJ) chainBase chainQ chainQb
      (chainTrees 1540 (chainLetters OJ) chainBase) chunks = true := by
  refine pchainK_gens_sound chain_hyp (by norm_num) [0, 2] (by simp) grp_le
    (fun g hg => sep_J1 (fun x hx => ?_) g (grp_le hg)) sch0_spec sch_spec term_ok
  obtain ⟨s, hs, rfl⟩ := hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact Or.inl fun i hi => by rw [actN_sig chain_hyp (by norm_num) hi, lj0 hi]
  · exact Or.inr fun i hi => by rw [actN_sig chain_hyp (by norm_num) hi, lj2 hi]

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
