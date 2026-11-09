module

public import Certificates.Kernel.Sporadic.McLK.Checks
public import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.LocalCompSPCode
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Perm.Basic
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.McLK.sch0All CertificateChecks.KernelSpor.McLK.sch0 5
#kon_join CertificateChecks.KernelSpor.McLK.mclGramSlAll CertificateChecks.KernelSpor.McLK.mclGramSl 18

namespace CertificateChecks.KernelSpor.McLK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.VO3 CFSG.KS.F3R
open CFSG.Sporadic.McL.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.VecOrbit.Native
  CFSG.F3.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

noncomputable abbrev OJ : VOrbit := v3Rec 275 PM AL BE PA LA

theorem matrix_ok : matrixChecks () = true := by
  unfold matrixChecks matA matB
  rw [McLSeedA.eq, McLSeedB.eq]
  simp only [canonM_eq, eqM_eq, mul_eq, powM_eq, rowsOf_ofList]
  decide +kernel

theorem tA : transpose 21 (matA ()) = ATM := by
  unfold matA ATM
  rw [McLSeedA.eq, rowsOf_ofList, transpose_eq]

theorem tB : transpose 21 (matB ()) = BTM := by
  unfold matB BTM
  rw [McLSeedB.eq, rowsOf_ofList, transpose_eq]

theorem orb_eq : orbitData () = OJ ∧ ∀ chunks,
    vecOrbitOK 21 (transpose 21 (matA ())) (transpose 21 (matB ())) OJ chunks = true := by
  have hs : ATM.size = 21 ∧ BTM.size = 21 := by simp [ATM, BTM, transposeK]
  have h := v3_sound (cap := 400) hs orbHd_ok (allN_spec orbPt_ok) (allN_spec orbSort_ok)
  unfold orbitData
  rw [tA, tB]
  exact h

theorem ap_ofFn {N : Nat} {f : Nat → Nat} {x : Nat} (hx : x < N) (hf : f x < 2 ^ 32) :
    ap (Array.ofFn (n := N) fun i => UInt32.ofNat (f i.val)) x = f x := by
  unfold ap
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hf

theorem inv_facts {x : Nat} (hx : x < 275) : r32 AL x < 275 ∧ r32 AL (r32 AL x) = x ∧
    r32 BE x < 275 ∧ r32 BI (r32 BE x) = x ∧ r32 BI x < 275 := by
  have h := allN_spec invAB_ok x hx
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem al_get {x : Nat} (hx : x < 275) : ap OJ.alpha x = r32 AL x :=
  ap_ofFn hx (by have := (inv_facts hx).1; omega)

theorem be_get {x : Nat} (hx : x < 275) : ap OJ.beta x = r32 BE x :=
  ap_ofFn hx (by have := (inv_facts hx).2.2.1; omega)

theorem invB : invOK 275 OJ.beta (invT 275 OJ.beta) = true ∧
    ∀ y < 275, ap (invT 275 OJ.beta) y = r32 BI y :=
  invT_get (f := r32 BE) (by norm_num) fun x hx =>
    ⟨be_get hx, (inv_facts hx).2.2.1, (inv_facts hx).2.2.2.1⟩

theorem size_OJ : OJ.pts.size = 275 := by simp [v3Rec]

theorem GJ_eq (z : Int) (x : Nat) : GJ z x =
    if z = 1 ∨ z = -1 then r32 AL x else if z = 2 then r32 BE x else r32 BI x := by
  rcases z with ((_ | _ | _ | k) | (_ | k)) <;> rfl

theorem gens_get (z : Int) {x : Nat} (hx : x < 275) :
    ap (genTables OJ z) x = GJ z x ∧ GJ z x < 275 := by
  have hf := inv_facts hx
  rw [GJ_eq]
  unfold genTables
  by_cases h1 : z = 1 ∨ z = -1
  · simp only [h1, ↓reduceIte]
    exact ⟨al_get hx, hf.1⟩
  by_cases h3 : z = 2
  · simp only [h3, ↓reduceIte]
    exact ⟨be_get hx, hf.2.2.1⟩
  · simp only [h1, h3, ↓reduceIte]
    exact ⟨invB.2 x hx, hf.2.2.2.2⟩

theorem inv_spec {j x : Nat} (hj : j < 9) (hx : x < 275) : LJ (2 * j) x < 275 ∧
    LJ (2 * j + 1) x < 275 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 275 18 = true := invL_ok
  unfold invK at h0
  have hj' : j < Nat.div 18 2 := by change j < 18 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem GNM_other {c : Nat} (y : Nat) (h1 : c ≠ 1) (h2 : c ≠ 2) (h4 : c ≠ 4) :
    GNM c y = r32 BI y := by
  have e1 : Nat.beq c 1 = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  have e2 : Nat.beq c 2 = false := Bool.eq_false_iff.2 fun h => h2 (Nat.eq_of_beq_eq_true h)
  have e4 : Nat.beq c 4 = false := Bool.eq_false_iff.2 fun h => h4 (Nat.eq_of_beq_eq_true h)
  unfold GNM
  rw [e2, e1, e4]

theorem GNM_code (z : Int) (y : Nat) : GNM (codeZ z) y = GJ z y := by
  rcases z with ((_ | _ | _ | k) | (_ | k))
  · rfl
  · rfl
  · rfl
  · change GNM (2 * (k + 3)) y = GJ (Int.ofNat (k + 3)) y
    rw [GJ_eq, GNM_other y (by omega) (by omega) (by omega)]
    have h1 : ¬(Int.ofNat (k + 3) = 1 ∨ Int.ofNat (k + 3) = -1) := by
      rw [Int.ofNat_eq_coe]
      omega
    have h2 : ¬Int.ofNat (k + 3) = 2 := by
      rw [Int.ofNat_eq_coe]
      omega
    rw [if_neg h1, if_neg h2]
  · rfl
  · change GNM (2 * (k + 1) + 1) y = GJ (Int.negSucc (k + 1)) y
    rw [GJ_eq, GNM_other y (by omega) (by omega) (by omega)]
    have h1 : ¬(Int.negSucc (k + 1) = 1 ∨ Int.negSucc (k + 1) = -1) := by
      rw [Int.negSucc_eq]
      omega
    have h2 : ¬Int.negSucc (k + 1) = 2 := by
      rw [Int.negSucc_eq]
      omega
    rw [if_neg h1, if_neg h2]

theorem foldWM_cons (x c : Nat) (w : List Nat) : foldWM x (c :: w) = GNM c (foldWM x w) := by
  change CFSG.KC.Loop.strictN (foldWM x w) (GNM c) = _
  cases foldWM x w <;> rfl

theorem foldr_code (x : Nat) (w : List Int) :
    List.foldr GJ x w = foldWM x (w.map codeZ) := by
  induction w with
  | nil => rfl
  | cons z w ih => rw [List.foldr_cons, List.map_cons, foldWM_cons, ← ih, GNM_code]

theorem map_get {α β : Type} [Inhabited α] {a : Array α} {f : α → β} {L : List β}
    (h : a.toList.map f = L) {j : Nat} (hj : j < L.length) (d : β) : f a[j]! = L.getD j d := by
  have hl : j < a.size := by
    rw [← h] at hj
    simpa using hj
  rw [getElem!_pos a j hl, List.getD_eq_getElem?_getD, ← h, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hl)]
  simp

theorem wl_eq {j : Nat} (hj : j < 9) : ((chainWords ())[j]!).map codeZ = WL j := by
  rw [map_get words_all (by simpa using hj) []]
  interval_cases j <;> rfl

theorem gram_get {s : Nat} (hs : s < 177) : mclGramS s = true := by
  have hs' : s / 10 < 18 := by omega
  have h := mclGramSlAll (s / 10) hs'
  unfold mclGramSl at h
  have h' := allN_spec h (s % 10) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h'
  have e : Nat.add (Nat.mul (s / 10) 10) (s % 10) = s := by
    change s / 10 * 10 + s % 10 = s
    omega
  rw [e, Eq.mpr Nat.blt_eq hs] at h'
  exact h'

theorem gram_term {s : Nat} (hs : s < 5) {x : Nat} (hx : x < 275) : SymTJ s x = GNM s x := by
  have h := gram_get (s := s) (by omega)
  unfold mclGramS at h
  rw [Eq.mpr Nat.blt_eq hs] at h
  dsimp only at h
  exact Nat.eq_of_beq_eq_true (allN_spec h x hx)

theorem gram_rule {s : Nat} (hs : s < 177) (h5 : 5 ≤ s) : r32 MclGL s < s ∧ r32 MclGR s < s ∧
    ∀ x < 275, SymTJ s x = SymTJ (r32 MclGL s) (SymTJ (r32 MclGR s) x) := by
  have h := gram_get hs
  unfold mclGramS at h
  have e : Nat.blt s 5 = false := Bool.eq_false_iff.2 fun h' => by
    rw [Nat.blt_eq] at h'
    omega
  rw [e] at h
  dsimp only at h
  rw [strictB_eq, strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, h.2.1, fun x hx => Nat.eq_of_beq_eq_true (allN_spec h.2.2 x hx)⟩

theorem GNM_lt {s : Nat} (hs : s < 5) {x : Nat} (hx : x < 275) : GNM s x < 275 := by
  have hf := inv_facts hx
  interval_cases s
  · exact hf.2.2.2.2
  · exact hf.1
  · exact hf.1
  · exact hf.2.2.2.2
  · exact hf.2.2.1

theorem SymTJ_lt : ∀ s < 177, ∀ x < 275, SymTJ s x < 275 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs x hx
    rcases Nat.lt_or_ge s 5 with h5 | h5
    · rw [gram_term h5 hx]
      exact GNM_lt h5 hx
    · obtain ⟨hl, hr, he⟩ := gram_rule hs h5
      rw [he x hx]
      exact ih _ hl (by omega) _ (ih _ hr (by omega) x hx)

theorem expSymK_spec : ∀ k s, s ≤ k → s < 177 → ∀ acc x, foldWM x acc < 275 →
    foldWM x (expSymK k s acc) = SymTJ s (foldWM x acc) := by
  intro k
  induction k with
  | zero =>
    intro s hs _ acc x hy
    obtain rfl : s = 0 := by omega
    change foldWM x (0 :: acc) = _
    rw [foldWM_cons, gram_term (by norm_num) hy]
  | succ k ih =>
    intro s hs hs' acc x hy
    rcases Nat.lt_or_ge s 5 with h5 | h5
    · have e : expSymK (k + 1) s acc = s :: acc := by
        change Bool.rec (motive := fun _ => List Nat) _ (s :: acc) (Nat.blt s 5) = _
        rw [Eq.mpr Nat.blt_eq h5]
      rw [e, foldWM_cons, gram_term h5 hy]
    · obtain ⟨hl, hr, he⟩ := gram_rule hs' h5
      have e : expSymK (k + 1) s acc = expSymK k (r32 MclGL s) (expSymK k (r32 MclGR s) acc) := by
        change Bool.rec (motive := fun _ => List Nat) _ (s :: acc) (Nat.blt s 5) = _
        have e5 : Nat.blt s 5 = false := Bool.eq_false_iff.2 fun h' => by
          rw [Nat.blt_eq] at h'
          omega
        rw [e5]
        rfl
      have hr' := ih (r32 MclGR s) (by omega) (by omega) acc x hy
      have hy' : foldWM x (expSymK k (r32 MclGR s) acc) < 275 := by
        rw [hr']
        exact SymTJ_lt _ (by omega) _ hy
      rw [e, ih (r32 MclGL s) (by omega) (by omega) _ x hy', hr', ← he _ hy]

theorem word_spec {j x : Nat} (hj : j < 9) (hx : x < 275) :
    LJ (2 * j) x = List.foldr GJ x (chainWords ())[j]! := by
  rw [foldr_code, wl_eq hj]
  have h := allN_spec mclLettersW_ok j hj
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  have h' : LJ (2 * j) x = SymTJ (r32 MclRO j) x := Nat.eq_of_beq_eq_true (allN_spec h.2 x hx)
  rw [h']
  exact (expSymK_spec _ _ (Nat.le_refl _) h.1 [] x hx).symm

theorem letters_get : (chainLetters OJ).size = 18 ∧
    ∀ l < 18, ∀ x < 275, ap (chainLetters OJ)[l]! x = LJ l x ∧ LJ l x < 275 := by
  have hb := buildLetters_get (n := 275) (gens := genTables OJ) (words := chainWords ()) (G := GJ)
    (H := fun j => LJ (2 * j + 1)) (by norm_num) (fun z x hx => gens_get z hx)
    (fun j hj x hx => by
      have hj' : j < 9 := hj
      rw [← word_spec hj' hx]
      exact (inv_spec hj' hx).2.2)
  have e : chainLetters OJ = buildLetters 275 (genTables OJ) (chainWords ()) := rfl
  rw [e]
  refine ⟨hb.1, fun l hl x hx => ?_⟩
  have hs : (chainWords ()).size = 9 := by decide +kernel
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · have hj : j < 9 := by omega
    exact ⟨by rw [(hb.2 j (by rw [hs]; exact hj) x hx).1, word_spec hj hx], (inv_spec hj hx).1⟩
  · have hj : j < 9 := by omega
    exact ⟨(hb.2 j (by rw [hs]; exact hj) x hx).2, (inv_spec hj hx).2.1⟩

theorem tree_spec {i : Nat} (hi : i < 6) :
    tbfsHdK 275 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 275 (CNTJ i) (lvK LJ BJ 18 i).length LJ (lvAt LJ BJ 18 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  have h := allN_spec tree_ok i hi
  unfold tree at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, allN_spec h2⟩

theorem schSl_spec {i lo len : Nat}
    (h : schSlK LJ BJ 18 PTSJ POSJ PARJ LABJ CNTJ QB QL 6 i lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < CNTJ i → ∀ t < (lvK LJ BJ 18 i).length,
      schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 6 i (lvAt LJ BJ 18 i t) k = true := by
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

theorem cnt0 : CNTJ 0 = 275 := rfl

theorem sch_spec : ∀ i < 6, ∀ k < CNTJ i, ∀ t < (lvK LJ BJ 18 i).length,
    schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 6 i (lvAt LJ BJ 18 i t) k = true := by
  intro i hi k hk
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have hs : k / 55 < 5 := by rw [cnt0] at hk; omega
    exact schSl_spec (sch0All (k / 55) hs) k (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hk
  · obtain ⟨j, rfl⟩ : ∃ j, i = Nat.succ j := ⟨i - 1, by omega⟩
    have h := allN_spec schR_ok j (by omega)
    unfold schR at h
    exact schSl_spec h k (Nat.zero_le _) (by omega) hk

theorem chain_hyp : ChainHyp 275 18 6 (chainLetters OJ) chainBase chainQ (chainQb ()) LJ BJ QL QB
    CNTJ PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_get.1, fun l hl x hx => (letters_get.2 l hl x hx).1⟩
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem chain_eq : chainTrees 275 (chainLetters OJ) chainBase =
      Array.ofFn (n := 6) (fun i => tbfsRec 275 (CNTJ i.val) (PTSJ i.val) (POSJ i.val) (PARJ i.val)
        (LABJ i.val)) ∧
    ∀ chunks, chainOK 275 (chainLetters OJ) chainBase chainQ (chainQb ())
      (chainTrees 275 (chainLetters OJ) chainBase) chunks = true :=
  pchainK_sound chain_hyp sch_spec term_ok

theorem sizes : (orbitSizes (chainTrees 275 (chainLetters OJ) chainBase) ==
    [275, 162, 56, 30, 4, 3]) = true := by
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  rfl

theorem lv1_eq : levelLetters (chainLetters OJ) chainBase 1 = (lvK LJ BJ 18 1).toArray := by
  rw [← Array.toList_inj]
  simp only [levelLetters, Array.toList_filter, Array.toList_range, letters_get.1, lvK]
  apply List.filter_congr
  intro l hl
  have hl' : l < 18 := List.mem_range.1 hl
  have e : chainBase[0]! = 0 := rfl
  rw [e, (letters_get.2 l hl' 0 (by norm_num)).1, Bool.eq_iff_iff, CFSG.KLC.E8.allN_iff]
  simp [BJ]

theorem t2_eq : treeBFS 275 (subRoot ()) (chainLetters OJ) (levelLetters (chainLetters OJ) chainBase 1) =
      tbfsRec 275 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB ∧
    treeOK 275 (subRoot ()) (tbfsRec 275 T2.cnt T2.PTS T2.POS T2.PAR T2.LAB) (chainLetters OJ)
      (levelLetters (chainLetters OJ) chainBase 1) = true := by
  have h : t2 = true := t2_ok
  unfold t2 at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [lv1_eq]
  refine tbfsK_sound (L := LJ) (LV := lvAt LJ BJ 18 1) ⟨by simp, fun t ht => ?_⟩ h1 (allN_spec h2)
  have ht' : t < (lvK LJ BJ 18 1).length := by simpa using ht
  have hm := List.getElem_mem ht'
  have hlt : (lvK LJ BJ 18 1)[t] < 18 := by
    unfold lvK at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have e : (lvK LJ BJ 18 1).toArray[t]! = lvAt LJ BJ 18 1 t := by
    rw [getElem!_pos _ t (by simpa using ht')]
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e]
  have e2 : lvAt LJ BJ 18 1 t = (lvK LJ BJ 18 1)[t] := by
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e2]
  exact ⟨rfl, by rw [letters_get.1]; exact hlt, fun x hx => (letters_get.2 _ hlt x hx).1⟩

theorem pts_get {q : Nat} (hq : q < 275) : OJ.pts[q]! = decV3 (PM q) := by
  rw [getElem!_pos _ q (by simpa [v3Rec] using hq)]
  simp [v3Rec]

theorem basis_ok : basisOK 21 (chainQ.map fun r => OJ.pts[r]!) basisTinv = true := by
  unfold basisOK
  simp only [chainQ, List.map_toArray, List.map_cons, List.map_nil]
  simp (disch := decide) only [pts_get]
  simp only [wfM_eq, eqM_eq, mul_eq]
  decide +kernel

theorem mcl_cert : mclCertificate 3 = true := by
  unfold mclCertificate
  simp only [Bool.and_eq_true]
  rw [orb_eq.1]
  refine ⟨matrix_ok, orb_eq.2 3, ?_⟩
  unfold actionChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel⟩, ?_⟩, invB.1⟩,
    by decide +kernel⟩, ?_⟩, basis_ok⟩, chain_eq.2 3⟩, sizes⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold CFSG.Sporadic.Th.Native.invoOK allIn
    rw [all_eq]
    decide +kernel
  · rw [← Array.all_toList]
    decide +kernel
  · rw [t2_eq.1]
    exact t2_eq.2
  · rw [t2_eq.1]
    rfl
  · rw [chain_eq.1, t2_eq.1]
    unfold allIn
    rw [all_eq]
    decide +kernel

end CertificateChecks.KernelSpor.McLK

end
