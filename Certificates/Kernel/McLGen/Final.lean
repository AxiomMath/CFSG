module

public import Certificates.Data.GH74.McLGen45
public import Certificates.Kernel.McLGen.Checks
public import Certificates.Kernel.ThFamC.K19766
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Certificates.Kernel.Spor.TBfsSound
public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.Misc.XiBits
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.LinesPerp
public import CFSG.Certificates.Kernel.Misc.O73Defs
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLGen

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.SC CFSG.KS.VO
open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.LevelChain.Native CFSG.Sporadic.PairGen CFSG.Sporadic.McL.Gen45

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem notK_true {b : Bool} (h : notK b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem gen_facts {x : Nat} (hx : x < 275) :
    r32 AT x < 275 ∧ r32 AI (r32 AT x) = x ∧ r32 AI x < 275 ∧ r32 BT x < 275 ∧
      r32 BI (r32 BT x) = x ∧ r32 BI x < 275 ∧
      r32 AT x = pg 9 (mask 9) (CertificateChecks.KernelCensus.McLS.F 0) x ∧
      r32 BT x = pg 9 (mask 9) (CertificateChecks.KernelCensus.McLS.F 1) x := by
  have h := allN_spec gen_ok x hx
  unfold genOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨blt_true h1, beq_true h2, blt_true h3, blt_true h4, beq_true h5, blt_true h6,
    beq_true h7, beq_true h8⟩

theorem tbl_get {k : Nat} (hk : k < 2) {x : Nat} (hx : x < 275) :
    ap (mclGenTbl k) x = pg 9 (mask 9) (CertificateChecks.KernelCensus.McLS.F k) x := by
  have hf := gen_facts hx
  have hb : pg 9 (mask 9) (CertificateChecks.KernelCensus.McLS.F k) x < 2 ^ 32 := by
    interval_cases k
    · rw [← hf.2.2.2.2.2.2.1]; omega
    · rw [← hf.2.2.2.2.2.2.2]; omega
  unfold ap mclGenTbl
  rw [CertificateChecks.KernelThFamC.K19766.strong_eq k (by omega)]
  rw [getElem!_pos _ x (by simp [CFSG.KS.Raw.unpack]; omega), Array.getElem_map,
    ← getElem!_pos _ x (by simp [CFSG.KS.Raw.unpack]; omega), CFSG.KC.Child3.unpack_get' hx,
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt hb]

theorem invA : invOK 275 (mclGenTbl 0) (invT 275 (mclGenTbl 0)) = true ∧
    ∀ y < 275, ap (invT 275 (mclGenTbl 0)) y = r32 AI y :=
  invT_get (f := r32 AT) (by norm_num) fun x hx =>
    ⟨(tbl_get (by norm_num) hx).trans (gen_facts hx).2.2.2.2.2.2.1.symm, (gen_facts hx).1,
      (gen_facts hx).2.1⟩

theorem invB : invOK 275 (mclGenTbl 1) (invT 275 (mclGenTbl 1)) = true ∧
    ∀ y < 275, ap (invT 275 (mclGenTbl 1)) y = r32 BI y :=
  invT_get (f := r32 BT) (by norm_num) fun x hx =>
    ⟨(tbl_get (by norm_num) hx).trans (gen_facts hx).2.2.2.2.2.2.2.symm, (gen_facts hx).2.2.2.1,
      (gen_facts hx).2.2.2.2.1⟩

theorem GJ_other {z : Int} (h1 : z ≠ 1) (h2 : z ≠ -1) (h3 : z ≠ 2) (x : Nat) :
    GJ z x = r32 BI x := by
  unfold GJ
  rcases z with k | k
  · have e1 : Nat.beq k 1 = false := by
      cases hq : Nat.beq k 1
      · rfl
      · exact absurd (by rw [beq_true hq]; rfl) h1
    have e2 : Nat.beq k 2 = false := by
      cases hq : Nat.beq k 2
      · rfl
      · exact absurd (by rw [beq_true hq]; rfl) h3
    simp only [e1, e2]
  · have e0 : Nat.beq k 0 = false := by
      cases hq : Nat.beq k 0
      · rfl
      · exact absurd (by rw [beq_true hq]; rfl) h2
    simp only [e0]

theorem gens_get (z : Int) {x : Nat} (hx : x < 275) :
    ap (mclLetters (mclGenTbl 0) (mclGenTbl 1) z) x = GJ z x ∧ GJ z x < 275 := by
  have hf := gen_facts hx
  unfold mclLetters
  by_cases h1 : z = 1
  · subst h1
    rw [if_pos rfl]
    exact ⟨(tbl_get (by norm_num) hx).trans hf.2.2.2.2.2.2.1.symm, hf.1⟩
  by_cases h2 : z = -1
  · subst h2
    rw [if_neg (show (-1 : Int) ≠ 1 by decide), if_pos rfl]
    exact ⟨invA.2 x hx, hf.2.2.1⟩
  by_cases h3 : z = 2
  · subst h3
    rw [if_neg (show (2 : Int) ≠ 1 by decide), if_neg (show (2 : Int) ≠ -1 by decide),
      if_pos rfl]
    exact ⟨(tbl_get (by norm_num) hx).trans hf.2.2.2.2.2.2.2.symm, hf.2.2.2.1⟩
  rw [if_neg h1, if_neg h2, if_neg h3, GJ_other h1 h2 h3]
  exact ⟨invB.2 x hx, hf.2.2.2.2.2.1⟩

theorem slp_ok : slpOK mclGenWords = true := by
  simp only [slpOK, CFSG.KC.Misc.Xi.allIn_iff']
  decide +kernel

theorem words_size : mclGenWords.size = 18 := rfl

theorem inv_spec {j x : Nat} (hj : j < 18) (hx : x < 275) : LJ (2 * j) x < 275 ∧
    LJ (2 * j + 1) x < 275 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 275 36 = true := inv_ok
  unfold invK at h0
  have hj' : j < Nat.div 36 2 := by change j < 36 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem letters_get : (slpLetters 275 (mclLetters (mclGenTbl 0) (mclGenTbl 1)) mclGenWords).size =
      36 ∧ ∀ l < 36, ∀ x < 275,
        ap (slpLetters 275 (mclLetters (mclGenTbl 0) (mclGenTbl 1)) mclGenWords)[l]! x = LJ l x ∧
          LJ l x < 275 := by
  have hok : ∀ j < mclGenWords.size, ∀ z ∈ mclGenWords[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
    have h := slp_ok
    unfold slpOK at h
    rw [TBfs.allIn_iff] at h
    intro j hj z hz
    have h' := List.all_eq_true.1 (h j hj) z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h'
    exact h'
  have hw : ∀ j < mclGenWords.size, ∀ x < 275, LJ (2 * j) x = List.foldr (slpG GJ LJ) x mclGenWords[j]! := by
    intro j hj x hx
    rw [words_size] at hj
    exact beq_true (allN_spec (allN_spec words_ok j hj) x hx)
  have hinv : ∀ j < mclGenWords.size, ∀ x < 275, LJ (2 * j) x < 275 ∧ LJ (2 * j + 1) x < 275 ∧
      LJ (2 * j + 1) (LJ (2 * j) x) = x := by
    intro j hj x hx
    rw [words_size] at hj
    exact inv_spec hj hx
  have hb := slpLetters_get (n := 275) (gens := mclLetters (mclGenTbl 0) (mclGenTbl 1))
    (words := mclGenWords) (G := GJ) (L := LJ) (by norm_num) (fun z x hx => gens_get z hx) hok hw hinv
  rw [words_size] at hb
  refine ⟨hb.1, fun l hl x hx => ⟨hb.2 l hl x hx, ?_⟩⟩
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · exact (inv_spec (by omega) hx).1
  · exact (inv_spec (by omega) hx).2.1

theorem invOK_of {P R : Table} (h : ∀ i < 275, ap R (ap P i) = i) : invOK 275 P R = true := by
  unfold invOK
  rw [TBfs.allIn_iff]
  intro i hi
  simp [h i hi]

theorem invoOK_of {P : Table} (h : ∀ i < 275, ap P (ap P i) = i) :
    CFSG.Sporadic.Th.Native.invoOK 275 P = true := by
  unfold CFSG.Sporadic.Th.Native.invoOK
  rw [TBfs.allIn_iff]
  intro i hi
  simp [h i hi]

theorem commTab_of {P Q : Table} (h : ∀ i < 275, ap P (ap Q i) = ap Q (ap P i)) :
    commTab 275 P Q = true := by
  unfold commTab compT
  have e : (Array.ofFn (n := 275) fun i => P[(Q[i.val]!).toNat]!) =
      Array.ofFn (n := 275) fun i => Q[(P[i.val]!).toNat]! := by
    congr 1
    funext i
    exact UInt32.toNat_inj.1 (h i.val i.isLt)
  rw [e]
  exact beq_self_eq_true _

theorem st_get {i : Nat} (hi : i < 6) : (#[8, 10, 12, 14, 17, 18] : Array Nat)[i]! = STJ i := by
  interval_cases i <;> rfl

theorem bs_get {i : Nat} (hi : i < 5) : (#[0, 3, 4, 5, 1] : Array Nat)[i]! = BSJ i := by
  interval_cases i <;> rfl

theorem st_lt {i : Nat} (hi : i < 5) : STJ i < STJ (i + 1) ∧ STJ (i + 1) ≤ 18 := by
  interval_cases i <;> decide

theorem tree_spec {i : Nat} (hi : i < 5) :
    let L := slpLetters 275 (mclLetters (mclGenTbl 0) (mclGenTbl 1)) mclGenWords
    treeBFS 275 (BSJ i) L (levelLv #[8, 10, 12, 14, 17, 18] i) =
        tbfsRec 275 (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) ∧
      treeOK 275 (BSJ i) (tbfsRec 275 (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i)) L
        (levelLv #[8, 10, 12, 14, 17, 18] i) = true := by
  intro L
  have h := allN_spec tree_ok i hi
  unfold tree at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hs := st_lt hi
  have hlv : levelLv #[8, 10, 12, 14, 17, 18] i = Array.ofFn (n := RJ i) fun t => LVJ i t.val := by
    interval_cases i <;> rfl
  rw [hlv]
  refine tbfsK_sound (r := RJ i) (L := LJ) (LV := LVJ i) ⟨by simp, fun t ht => ?_⟩ h1 (allN_spec h2)
  have hlt : LVJ i t < 36 := by
    have : t < 2 * (STJ (i + 1) - STJ i) := ht
    change 2 * STJ i + t < 36
    omega
  refine ⟨?_, by rw [letters_get.1]; exact hlt, fun x hx => (letters_get.2 _ hlt x hx).1⟩
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_ofFn]

theorem pairOK_spec : (∀ x < 275, LJ 0 (LJ 0 x) = x ∧ LJ 6 (LJ 6 x) = x ∧
      LJ 0 (LJ 6 x) = LJ 6 (LJ 0 x) ∧ LJ 0 (LJ 16 x) = LJ 16 (LJ 0 x) ∧
      LJ 6 (LJ 18 x) = LJ 18 (LJ 6 x)) ∧ LJ 0 1 ≠ 1 ∧ LJ 6 0 ≠ 0 ∧ LJ 0 0 ≠ LJ 6 0 := by
  have h := pair_ok
  unfold pairOK at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
  · have h' := allN_spec h1 x hx
    simp only [bAnd_iff] at h'
    obtain ⟨a, b, c, d, e⟩ := h'
    exact ⟨beq_true a, beq_true b, beq_true c, beq_true d, beq_true e⟩
  · intro e
    have := notK_true h2
    rw [e] at this
    exact absurd this (by decide)
  · intro e
    have := notK_true h3
    rw [e] at this
    exact absurd this (by decide)
  · intro e
    have := notK_true h4
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem fix_spec (i : Nat) (hi : i < 4) (j : Nat) (h3 : STJ (i + 1) ≤ j) (h4 : j < STJ (i + 1 + 1)) :
    LJ (2 * j) (BSJ i) = BSJ i := by
  have hd : j - STJ (i + 1) < Nat.sub (STJ (Nat.succ (Nat.succ i))) (STJ (Nat.succ i)) := by
    change j - STJ (i + 1) < STJ (i + 1 + 1) - STJ (i + 1)
    omega
  have h := beq_true (allN_spec (allN_spec fix_ok i hi) (j - STJ (i + 1)) hd)
  have e : Nat.add (STJ (Nat.succ i)) (j - STJ (i + 1)) = j := by
    change STJ (i + 1) + (j - STJ (i + 1)) = j
    omega
  rw [e] at h
  exact h

theorem gen_cert : mclGenCertificate () = true := by
  unfold mclGenCertificate mclGenCheck pairCheck
  simp only [mclGenData, Bool.and_eq_true]
  have hL := letters_get
  have tr : ∀ i < 5, _ := fun i hi => tree_spec hi
  generalize slpLetters 275 (mclLetters (mclGenTbl 0) (mclGenTbl 1)) mclGenWords = L at hL tr ⊢
  have hp := pairOK_spec
  have ap0 : ∀ x < 275, ap L[0]! x = LJ 0 x := fun x hx => (hL.2 0 (by norm_num) x hx).1
  have ap6 : ∀ x < 275, ap L[6]! x = LJ 6 x := fun x hx => (hL.2 6 (by norm_num) x hx).1
  have ap16 : ∀ x < 275, ap L[16]! x = LJ 16 x := fun x hx => (hL.2 16 (by norm_num) x hx).1
  have ap18 : ∀ x < 275, ap L[18]! x = LJ 18 x := fun x hx => (hL.2 18 (by norm_num) x hx).1
  have lt : ∀ l < 36, ∀ x < 275, LJ l x < 275 := fun l hl x hx => (hL.2 l hl x hx).2
  have hsz : ∀ i < 5, (levelTrees 275 L #[8, 10, 12, 14, 17, 18] #[0, 3, 4, 5, 1])[i]! =
      tbfsRec 275 (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) := by
    intro i hi
    unfold levelTrees
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, bs_get hi]
    exact (tr i hi).1
  repeat' apply And.intro
  · exact invA.1
  · exact invB.1
  · exact slp_ok
  · rw [hL.1]; rfl
  · rw [TBfs.allIn_iff]
    intro j hj
    rw [words_size] at hj
    refine invOK_of fun i hi => ?_
    rw [(hL.2 _ (by omega) i hi).1, (hL.2 _ (by omega) _ (inv_spec hj hi).1).1]
    exact (inv_spec hj hi).2.2
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · refine invoOK_of fun i hi => ?_
    change ap L[0]! (ap L[0]! i) = i
    rw [ap0 i hi, ap0 _ (lt 0 (by norm_num) i hi)]
    exact hp.1 i hi |>.1
  · change (ap L[0]! 1 != 1) = true
    rw [ap0 1 (by norm_num)]
    simp [hp.2.1]
  · refine invoOK_of fun i hi => ?_
    change ap L[6]! (ap L[6]! i) = i
    rw [ap6 i hi, ap6 _ (lt 6 (by norm_num) i hi)]
    exact hp.1 i hi |>.2.1
  · change (ap L[6]! 0 != 0) = true
    rw [ap6 0 (by norm_num)]
    simp [hp.2.2.1]
  · change (ap L[0]! 0 != ap L[6]! 0) = true
    rw [ap0 0 (by norm_num), ap6 0 (by norm_num)]
    simp [hp.2.2.2]
  · refine commTab_of fun i hi => ?_
    change ap L[0]! (ap L[6]! i) = ap L[6]! (ap L[0]! i)
    rw [ap6 i hi, ap0 i hi, ap0 _ (lt 6 (by norm_num) i hi), ap6 _ (lt 0 (by norm_num) i hi)]
    exact hp.1 i hi |>.2.2.1
  · refine commTab_of fun i hi => ?_
    change ap L[0]! (ap L[16]! i) = ap L[16]! (ap L[0]! i)
    rw [ap16 i hi, ap0 i hi, ap0 _ (lt 16 (by norm_num) i hi), ap16 _ (lt 0 (by norm_num) i hi)]
    exact hp.1 i hi |>.2.2.2.1
  · refine commTab_of fun i hi => ?_
    change ap L[6]! (ap L[18]! i) = ap L[18]! (ap L[6]! i)
    rw [ap18 i hi, ap6 i hi, ap6 _ (lt 18 (by norm_num) i hi), ap18 _ (lt 6 (by norm_num) i hi)]
    exact hp.1 i hi |>.2.2.2.2
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [CFSG.KC.Misc.Xi.allIn_iff']
    decide +kernel
  · simp only [nestAt, CFSG.KC.Misc.Xi.allIn_iff']
    decide +kernel
  · rw [CFSG.KC.Misc.Xi.allIn_iff']
    intro i h1 h2
    rw [CFSG.KC.Misc.Xi.allIn_iff']
    intro j h3 h4
    have h2' : i < 5 := h2
    rw [st_get (by omega)] at h3
    rw [st_get (by omega)] at h4
    have hs := st_lt (i := i) (by omega)
    rw [bs_get (by omega), (hL.2 _ (by omega) _ (by interval_cases i <;> decide)).1]
    simp [fix_spec (i - 1) (by omega) j (by
      have e : i - 1 + 1 = i := by omega
      rw [e]; exact h3) (by
      have e : i - 1 + 1 + 1 = i + 1 := by omega
      rw [e]; exact h4)]
  · simp [levelTrees]
  · rw [TBfs.allIn_iff]
    intro i hi
    have hi' : i < 5 := hi
    rw [hsz i hi', bs_get hi']
    exact (tr i hi').2
  · have e : orbitSizes (levelTrees 275 L #[8, 10, 12, 14, 17, 18] #[0, 3, 4, 5, 1]) =
        [CNTJ 0, CNTJ 1, CNTJ 2, CNTJ 3, CNTJ 4] := by
      unfold orbitSizes
      apply List.ext_getElem
      · simp [levelTrees]
      · intro k h1 h2
        have hk : k < 5 := by simpa [levelTrees] using h1
        rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos _ k (by simpa [levelTrees] using hk),
          hsz k hk]
        simp only [tbfsRec, Array.size_ofFn]
        interval_cases k <;> rfl
    rw [e]
    have hc := cnt_ok
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
    rw [h0, h1, h2, h3, h4]
    rfl

end CertificateChecks.KernelMcLGen

end
