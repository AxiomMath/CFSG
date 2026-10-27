module

public import Certificates.Data.Kernel.Fi22.T46
public import Certificates.Data.CFSGNative.Fi22.Local
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.PChainSound
import CFSG.Certificates.Kernel.Fi22.WordInts
import CFSG.Fischer.UnitaryPerm
import CFSG.Certificates.Kernel.Fi22.LettersSound
public import Certificates.Kernel.Misc.Unitary
import Certificates.Kernel.Sporadic.ON.Gen
import Certificates.Kernel.Sporadic.StrList
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT46

open CFSG.KS.T46K

@[expose] noncomputable def gs (j : Nat) : Bool := genSl j

end CertificateChecks.KernelT46

#kon_slices CertificateChecks.KernelT46.gs 0 46
#kon_join CertificateChecks.KernelT46.gAll CertificateChecks.KernelT46.gs 46

namespace CertificateChecks.KernelT46

open CFSG.KC.Enum CFSG.KS CFSG.KS.T46K CFSG.KS.TW CFSG.KS.PC CFSG.KS.WordInts CFSG.F4.Native
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KD.Misc.Unitary

@[expose] def WL : List (List Nat) :=
  [[0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16],
    [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32],
    [33], [34], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [0], [11], [21],
    [34], [18, 31, 45, 31, 18], [11, 18, 31, 45, 31, 18, 39, 24, 18, 31, 45, 31, 18, 14],
    [11, 14, 11, 18, 31, 45, 31, 18, 39, 24, 18, 31, 45, 31, 18, 14, 14, 11]]

set_option Elab.async false

theorem pts_ok : eqLF UC 0 UL = true := by quickRfl

theorem gens_ok : eqLF GC 0 ((UL.filter fun c => weightC c == 2) ++ [85]) = true := by quickRfl

theorem word_ok : wordK = true := by quickRfl

theorem inv_ok : invK LK 693 106 = true := by quickRfl

theorem words_eq : (t46Words ()).toList.map (List.map fun z => z.natAbs - 1) = WL := by
  simp (disch := simp only [strToList]; decide) only [t46Words, wordOfInts_eq]
  simp only [strToList]
  decide

theorem eqLF_spec {F : Nat → Nat} : ∀ (l : List Nat) (x : Nat), eqLF F x l = true →
    ∀ i < l.length, F (x + i) = l.getD i 0
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | c :: l, x, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (strictB (Nat.succ x) (fun x => eqLF F x l))
      (Nat.beq (F x) c) = true at h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.strictB_eq, Nat.beq_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := eqLF_spec l (x + 1) h.2 i (by simpa using hi)
      rw [show x + (i + 1) = x + 1 + i by omega, this]
      rfl

theorem uPts_get {x : Nat} (hx : x < 693) : uPts[x]! = UC x := by
  rw [hU, getE, (eqLF_spec UL 0 pts_ok x (by rw [show UL.length = 693 from rfl]; exact hx)).symm,
    Nat.zero_add]

theorem tvGens_get {j : Nat} (hj : j < 46) : (tvGens ())[j]! = GC j := by
  have hl : ((UL.filter fun c => weightC c == 2) ++ [85]).length = 46 := by decide
  have := eqLF_spec _ 0 gens_ok j (by rw [hl]; exact hj)
  rw [Nat.zero_add] at this
  rw [gE, List.push_toArray, this]
  simp only [getElem!_def, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  generalize ((UL.filter fun c => weightC c == 2) ++ [85])[j]? = o
  cases o <;> rfl

theorem idx_uPts {y : Nat} (hy : y < 693) : uPts.toList.idxOf uPts[y]! = y := by
  have hP := CFSG.Fischer.ptsFacts_of uPtsOK_true
  have hs : y < uPts.toList.length := by rw [Array.length_toList, hP.size]; exact hy
  rw [getElem!_pos uPts y (by rw [hP.size]; exact hy), ← Array.getElem_toList]
  exact List.get_idxOf (CFSG.Fischer.uPts_nodup hP) ⟨y, hs⟩

theorem gen_facts {j x : Nat} (hj : j < 46) (hx : x < 693) :
    LK (2 * j) x < 693 ∧ UC (LK (2 * j) x) = normC (tvC (GC j) (UC x)) := by
  have h0 := gAll j hj
  unfold gs genSl at h0
  have h := Raw.Orb.allN_iff.1 h0 x hx
  unfold genAt at h
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem UC_lt (x : Nat) : UC x < 4096 := by
  unfold UC LK
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem gen_TR {j : Nat} (hj : j < 46) : TR 693 (tvTable (tvGens ())[j]!) (LK (2 * j)) := by
  refine ⟨by simp [tvTable], fun x hx => ⟨?_, (gen_facts hj hx).1⟩⟩
  obtain ⟨h1, h2⟩ := gen_facts hj hx
  have hm : normC (tvC (tvGens ())[j]! uPts[x]!) = uPts[LK (2 * j) x]! := by
    rw [tvGens_get hj, uPts_get hx, uPts_get h1, h2]
  unfold ap tvTable
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, hm]
  have hc : uPts[LK (2 * j) x]! < 4096 := by rw [uPts_get h1]; exact UC_lt _
  have hle : uPos[uPts[LK (2 * j) x]!]! ≤ 693 := by
    rw [CFSG.Fischer.uPos_get hc, ← (CFSG.Fischer.ptsFacts_of uPtsOK_true).size,
      ← Array.length_toList]
    exact List.idxOf_le_length
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (lt_of_le_of_lt hle (by norm_num)),
    CFSG.Fischer.uPos_get hc, idx_uPts h1]

@[expose] noncomputable def GZ (z : Int) (y : Nat) : Nat := LK (2 * (z.natAbs - 1)) y

theorem t46Gen_TR {z : Int} (hz : z.natAbs - 1 < 46) : TR 693 (t46Gen z) (GZ z) :=
  gen_TR hz

theorem appW_map (w : List Int) (x : Nat) :
    appW (w.map fun z => z.natAbs - 1) x = w.foldr GZ x := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    change LK (Nat.mul 2 (z.natAbs - 1)) (appW (w.map fun z => z.natAbs - 1) x) = _
    rw [ih]
    rfl

theorem WL_get {j : Nat} (hj : j < 53) : ∀ x < 693, appW (WL.getD j []) x = LK (2 * j) x := by
  intro x hx
  have hw := word_ok
  unfold wordK at hw
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hw
  obtain ⟨w0, w1, w2, w3, w4, w5, w6⟩ := hw
  have hc : ∀ {k : Nat} {w : List Nat}, wChk k w = true → appW w x = LK (2 * k) x := by
    intro k w h
    exact (Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h x hx)).symm
  by_cases h46 : j < 46
  · have e : WL.getD j [] = [j] := by
      have : ∀ j < 46, WL.getD j [] = [j] := by decide
      exact this j h46
    rw [e]
    rfl
  · interval_cases j
    · exact hc w0
    · exact hc w1
    · exact hc w2
    · exact hc w3
    · exact hc w4
    · exact hc w5
    · exact hc w6

theorem words_size : (t46Words ()).size = 53 := by
  have := congrArg List.length words_eq
  rw [List.length_map, Array.length_toList] at this
  exact this.trans rfl

theorem word_get {j : Nat} (hj : j < 53) :
    ((t46Words ())[j]!).map (fun z => z.natAbs - 1) = WL.getD j [] := by
  have hj' : j < (t46Words ()).size := by rw [words_size]; exact hj
  have := congrArg (fun L : List (List Nat) => L.getD j []) words_eq
  rw [← this, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hj', getElem!_pos _ j hj']
  rfl

theorem word_lt {j : Nat} (hj : j < 53) : ∀ z ∈ (t46Words ())[j]!, z.natAbs - 1 < 46 := by
  intro z hz
  have hm : z.natAbs - 1 ∈ WL.getD j [] := by
    rw [← word_get hj]
    exact List.mem_map_of_mem hz
  have hall : ∀ j < 53, ∀ g ∈ WL.getD j [], g < 46 := by decide
  exact hall j hj _ hm

theorem even_TR {j : Nat} (hj : j < 53) :
    TR 693 (wordT 693 t46Gen (t46Words ())[j]!) (LK (2 * j)) := by
  have hT := wordT_TR (n := 693) (by norm_num) (gens := t46Gen) (G := GZ) (t46Words ())[j]!
    fun z hz => t46Gen_TR (word_lt hj z hz)
  refine CFSG.KS.Fi22L.TR_congr hT fun x hx => ?_
  rw [← appW_map, word_get hj, WL_get hj x hx]

theorem letters : (t46Letters ()).size = 106 ∧ ∀ l < 106, TR 693 (t46Letters ())[l]! (LK l) := by
  have hs : (t46Letters ()).size = 106 := by
    simp [t46Letters, buildLetters, words_size]
  refine ⟨hs, fun l hl => ?_⟩
  have hget : (t46Letters ())[l]! =
      if l % 2 = 0 then wordT 693 t46Gen (t46Words ())[l / 2]!
      else invT 693 (wordT 693 t46Gen (t46Words ())[l / 2]!) := by
    rw [getElem!_pos _ l (by rw [hs]; exact hl)]
    simp only [t46Letters, buildLetters, Array.getElem_ofFn]
  have hj : l / 2 < 53 := by omega
  have hE := even_TR hj
  rw [hget]
  split_ifs with h2
  · have e : 2 * (l / 2) = l := by omega
    rw [e] at hE
    exact hE
  · have hk : l / 2 < 106 / 2 := by omega
    have e : 2 * (l / 2) + 1 = l := by omega
    refine invT_TR (n := 693) (by norm_num) hE fun i hi => ?_
    obtain ⟨-, a2, a3⟩ := invK_spec inv_ok hk hi
    have hgf := fun x (hx : x < 693) => (invK_spec inv_ok hk hx).2.2
    have hfg := pair_inv (fun x hx => (invK_spec inv_ok hk hx).1) hgf i hi
    rw [e] at a2 hfg a3
    exact ⟨a2, hfg, a3⟩

end CertificateChecks.KernelT46

end
