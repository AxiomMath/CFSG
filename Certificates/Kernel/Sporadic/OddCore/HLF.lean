module

public import Certificates.Kernel.Sporadic.OddCore.HLAll
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.OddCore.HLD0
public import Certificates.Kernel.Sporadic.OddCore.HLD1
public import Certificates.Kernel.Sporadic.OddCore.HLK0
public import Certificates.Kernel.Sporadic.OddCore.HLK1
public import Certificates.Kernel.Sporadic.OddCore.HLK2
public import Certificates.Kernel.Sporadic.OddCore.HLK3
public import Certificates.Kernel.Sporadic.OddCore.HLK4
public import Certificates.Kernel.Sporadic.OddCore.HLK5
public import Certificates.Kernel.Sporadic.OddCore.HLK6
public import Certificates.Kernel.Sporadic.OddCore.HLO0
public import Certificates.Kernel.Sporadic.OddCore.HLO1
public import Certificates.Kernel.Sporadic.OddCore.HLO2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.HeldB CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.Mathieu CFSG.KC.Misc.HexAt CFSG.Sporadic.SuzOddCore

theorem base : szOK 105 7 = true ∧ canonK 105 7 (mask 7) (105 * 7) (pidn 105 7) = true ∧
    CFSG.KS.Prim.idK 105 7 (mask 7) = true ∧
    allN 2 (fun k => bAnd(
      canonK 8330 14 (mask 14) (8330 * 14) (CertificateChecks.KernelSpor.HeC.S k),
      canonK 8330 14 (mask 14) (8330 * 14) (CertificateChecks.KernelSpor.HeC.SI k))) = true := by
  simpa only [bAnd_iff] using base_ok

theorem idTab_eq : idTab 105 = unpack 105 7 (pidn 105 7) := (idK_sound base.2.2.1).symm

theorem comp105 {p q : Nat} (hp : canonK 105 7 (mask 7) (105 * 7) p = true)
    (hq : canonK 105 7 (mask 7) (105 * 7) q = true) :
    comp 105 (unpack 105 7 p) (unpack 105 7 q) = unpack 105 7 (pcomp 105 7 (mask 7) p q) :=
  compA_unpack hp hq

theorem rec_get {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 105 7 cnt T PL).tabs[i]! = unpack 105 7 (T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem canon_lt {p a : Nat} (hp : canonK 105 7 (mask 7) (105 * 7) p = true) (ha : a < 105) :
    pg 7 (mask 7) p a < 105 := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  exact Eq.mp Nat.blt_eq (allN_spec hp.2.2 a ha)

theorem hcanon {k : Nat} (hk : k < 2) :
    canonK 8330 14 (mask 14) (8330 * 14) (CertificateChecks.KernelSpor.HeC.S k) = true ∧
      canonK 8330 14 (mask 14) (8330 * 14) (CertificateChecks.KernelSpor.HeC.SI k) = true :=
  (bAnd_iff _ _).1 (allN_spec base.2.2.2 k hk)

theorem hlt {p x : Nat} (hp : canonK 8330 14 (mask 14) (8330 * 14) p = true) (hx : x < 8330) :
    pg 14 (mask 14) p x < 8330 := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  exact Eq.mp Nat.blt_eq (allN_spec hp.2.2 x hx)

theorem letters_get {k : Nat} (hk : k < 2) :
    heGen k = unpack 8330 14 (CertificateChecks.KernelSpor.HeC.S k) ∧
      invCand 8330 (heGen k) = unpack 8330 14 (CertificateChecks.KernelSpor.HeC.SI k) := by
  have h := CertificateChecks.KernelSpor.He2112.gen_eq k hk
  rw [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn] at h
  refine ⟨h, ?_⟩
  rw [h]
  exact (invEqK_sound (allN_spec CertificateChecks.KernelSpor.He2112.perm k (by omega))).1

@[expose] def letOK (l : Int) : Prop := l = 1 ∨ l = 2 ∨ l = 3 ∨ l = -1 ∨ l = -2 ∨ l = -3

theorem letterA3 (a b c : Array Nat) (f : Array Nat → Array Nat) :
    letterA #[a, b, c] (#[a, b, c].map f) 1 = a ∧ letterA #[a, b, c] (#[a, b, c].map f) 2 = b ∧
      letterA #[a, b, c] (#[a, b, c].map f) 3 = c ∧ letterA #[a, b, c] (#[a, b, c].map f) (-1) = f
          a ∧
      letterA #[a, b, c] (#[a, b, c].map f) (-2) = f b ∧
      letterA #[a, b, c] (#[a, b, c].map f) (-3) = f c := by
  simp [letterA]

theorem letter_get {l : Int} (hl : letOK l) {x : Nat} (hx : x < 8330) :
    (letterA heInnerLetters0 (heInnerLetters0.map (invCand 8330)) l)[x]! =
        pg 14 (mask 14) (letK l) x ∧
      pg 14 (mask 14) (letK l) x < 8330 := by
  obtain ⟨g0, i0⟩ := letters_get (k := 0) (by norm_num)
  obtain ⟨g1, i1⟩ := letters_get (k := 1) (by norm_num)
  have c0 := hcanon (k := 0) (by norm_num)
  have c1 := hcanon (k := 1) (by norm_num)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := letterA3 (heGen 0) (heGen 1) (heGen 0) (invCand 8330)
  unfold heInnerLetters0
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e1, g0, CFSG.KC.Misc.PairCount.unpack_get hx]
    exact ⟨rfl, hlt c0.1 hx⟩
  · rw [e2, g1, CFSG.KC.Misc.PairCount.unpack_get hx]
    exact ⟨rfl, hlt c1.1 hx⟩
  · rw [e3, g0, CFSG.KC.Misc.PairCount.unpack_get hx]
    exact ⟨rfl, hlt c0.1 hx⟩
  · rw [e4, i0, CFSG.KC.Misc.PairCount.unpack_get hx]
    exact ⟨rfl, hlt c0.2 hx⟩
  · rw [e5, i1, CFSG.KC.Misc.PairCount.unpack_get hx]
    exact ⟨rfl, hlt c1.2 hx⟩
  · rw [e6, i0, CFSG.KC.Misc.PairCount.unpack_get hx]
    exact ⟨rfl, hlt c0.2 hx⟩

theorem hwpt_cons (l : Int) (wd : List Int) (x : Nat) :
    hwpt (l :: wd) x = pg 14 (mask 14) (letK l) (hwpt wd x) := by
  change strictN (hwpt wd x) (fun y => pg 14 (mask 14) (letK l) y) = _
  rw [strictN_app']

theorem word_get : ∀ wd : List Int, (∀ l ∈ wd, letOK l) → ∀ x < 8330,
    (wordA 8330 heInnerLetters0 (heInnerLetters0.map (invCand 8330)) wd)[x]! = hwpt wd x ∧
      hwpt wd x < 8330
  | [], _, x, hx => by
    refine ⟨?_, hx⟩
    rw [wordA, CertificateChecks.KernelSpor.OddCore.idA_get hx]
    rfl
  | l :: wd, h, x, hx => by
    obtain ⟨ih1, ih2⟩ := word_get wd (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) x hx
    obtain ⟨e1, e2⟩ := letter_get (h l List.mem_cons_self) ih2
    rw [wordA, CertificateChecks.KernelSpor.OddCore.compA_get hx, ih1, e1, hwpt_cons]
    exact ⟨rfl, e2⟩

theorem words_ok : ∀ j < 9, ∀ l ∈ heInnerWords0.getD j [], letOK l := by
  intro j hj l hl
  unfold letOK
  interval_cases j <;> simp [heInnerWords0] at hl <;> omega

theorem sig_ok {j : Nat} (hj : j < 9) : sigK j = true := by
  interval_cases j
  exacts [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]

theorem sig_facts {j : Nat} (hj : j < 9) :
    canonK 105 7 (mask 7) (105 * 7) (HKE.G j) = true ∧
      invEqK 105 7 (mask 7) (105 * 7) (HKE.G j) (HKI j) = true ∧
      invEqK 105 7 (mask 7) (105 * 7) (HKI j) (HKE.G j) = true ∧
      canonK 105 7 (mask 7) (105 * 7) (HKI j) = true ∧
      Nat.beq (pcomp 105 7 (mask 7) (HKI j) (HKE.G j)) (pidn 105 7) = true ∧
      allN 105 (fun k => Nat.beq (hwpt (wK j) (nget omL k))
        (nget omL (pg 7 (mask 7) (HKE.G j) k))) = true := by
  simpa only [sigK, bAnd_iff] using sig_ok hj

theorem om_eq : heOmega0.toList = omL := by decide

theorem om_len : omL.length = 105 := rfl

theorem om_nodup : omL.Nodup := by decide

theorem om_lt {a : Nat} (ha : a < 105) : omL[a]'(by rw [om_len]; exact ha) < 8330 := by
  have h : ∀ x ∈ omL, x < 8330 := by decide
  exact h _ (List.getElem_mem _)

theorem om_get {a : Nat} (ha : a < 105) : heOmega0[a]! = nget omL a := by
  rw [getElem!_pos heOmega0 a (by rw [← Array.length_toList, om_eq, om_len]; exact ha),
    nget_get omL (by rw [om_len]; exact ha), ← Array.getElem_toList]
  simp only [om_eq]

theorem om_inc : ∀ k < 104, nget omL k < nget omL (k + 1) := by decide

theorem inc_ok : incListOK 8330 105 heOmega0 = true := by
  unfold incListOK
  simp only [Bool.and_eq_true, beq_iff_eq, CertificateChecks.KernelSpor.OddCore.allLt_iff,
    decide_eq_true_eq]
  refine ⟨⟨by rw [← Array.length_toList, om_eq, om_len], fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [om_get hk, nget_get omL (by rw [om_len]; exact hk)]
    exact om_lt hk
  · rw [om_get (by omega), om_get (by omega)]
    exact om_inc k (by omega)

theorem c0_pt {j a : Nat} (hj : j < 9) (ha : a < 105) :
    (heInnerC0 j)[heOmega0[a]!]! = heOmega0[(unpack 105 7 (HKE.G j))[a]!]! := by
  obtain ⟨hc, -, -, -, -, hall⟩ := sig_facts hj
  have hb := Nat.eq_of_beq_eq_true (allN_spec hall a ha)
  have hs := canon_lt hc ha
  rw [om_get ha, CFSG.KC.Misc.PairCount.unpack_get ha, om_get hs, ← hb]
  unfold heInnerC0
  have hx : nget omL a < 8330 := by
    rw [nget_get omL (by rw [om_len]; exact ha)]
    exact om_lt ha
  exact (word_get _ (words_ok j hj) _ hx).1

theorem kgens_get {j : Nat} (hj : j < 9) : heKGens[j]! = unpack 105 7 (HKE.G j) := by
  obtain ⟨hc, -, -, -, -, hall⟩ := sig_facts hj
  rw [getElem!_pos heKGens j (by simp [heKGens]; omega)]
  simp only [heKGens, Array.getElem_ofFn]
  apply Array.ext
  · simp [restrictArr, unpack, ← Array.length_toList, om_eq, om_len]
  · intro a h1 _
    have ha : a < 105 := by simpa [restrictArr, om_eq, om_len] using h1
    simp only [restrictArr, List.getElem_toArray, List.getElem_map]
    rw [← getElem!_pos (unpack 105 7 (HKE.G j)) a (by simp [unpack, ha])]
    have e := c0_pt hj ha
    have hs := canon_lt hc ha
    rw [CFSG.KC.Misc.PairCount.unpack_get ha] at e ⊢
    have hsz : a < heOmega0.size := by rw [← Array.length_toList, om_eq, om_len]; exact ha
    rw [Array.getElem_toList, ← getElem!_pos heOmega0 a hsz, e, om_get hs,
      nget_get omL (by rw [om_len]; exact hs), om_eq, om_nodup.idxOf_getElem]

theorem kinvs_get {j : Nat} (hj : j < 9) : heKInvs[j]! = unpack 105 7 (HKI j) := by
  rw [heKInvs, getElem!_pos _ j (by simp [heKGens]; omega), Array.getElem_map,
    ← getElem!_pos heKGens j (by simp [heKGens]; omega), kgens_get hj]
  exact (invEqK_sound (sig_facts hj).2.1).1

theorem k_ok : GensOK 105 7 HKE.k HKE.G heKGens :=
  ⟨rfl, fun _ hj => ⟨kgens_get hj, (sig_facts hj).1⟩⟩

theorem k_first : (∀ j < 9, permChk 105 heKGens[j]! = true ∧ heKGens[j]!.size = 105 ∧
    agreeOK 105 (heInnerC0 j) heOmega0 heKGens[j]! = true) := by
  intro j hj
  obtain ⟨hc, h1, h2, hci, -, -⟩ := sig_facts hj
  rw [kgens_get hj]
  refine ⟨?_, unpack_size _ _ _, ?_⟩
  · unfold permChk
    obtain ⟨e1, e2⟩ := invEqK_sound h1
    obtain ⟨-, e4⟩ := invEqK_sound h2
    rw [e1, e2, e4]
    rfl
  · unfold agreeOK
    rw [CertificateChecks.KernelSpor.OddCore.allLt_iff]
    intro a ha
    rw [c0_pt hj ha]
    exact beq_self_eq_true _

theorem cover' {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → P i) : ∀ i < L * N, P i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this


theorem kpt_all {i : Nat} (hi : i < HKE.cnt) : penumPtK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI
      HKE.k HKE.cnt HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI i = true := by
  have key : ∀ i < 450 * 90, i < HKE.cnt → penumPtK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI
      HKE.k HKE.cnt HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI i = true := by
    refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
    interval_cases s
    · exact penumSl_spec kE0 i h1 h2 hc
    · exact penumSl_spec kE1 i h1 h2 hc
    · exact penumSl_spec kE2 i h1 h2 hc
    · exact penumSl_spec kE3 i h1 h2 hc
    · exact penumSl_spec kE4 i h1 h2 hc
    · exact penumSl_spec kE5 i h1 h2 hc
    · exact penumSl_spec kE6 i h1 h2 hc
    · exact penumSl_spec kE7 i h1 h2 hc
    · exact penumSl_spec kE8 i h1 h2 hc
    · exact penumSl_spec kE9 i h1 h2 hc
    · exact penumSl_spec kE10 i h1 h2 hc
    · exact penumSl_spec kE11 i h1 h2 hc
    · exact penumSl_spec kE12 i h1 h2 hc
    · exact penumSl_spec kE13 i h1 h2 hc
    · exact penumSl_spec kE14 i h1 h2 hc
    · exact penumSl_spec kE15 i h1 h2 hc
    · exact penumSl_spec kE16 i h1 h2 hc
    · exact penumSl_spec kE17 i h1 h2 hc
    · exact penumSl_spec kE18 i h1 h2 hc
    · exact penumSl_spec kE19 i h1 h2 hc
    · exact penumSl_spec kE20 i h1 h2 hc
    · exact penumSl_spec kE21 i h1 h2 hc
    · exact penumSl_spec kE22 i h1 h2 hc
    · exact penumSl_spec kE23 i h1 h2 hc
    · exact penumSl_spec kE24 i h1 h2 hc
    · exact penumSl_spec kE25 i h1 h2 hc
    · exact penumSl_spec kE26 i h1 h2 hc
    · exact penumSl_spec kE27 i h1 h2 hc
    · exact penumSl_spec kE28 i h1 h2 hc
    · exact penumSl_spec kE29 i h1 h2 hc
    · exact penumSl_spec kE30 i h1 h2 hc
    · exact penumSl_spec kE31 i h1 h2 hc
    · exact penumSl_spec kE32 i h1 h2 hc
    · exact penumSl_spec kE33 i h1 h2 hc
    · exact penumSl_spec kE34 i h1 h2 hc
    · exact penumSl_spec kE35 i h1 h2 hc
    · exact penumSl_spec kE36 i h1 h2 hc
    · exact penumSl_spec kE37 i h1 h2 hc
    · exact penumSl_spec kE38 i h1 h2 hc
    · exact penumSl_spec kE39 i h1 h2 hc
    · exact penumSl_spec kE40 i h1 h2 hc
    · exact penumSl_spec kE41 i h1 h2 hc
    · exact penumSl_spec kE42 i h1 h2 hc
    · exact penumSl_spec kE43 i h1 h2 hc
    · exact penumSl_spec kE44 i h1 h2 hc
    · exact penumSl_spec kE45 i h1 h2 hc
    · exact penumSl_spec kE46 i h1 h2 hc
    · exact penumSl_spec kE47 i h1 h2 hc
    · exact penumSl_spec kE48 i h1 h2 hc
    · exact penumSl_spec kE49 i h1 h2 hc
    · exact penumSl_spec kE50 i h1 h2 hc
    · exact penumSl_spec kE51 i h1 h2 hc
    · exact penumSl_spec kE52 i h1 h2 hc
    · exact penumSl_spec kE53 i h1 h2 hc
    · exact penumSl_spec kE54 i h1 h2 hc
    · exact penumSl_spec kE55 i h1 h2 hc
    · exact penumSl_spec kE56 i h1 h2 hc
    · exact penumSl_spec kE57 i h1 h2 hc
    · exact penumSl_spec kE58 i h1 h2 hc
    · exact penumSl_spec kE59 i h1 h2 hc
    · exact penumSl_spec kE60 i h1 h2 hc
    · exact penumSl_spec kE61 i h1 h2 hc
    · exact penumSl_spec kE62 i h1 h2 hc
    · exact penumSl_spec kE63 i h1 h2 hc
    · exact penumSl_spec kE64 i h1 h2 hc
    · exact penumSl_spec kE65 i h1 h2 hc
    · exact penumSl_spec kE66 i h1 h2 hc
    · exact penumSl_spec kE67 i h1 h2 hc
    · exact penumSl_spec kE68 i h1 h2 hc
    · exact penumSl_spec kE69 i h1 h2 hc
    · exact penumSl_spec kE70 i h1 h2 hc
    · exact penumSl_spec kE71 i h1 h2 hc
    · exact penumSl_spec kE72 i h1 h2 hc
    · exact penumSl_spec kE73 i h1 h2 hc
    · exact penumSl_spec kE74 i h1 h2 hc
    · exact penumSl_spec kE75 i h1 h2 hc
    · exact penumSl_spec kE76 i h1 h2 hc
    · exact penumSl_spec kE77 i h1 h2 hc
    · exact penumSl_spec kE78 i h1 h2 hc
    · exact penumSl_spec kE79 i h1 h2 hc
    · exact penumSl_spec kE80 i h1 h2 hc
    · exact penumSl_spec kE81 i h1 h2 hc
    · exact penumSl_spec kE82 i h1 h2 hc
    · exact penumSl_spec kE83 i h1 h2 hc
    · exact penumSl_spec kE84 i h1 h2 hc
    · exact penumSl_spec kE85 i h1 h2 hc
    · exact penumSl_spec kE86 i h1 h2 hc
    · exact penumSl_spec kE87 i h1 h2 hc
    · exact penumSl_spec kE88 i h1 h2 hc
    · exact penumSl_spec kE89 i h1 h2 hc
  have e : HKE.cnt = 40320 := rfl
  exact key i (by omega) hi

theorem dpt_all {i : Nat} (hi : i < HDE.cnt) : penumPtK 105 7 (mask 7) (105 * 7) false HDE.G HDE.GI
      HDE.k HDE.cnt HDE.T HDE.PL HDE.POS HDE.SRT HDE.SRI i = true := by
  have key : ∀ i < 450 * 45, i < HDE.cnt → penumPtK 105 7 (mask 7) (105 * 7) false HDE.G HDE.GI
      HDE.k HDE.cnt HDE.T HDE.PL HDE.POS HDE.SRT HDE.SRI i = true := by
    refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
    interval_cases s
    · exact penumSl_spec dE0 i h1 h2 hc
    · exact penumSl_spec dE1 i h1 h2 hc
    · exact penumSl_spec dE2 i h1 h2 hc
    · exact penumSl_spec dE3 i h1 h2 hc
    · exact penumSl_spec dE4 i h1 h2 hc
    · exact penumSl_spec dE5 i h1 h2 hc
    · exact penumSl_spec dE6 i h1 h2 hc
    · exact penumSl_spec dE7 i h1 h2 hc
    · exact penumSl_spec dE8 i h1 h2 hc
    · exact penumSl_spec dE9 i h1 h2 hc
    · exact penumSl_spec dE10 i h1 h2 hc
    · exact penumSl_spec dE11 i h1 h2 hc
    · exact penumSl_spec dE12 i h1 h2 hc
    · exact penumSl_spec dE13 i h1 h2 hc
    · exact penumSl_spec dE14 i h1 h2 hc
    · exact penumSl_spec dE15 i h1 h2 hc
    · exact penumSl_spec dE16 i h1 h2 hc
    · exact penumSl_spec dE17 i h1 h2 hc
    · exact penumSl_spec dE18 i h1 h2 hc
    · exact penumSl_spec dE19 i h1 h2 hc
    · exact penumSl_spec dE20 i h1 h2 hc
    · exact penumSl_spec dE21 i h1 h2 hc
    · exact penumSl_spec dE22 i h1 h2 hc
    · exact penumSl_spec dE23 i h1 h2 hc
    · exact penumSl_spec dE24 i h1 h2 hc
    · exact penumSl_spec dE25 i h1 h2 hc
    · exact penumSl_spec dE26 i h1 h2 hc
    · exact penumSl_spec dE27 i h1 h2 hc
    · exact penumSl_spec dE28 i h1 h2 hc
    · exact penumSl_spec dE29 i h1 h2 hc
    · exact penumSl_spec dE30 i h1 h2 hc
    · exact penumSl_spec dE31 i h1 h2 hc
    · exact penumSl_spec dE32 i h1 h2 hc
    · exact penumSl_spec dE33 i h1 h2 hc
    · exact penumSl_spec dE34 i h1 h2 hc
    · exact penumSl_spec dE35 i h1 h2 hc
    · exact penumSl_spec dE36 i h1 h2 hc
    · exact penumSl_spec dE37 i h1 h2 hc
    · exact penumSl_spec dE38 i h1 h2 hc
    · exact penumSl_spec dE39 i h1 h2 hc
    · exact penumSl_spec dE40 i h1 h2 hc
    · exact penumSl_spec dE41 i h1 h2 hc
    · exact penumSl_spec dE42 i h1 h2 hc
    · exact penumSl_spec dE43 i h1 h2 hc
    · exact penumSl_spec dE44 i h1 h2 hc
  have e : HDE.cnt = 20160 := rfl
  exact key i (by omega) hi

theorem orb_pt {l i : Nat} (hl : l < 10) (hi : i < HOF.C l) :
    penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C l) (offF HOF.T (HOF.TO l))
      (offF HOF.PL (HOF.PLO l)) (offF HOF.POS (HOF.POSO l)) (offF HOF.SRT (HOF.SRTO l))
      (offF HOF.SRI (HOF.SRIO l)) i = true := by
  interval_cases l
  · have key : ∀ i < 450 * 1, i < HOF.C 0 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 0)
          (offF HOF.T (HOF.TO 0)) (offF HOF.PL (HOF.PLO 0)) (offF HOF.POS (HOF.POSO 0))
          (offF HOF.SRT (HOF.SRTO 0)) (offF HOF.SRI (HOF.SRIO 0)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE0_0 i h1 h2 hc
    have e : HOF.C 0 = 1 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 1, i < HOF.C 1 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 1)
          (offF HOF.T (HOF.TO 1)) (offF HOF.PL (HOF.PLO 1)) (offF HOF.POS (HOF.POSO 1))
          (offF HOF.SRT (HOF.SRTO 1)) (offF HOF.SRI (HOF.SRIO 1)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE1_0 i h1 h2 hc
    have e : HOF.C 1 = 315 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 3, i < HOF.C 2 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 2)
          (offF HOF.T (HOF.TO 2)) (offF HOF.PL (HOF.PLO 2)) (offF HOF.POS (HOF.POSO 2))
          (offF HOF.SRT (HOF.SRTO 2)) (offF HOF.SRI (HOF.SRIO 2)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE2_0 i h1 h2 hc
      · exact penumSl_spec oE2_1 i h1 h2 hc
      · exact penumSl_spec oE2_2 i h1 h2 hc
    have e : HOF.C 2 = 1260 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 3, i < HOF.C 3 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 3)
          (offF HOF.T (HOF.TO 3)) (offF HOF.PL (HOF.PLO 3)) (offF HOF.POS (HOF.POSO 3))
          (offF HOF.SRT (HOF.SRTO 3)) (offF HOF.SRI (HOF.SRIO 3)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE3_0 i h1 h2 hc
      · exact penumSl_spec oE3_1 i h1 h2 hc
      · exact penumSl_spec oE3_2 i h1 h2 hc
    have e : HOF.C 3 = 1260 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 3, i < HOF.C 4 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 4)
          (offF HOF.T (HOF.TO 4)) (offF HOF.PL (HOF.PLO 4)) (offF HOF.POS (HOF.POSO 4))
          (offF HOF.SRT (HOF.SRTO 4)) (offF HOF.SRI (HOF.SRIO 4)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE4_0 i h1 h2 hc
      · exact penumSl_spec oE4_1 i h1 h2 hc
      · exact penumSl_spec oE4_2 i h1 h2 hc
    have e : HOF.C 4 = 1260 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 5, i < HOF.C 5 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 5)
          (offF HOF.T (HOF.TO 5)) (offF HOF.PL (HOF.PLO 5)) (offF HOF.POS (HOF.POSO 5))
          (offF HOF.SRT (HOF.SRTO 5)) (offF HOF.SRI (HOF.SRIO 5)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE5_0 i h1 h2 hc
      · exact penumSl_spec oE5_1 i h1 h2 hc
      · exact penumSl_spec oE5_2 i h1 h2 hc
      · exact penumSl_spec oE5_3 i h1 h2 hc
      · exact penumSl_spec oE5_4 i h1 h2 hc
    have e : HOF.C 5 = 2240 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 7, i < HOF.C 6 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 6)
          (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
          (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE6_0 i h1 h2 hc
      · exact penumSl_spec oE6_1 i h1 h2 hc
      · exact penumSl_spec oE6_2 i h1 h2 hc
      · exact penumSl_spec oE6_3 i h1 h2 hc
      · exact penumSl_spec oE6_4 i h1 h2 hc
      · exact penumSl_spec oE6_5 i h1 h2 hc
      · exact penumSl_spec oE6_6 i h1 h2 hc
    have e : HOF.C 6 = 2880 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 7, i < HOF.C 7 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 7)
          (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
          (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE7_0 i h1 h2 hc
      · exact penumSl_spec oE7_1 i h1 h2 hc
      · exact penumSl_spec oE7_2 i h1 h2 hc
      · exact penumSl_spec oE7_3 i h1 h2 hc
      · exact penumSl_spec oE7_4 i h1 h2 hc
      · exact penumSl_spec oE7_5 i h1 h2 hc
      · exact penumSl_spec oE7_6 i h1 h2 hc
    have e : HOF.C 7 = 2880 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 9, i < HOF.C 8 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 8)
          (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
          (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE8_0 i h1 h2 hc
      · exact penumSl_spec oE8_1 i h1 h2 hc
      · exact penumSl_spec oE8_2 i h1 h2 hc
      · exact penumSl_spec oE8_3 i h1 h2 hc
      · exact penumSl_spec oE8_4 i h1 h2 hc
      · exact penumSl_spec oE8_5 i h1 h2 hc
      · exact penumSl_spec oE8_6 i h1 h2 hc
      · exact penumSl_spec oE8_7 i h1 h2 hc
      · exact penumSl_spec oE8_8 i h1 h2 hc
    have e : HOF.C 8 = 4032 := rfl
    exact key i (by omega) hi
  · have key : ∀ i < 450 * 9, i < HOF.C 9 → penumPtK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI
      HOF.k (HOF.C 9)
          (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
          (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) i = true := by
      refine cover' (by norm_num) fun s hs i h1 h2 hc => ?_
      interval_cases s
      · exact penumSl_spec oE9_0 i h1 h2 hc
      · exact penumSl_spec oE9_1 i h1 h2 hc
      · exact penumSl_spec oE9_2 i h1 h2 hc
      · exact penumSl_spec oE9_3 i h1 h2 hc
      · exact penumSl_spec oE9_4 i h1 h2 hc
      · exact penumSl_spec oE9_5 i h1 h2 hc
      · exact penumSl_spec oE9_6 i h1 h2 hc
      · exact penumSl_spec oE9_7 i h1 h2 hc
      · exact penumSl_spec oE9_8 i h1 h2 hc
    have e : HOF.C 9 = 4032 := rfl
    exact key i (by omega) hi

theorem invTab_eq (n : Nat) (t : Tab) : invTab n t = invCand n t := rfl

theorem heads' : penumHdK (pidn 105 7) HKE.cnt 40320 HKE.T HKE.PL = true ∧
    penumHdK (pidn 105 7) HDE.cnt 20160 HDE.T HDE.PL = true := by
  simpa only [bAnd_iff] using heads

theorem k_enum : heKEnum = penumRec 105 7 HKE.cnt HKE.T HKE.PL ∧
    enumOK 105 heKGens (penumRec 105 7 HKE.cnt HKE.T HKE.PL) = true :=
  penumK_left_sound (cap := 40320) base.1 k_ok heads'.1 (fun _ hi => kpt_all hi)

theorem dwords_lt : ∀ j < 5, ∀ i ∈ heDWords.getD j [], i < 9 := by decide

theorem dg_facts {i : Nat} (hi : i < 5) :
    Nat.beq (HDE.G i) (wordTabK 105 7 (mask 7) (pidn 105 7) HKE.G (lget2 heDWords i)) = true ∧
      canonK 105 7 (mask 7) (105 * 7) (HDE.G i) = true ∧
      invEqK 105 7 (mask 7) (105 * 7) (HDE.G i) (HDI i) = true ∧
      invEqK 105 7 (mask 7) (105 * 7) (HDI i) (HDE.G i) = true ∧
      canonK 105 7 (mask 7) (105 * 7) (HDI i) = true ∧
      Nat.beq (pcomp 105 7 (mask 7) (HDI i) (HDE.G i)) (pidn 105 7) = true := by
  simpa only [bAnd_iff] using allN_spec dg_ok i hi

theorem dgens_get {i : Nat} (hi : i < 5) : heDGens[i]! = unpack 105 7 (HDE.G i) := by
  rw [heDGens, getElem!_pos _ i (by simp; omega), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true (dg_facts hi).1, lget2_eq]
  exact (wordTabK_eq idTab_eq base.2.1 _ (fun l hl => by
    have hl9 := dwords_lt i hi l hl
    exact ⟨kgens_get hl9, (sig_facts hl9).1⟩)).1

theorem dinvs_get {i : Nat} (hi : i < 5) : heDInvs[i]! = unpack 105 7 (HDI i) := by
  rw [heDInvs, getElem!_pos _ i (by simp [heDGens]; omega), Array.getElem_map,
    ← getElem!_pos heDGens i (by simp [heDGens]; omega), dgens_get hi, invTab_eq]
  exact (invEqK_sound (dg_facts hi).2.2.1).1

theorem kinvs_get' {j : Nat} (hj : j < 9) : heKInvs[j]! = unpack 105 7 (HKI j) := by
  rw [heKInvs, getElem!_pos _ j (by simp [heKGens]; omega), Array.getElem_map,
    ← getElem!_pos heKGens j (by simp [heKGens]; omega), kgens_get hj, invTab_eq]
  exact (invEqK_sound (sig_facts hj).2.1).1

theorem d_ok : GensOK 105 7 HDE.k HDE.G heDGens :=
  ⟨rfl, fun _ hi => ⟨dgens_get hi, (dg_facts hi).2.1⟩⟩

theorem d_enum : heDEnum = penumRec 105 7 HDE.cnt HDE.T HDE.PL ∧
    enumOK 105 heDGens (penumRec 105 7 HDE.cnt HDE.T HDE.PL) = true :=
  penumK_left_sound (cap := 20160) base.1 d_ok heads'.2 (fun _ hi => dpt_all hi)

theorem normal : normalOK 105 (penumRec 105 7 HDE.cnt HDE.T HDE.PL).tabs heKGens heKInvs heDGens =
    true := by
  unfold normalOK
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by simp [heKInvs], ?_⟩
    unfold allBelow
    rw [List.all_eq_true]
    intro k hk
    have hk9 : k < 9 := by simpa [heKGens] using List.mem_range.1 hk
    obtain ⟨hc, -, -, hci, hpi, -⟩ := sig_facts hk9
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [kinvs_get' hk9, kgens_get hk9]
    refine ⟨unpack_size _ _ _, ?_⟩
    rw [comp105 hci hc, idTab_eq, Nat.eq_of_beq_eq_true hpi]
  · unfold allBelow
    rw [List.all_eq_true]
    intro j hj
    have hj9 : j < 9 := by simpa [heKGens] using List.mem_range.1 hj
    rw [List.all_eq_true]
    intro i hi
    have hi5 : i < 5 := by simpa [heDGens] using List.mem_range.1 hi
    have hn := allN_spec (allN_spec d_norm j hj9) i hi5
    obtain ⟨n1, n2⟩ := (bAnd_iff _ _).1 hn
    rw [strictB_app'] at n1 n2
    obtain ⟨q1, e1⟩ := (bAnd_iff _ _).1 n1
    obtain ⟨q2, e2⟩ := (bAnd_iff _ _).1 n2
    obtain ⟨hc, -, -, hci, -, -⟩ := sig_facts hj9
    have hg := d_ok.2 i hi5
    rw [Bool.and_eq_true, kgens_get hj9, kinvs_get' hj9, hg.1]
    unfold conjTab
    rw [comp105 hc hg.2, comp105 (canonK_pcomp hc hg.2) hci, comp105 hci hg.2,
      comp105 (canonK_pcomp hci hg.2) hc]
    exact ⟨penum_found_sound (fun _ hx => dpt_all hx) (Eq.mp Nat.blt_eq q1)
        (Nat.eq_of_beq_eq_true e1),
      penum_found_sound (fun _ hx => dpt_all hx) (Eq.mp Nat.blt_eq q2) (Nat.eq_of_beq_eq_true e2)⟩

@[expose] noncomputable def orbRec (l : Nat) : Enum :=
  penumRec 105 7 (HOF.C l) (offF HOF.T (HOF.TO l)) (offF HOF.PL (HOF.PLO l))

theorem fg_ok : GensOK 105 7 HOF.k HOF.G heDGens :=
  ⟨rfl, fun j hj => by
    have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec fam_g j hj)).1
    rw [e]
    exact ⟨dgens_get hj, (dg_facts hj).2.1⟩⟩

theorem fgi_ok : GensOK 105 7 HOF.k HOF.GI heDInvs :=
  ⟨by simp [heDInvs, heDGens]; rfl, fun j hj => by
    have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec fam_g j hj)).2
    rw [e]
    exact ⟨dinvs_get hj, (dg_facts hj).2.2.2.2.1⟩⟩

theorem invsD : invsOK 105 heDGens heDInvs = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [heDInvs], ?_⟩
  unfold allBelow
  rw [all_range_iff]
  intro k hk
  have hk5 : k < 5 := by simpa [heDGens] using hk
  obtain ⟨-, hc, -, -, hci, hpi⟩ := dg_facts hk5
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [dinvs_get hk5, dgens_get hk5]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp105 hci hc, idTab_eq, Nat.eq_of_beq_eq_true hpi]

theorem cover_all {k : Nat} (hk : k < 20160) : coverK k = true := by
  rcases Nat.lt_or_ge k 10080 with h0 | h0
  · simpa using allBlk_spec cover0 k h0
  · simpa [Nat.add_sub_cancel' h0] using allBlk_spec cover1 (k - 10080) (by omega)

theorem orb_hd {l : Nat} (hl : l < 10) :
    penumHdK (HOF.R l) (HOF.C l) 5000 (offF HOF.T (HOF.TO l)) (offF HOF.PL (HOF.PLO l)) = true :=
  allN_spec orb_hds l hl

theorem cwords_lt : ∀ l < 10, ∀ j ∈ heDClassWords.getD l [], j < heDGens.size := by
  decide

theorem rep_eq {l : Nat} (hl : l < 10) :
    wordTabS 105 heDGens (heDClassWords.getD l []) = unpack 105 7 (HOF.R l) := by
  obtain ⟨hr, -⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  rw [Nat.eq_of_beq_eq_true hr, lget2_eq]
  exact (wordTabK_eq idTab_eq base.2.1 _ (fun j hj => by
    have hj5 : j < 5 := by simpa [heDGens] using cwords_lt l hl j hj
    exact ⟨dgens_get hj5, (dg_facts hj5).2.1⟩)).1

theorem orbits_get {l : Nat} (hl : l < 10) : heDOrbits[l]! = orbitBFS 105 heDGens heDInvs
    (wordTabS 105 heDGens (heDClassWords.getD l [])) 5000 := by
  rw [getElem!_pos heDOrbits l (by simp [heDOrbits]; omega)]
  simp [heDOrbits]

theorem orb_enum {l : Nat} (hl : l < 10) : heDOrbits[l]! = orbRec l ∧
    treeOK (conjStep 105 heDGens heDInvs) heDGens.size
      (wordTabS 105 heDGens (heDClassWords.getD l [])) (orbRec l) = true := by
  rw [orbits_get hl]
  exact penumK_conj_sound base.1 fg_ok fgi_ok (rep_eq hl) (orb_hd hl) (fun _ hi => orb_pt hl hi)

theorem nget_getD' (L : List Nat) (i : Nat) : nget L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem orb_size {l : Nat} (hl : l < 10) : (orbRec l).tabs.size = heDClassSizes.getD l 0 := by
  obtain ⟨-, hc⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  simp only [orbRec, penumRec, Array.size_ofFn]
  rw [Nat.eq_of_beq_eq_true hc, nget_getD']

theorem orb_get {l q : Nat} (hl : l < 10) (hq : q < HOF.C l) :
    (orbRec l).tabs[q]! = unpack 105 7 (offF HOF.T (HOF.TO l) q) ∧
      canonK 105 7 (mask 7) (105 * 7) (offF HOF.T (HOF.TO l) q) = true := by
  refine ⟨?_, penumPt_canon (orb_pt hl hq)⟩
  rw [getElem!_pos _ q (by simp [orbRec, penumRec, hq])]
  simp [orbRec, penumRec]

theorem root_canon {l : Nat} (hl : l < 10) : canonK 105 7 (mask 7) (105 * 7) (HOF.R l) = true := by
  have hh := orb_hd hl
  unfold penumHdK at hh
  obtain ⟨h0, -, hr, -⟩ := (by simpa only [bAnd_iff] using hh :
    Nat.blt 0 (HOF.C l) = true ∧ Nat.ble (HOF.C l) 5000 = true ∧
      Nat.beq (offF HOF.T (HOF.TO l) 0) (HOF.R l) = true ∧
      Nat.beq (CFSG.KS.PEnum.r32 (offF HOF.PL (HOF.PLO l)) 0) 0 = true)
  rw [← Nat.eq_of_beq_eq_true hr]
  exact (orb_get hl (Eq.mp Nat.blt_eq h0)).2

set_option maxRecDepth 400000 in
theorem sizes_sums : ∀ U : Finset (Fin 10), 0 ∈ U → (∑ l ∈ U, heDClassSizes.getD l 0) ∣ 20160 →
    U = {0} ∨ U = Finset.univ := by
  decide +kernel

theorem facts2275 : (incListOK 8330 105 heOmega0 = true ∧
      (∀ j < 9, permChk 105 heKGens[j]! = true ∧ heKGens[j]!.size = 105 ∧
        agreeOK 105 (heInnerC0 j) heOmega0 heKGens[j]! = true) ∧
      (∀ j < 5, ∀ i ∈ heDWords.getD j [], i < 9))
    ∧ (enumOK 105 heKGens heKEnum = true ∧ heKEnum.tabs.size = 40320)
    ∧ (enumOK 105 heDGens heDEnum = true ∧ heDEnum.tabs.size = 20160 ∧
      normalOK 105 heDEnum.tabs heKGens heKInvs heDGens = true)
    ∧ (heDOrbits.size = 10 ∧ heDGens.size = 5 ∧
      (∀ l < 10, orbitOK 105 heDGens heDInvs (wordTabS 105 heDGens (heDClassWords.getD l []))
        heDOrbits[l]! = true ∧ heDOrbits[l]!.tabs.size = heDClassSizes.getD l 0) ∧
      (∀ l < 10, ∀ l' < 10, l ≠ l' →
        notInOK heDOrbits[l]!.tabs (wordTabS 105 heDGens (heDClassWords.getD l' [])) = true) ∧
      (∀ l < 10, ∀ j ∈ heDClassWords.getD l [], j < heDGens.size) ∧
      wordTabS 105 heDGens (heDClassWords.getD 0 []) = idTab 105)
    ∧ (coverAllOK heDEnum.tabs heDOrbits = true)
    ∧ (∀ U : Finset (Fin 10), 0 ∈ U →
      (∑ l ∈ U, heDClassSizes.getD l 0) ∣ 20160 → U = {0} ∨ U = Finset.univ) := by
  refine ⟨⟨inc_ok, k_first, dwords_lt⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨by simp [heDOrbits], rfl, fun l hl => ?_, fun l hl l' hl' hne => ?_, cwords_lt, rfl⟩, ?_,
    sizes_sums⟩
  · rw [k_enum.1]
    exact k_enum.2
  · rw [k_enum.1]
    simp [penumRec]
    rfl
  · rw [d_enum.1]
    exact d_enum.2
  · rw [d_enum.1]
    simp [penumRec]
    rfl
  · rw [d_enum.1]
    exact normal
  · obtain ⟨e, ht⟩ := orb_enum hl
    rw [e]
    refine ⟨?_, orb_size hl⟩
    unfold orbitOK
    rw [invsD, ht]
    rfl
  · rw [(orb_enum hl).1, rep_eq hl']
    unfold notInOK allBelow
    rw [all_range_iff]
    intro q hq
    have hq' : q < HOF.C l := by simpa [orbRec, penumRec] using hq
    obtain ⟨hg, hc⟩ := orb_get hl hq'
    rw [hg, beq_unpack hc (root_canon hl')]
    have hn := allN_spec (allN_spec notin l hl) l' hl'
    have hb : Nat.beq l l' = false := by
      cases h : Nat.beq l l'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hne
    rw [hb] at hn
    have hz := allN_spec hn q hq'
    cases h : Nat.beq (offF HOF.T (HOF.TO l) q) (HOF.R l')
    · rfl
    · rw [h] at hz
      exact absurd hz (by decide)
  · rw [d_enum.1]
    unfold coverAllOK allBelow
    rw [all_range_iff]
    intro k hk
    have hk' : k < HDE.cnt := by simpa [penumRec] using hk
    have hc := cover_all (k := k) hk'
    unfold coverK at hc
    simp only [strictB_app'] at hc
    obtain ⟨hl, hq, he⟩ := (by simpa only [bAnd_iff] using hc :
      Nat.blt (Nat.shiftRight (HCOV k) 16) 10 = true ∧
      Nat.blt (Nat.land (HCOV k) 65535) (HOF.C (Nat.shiftRight (HCOV k) 16)) = true ∧
      Nat.beq (offF HOF.T (HOF.TO (Nat.shiftRight (HCOV k) 16)) (Nat.land (HCOV k) 65535))
        (HDE.T k) = true)
    have hl' := Eq.mp Nat.blt_eq hl
    unfold anyBelow
    rw [List.any_eq_true]
    have hsz : Nat.shiftRight (HCOV k) 16 < heDOrbits.size := by simpa [heDOrbits] using hl'
    refine ⟨Nat.shiftRight (HCOV k) 16, List.mem_range.2 hsz, ?_⟩
    rw [CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ hsz, (orb_enum hl').1, rec_get hk']
    exact penum_found_sound (fun _ hx => orb_pt hl' hx) (Eq.mp Nat.blt_eq hq)
      (Nat.eq_of_beq_eq_true he)

end CertificateChecks.KernelSpor.HeL

end
