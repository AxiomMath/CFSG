module

public import Certificates.Kernel.Sporadic.OddCore.Suz23000K
public import Certificates.Kernel.Sporadic.SuzInv.Inner0
public import Certificates.Kernel.Sporadic.SuzInv.Full0
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz23000

open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.CatFactsL4U4.SuzCS
open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.KS.Mathieu CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzCT

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem notB_beq {a b : Nat} (h : notB (Nat.beq a b) = true) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · rw [e] at h
    exact absurd h (by decide)

theorem betaK_parts : (∀ h < 23, cn (GH h) = true) ∧ cn BK = true ∧
    (∀ a < 42, Nat.beq (pg 11 (mask 11) BK (nget fix0L a)) (nget fix0L a) = true) ∧
    Nat.beq BK (pidn 1782 11) = false ∧ Nat.beq BK (SuzTP 0) = false ∧
    (∀ k < 22, (Nat.beq (pc (GH (k + 1)) BK) (pc BK (GH (k + 1))) ||
      Nat.beq (pc (GH (k + 1)) BK) (pc (pc (SuzTP 0) BK) (GH (k + 1)))) = true) ∧
    Nat.beq (pc (GH 5) BK) (pc BK (GH 5)) = false := by
  have h := betaK
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨allN_spec h1, h2, allN_spec h3, notB_beq h4, notB_beq h5, fun k hk => ?_, notB_beq h7⟩
  have e := allN_spec h6 k hk
  rw [OddCore.strictB_app] at e
  cases e1 : Nat.beq (pc (GH (k + 1)) BK) (pc BK (GH (k + 1)))
  · rw [e1] at e
    simpa using e
  · rfl

theorem gh_get {h : Nat} (h1 : 1 ≤ h) (h2 : h ≤ 22) :
    (invInnerGenArrs 0)[h - 1]! = unpack 1782 11 (GH h) := by
  rw [SuzInv.gensI0.2 (h - 1) (by omega)]
  unfold GH
  congr 2
  change 32 + (h - 1) = 31 + h
  omega

theorem pid_canon : cn (pidn 1782 11) = true := (PP.id (n := 1782) (w := 11) rfl).1

theorem innerWordArr_eq : ∀ w : List Nat, (∀ h ∈ w, 1 ≤ h ∧ h ≤ 22) →
    innerWordArr 0 w = unpack 1782 11 (wordTabK 1782 11 (mask 11) (pidn 1782 11) GH w) ∧
      cn (wordTabK 1782 11 (mask 11) (pidn 1782 11) GH w) = true
  | [], _ => ⟨idA_eq (n := 1782) (w := 11) rfl, pid_canon⟩
  | h :: rest, hw => by
    obtain ⟨ih1, ih2⟩ := innerWordArr_eq rest fun h' hh' => hw h' (List.mem_cons_of_mem h hh')
    have hh := hw h List.mem_cons_self
    have hc : cn (GH h) = true := betaK_parts.1 h (by omega)
    have e : wordTabK 1782 11 (mask 11) (pidn 1782 11) GH (h :: rest) =
        pc (GH h) (wordTabK 1782 11 (mask 11) (pidn 1782 11) GH rest) := by
      change strictN (wordTabK 1782 11 (mask 11) (pidn 1782 11) GH rest) (fun acc => pc (GH h) acc) = _
      rw [strictN_app']
    have e2 : innerWordArr 0 (h :: rest) = compA 1782 (invInnerGenArrs 0)[h - 1]! (innerWordArr 0 rest) :=
      rfl
    rw [e, e2, ih1, gh_get hh.1 hh.2]
    exact ⟨compA_unpack hc ih2, canonK_pcomp hc ih2⟩

theorem betaWord_ok : ∀ h ∈ betaWord, 1 ≤ h ∧ h ≤ 22 := by decide

theorem betaArr_eq : betaArr = unpack 1782 11 BK := (innerWordArr_eq betaWord betaWord_ok).1

theorem t0_eq : tArr 0 = unpack 1782 11 (SuzTP 0) := (OddCore.rep_facts (i := 0) (by norm_num)).1

theorem t0_canon : cn (SuzTP 0) = true := (OddCore.rep_facts (i := 0) (by norm_num)).2.1

theorem gen_get {k : Nat} (hk : k < 22) : (invInnerGenArrs 0)[k]! = unpack 1782 11 (GH (k + 1)) := by
  have := gh_get (h := k + 1) (by omega) (by omega)
  simpa using this

theorem betaOK_true : betaOK = true := by
  obtain ⟨hG, hB, hfix, hid, ht, hconj, h4⟩ := betaK_parts
  have hsz : (invInnerGenArrs 0).size = 22 := SuzInv.gensI0.1
  unfold betaOK
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hsz]
    decide
  · rw [fix_eq0, List.all_eq_true]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hx
    have hlt := fix0_facts.2.2 _ hx
    have e := hfix a (by rw [← fix0_facts.1]; exact ha)
    rw [nget_get fix0L ha] at e
    rw [betaArr_eq, unpack_getElem!, if_pos hlt, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true e
  · rw [betaArr_eq, idA_eq (n := 1782) (w := 11) rfl, eqA_unpack hB pid_canon]
    exact hid
  · rw [betaArr_eq, t0_eq, eqA_unpack hB t0_canon]
    exact ht
  · rw [hsz]
    simp only [allBelow, List.all_eq_true, List.mem_range]
    intro k hk
    have hg := hG (k + 1) (by omega)
    unfold betaConjOK tBetaArr
    rw [gen_get hk, betaArr_eq, t0_eq, compA_unpack hg hB, compA_unpack hB hg,
      compA_unpack t0_canon hB, compA_unpack (canonK_pcomp t0_canon hB) hg,
      eqA_unpack (canonK_pcomp hg hB) (canonK_pcomp hB hg),
      eqA_unpack (canonK_pcomp hg hB) (canonK_pcomp (canonK_pcomp t0_canon hB) hg)]
    exact hconj k hk
  · have hg := hG 5 (by norm_num)
    rw [gen_get (k := 4) (by norm_num), betaArr_eq, compA_unpack hg hB, compA_unpack hB hg,
      eqA_unpack (canonK_pcomp hg hB) (canonK_pcomp hB hg)]
    exact h4

theorem outer_eq : outerArr = unpack 1782 11 OK7 := SuzInv.gensF0.2 6 (by norm_num)

theorem notIn_all {s : Nat} (hs : s < 8) : notInSl s = true := by
  interval_cases s
  · exact notIn0
  · exact notIn1
  · exact notIn2
  · exact notIn3
  · exact notIn4
  · exact notIn5
  · exact notIn6
  · exact notIn7

theorem og_not_found (hcG : canonK 42 6 (mask 6) (42 * 6) OG = true) :
    found (indexOf (penumRec 42 6 K0E.cnt K0E.T K0E.PL).tabs) (penumRec 42 6 K0E.cnt K0E.T K0E.PL).tabs
      (unpack 42 6 OG) = false := by
  cases e : found (indexOf (penumRec 42 6 K0E.cnt K0E.T K0E.PL).tabs)
      (penumRec 42 6 K0E.cnt K0E.T K0E.PL).tabs (unpack 42 6 OG)
  · rfl
  · obtain ⟨i, hi, hT⟩ := (found_penumRec_iff (fun _ hj => kpt_all hj) hcG).1 e
    have hc40 : K0E.cnt = 40320 := rfl
    have hi40 : i < 40320 := by rwa [hc40] at hi
    have h := allN_spec (notIn_all (s := i / 5040) (by omega)) (i % 5040) (Nat.mod_lt _ (by norm_num))
    have hi2 : Nat.add (Nat.mul 5040 (i / 5040)) (i % 5040) = i := Nat.div_add_mod i 5040
    rw [hi2, hT, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem outerOK_true : outerOK = true := by
  have k := outerK
  simp only [bAnd_iff] at k
  obtain ⟨hc, hs, hsig⟩ := k
  have hcG := (sig_facts hsig).1
  unfold outerOK
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  refine ⟨⟨by rw [SuzInv.gensF0.1]; norm_num, ?_⟩, ?_⟩
  · rw [OddCore.inM_eq outer_eq hc]
    cases e : OddCore.msift OK7
    · rfl
    · rw [e] at hs
      exact absurd hs (by decide)
  · rw [fix_eq0, outer_eq, restrict_eq fix0_facts.1 fix0_facts.2.1 fix0_facts.2.2 hsig, k_enum.1]
    unfold notInOK
    simp only [allBelow, List.all_eq_true, List.mem_range, Bool.not_eq_true']
    intro k hk
    have hnf := og_not_found hcG
    cases e : ((penumRec 42 6 K0E.cnt K0E.T K0E.PL).tabs[k]! == unpack 42 6 OG)
    · rfl
    · have hf := (found_indexOf_iff _ _).2 ⟨k, hk, beq_iff_eq.1 e⟩
      rw [hnf] at hf
      exact absurd hf (by decide)

theorem pw_eq {w : List Nat} (hw : ∀ j ∈ w, j < 5) : wordTab 42 dGens w = unpack 42 6 (PW w) ∧
    canonK 42 6 (mask 6) (42 * 6) (PW w) = true :=
  wordTabK_eq idTab42 base.2.1 w fun j hj => ⟨dgens_get (hw j hj), (dg_facts (hw j hj)).2.1⟩

theorem letters_of {w : List Nat} (h : w.all (fun j => Nat.blt j 5) = true) : ∀ j ∈ w, j < 5 :=
  fun j hj => Nat.blt_eq.mp (List.all_eq_true.1 h j hj)

theorem pinOK_true : pinOK = true := by
  have k := pinK
  simp only [bAnd_iff] at k
  obtain ⟨hl, hp⟩ := k
  unfold pinOK
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow, List.all_eq_true, List.mem_range]
  refine ⟨Nat.eq_of_beq_eq_true hl, fun p hp42 => ?_⟩
  obtain ⟨hA, hB⟩ := (bAnd_iff _ _).1 (allN_spec hp p hp42)
  have hA' := List.all_eq_true.1 hA
  refine ⟨fun w hw => ?_, fun q hq => ?_⟩
  · obtain ⟨hlet, hfix⟩ := (bAnd_iff _ _).1 (hA' w hw)
    have hj := letters_of hlet
    refine ⟨fun j hjw => ?_, ?_⟩
    · rw [dGens_size', decide_eq_true_eq]
      exact hj j hjw
    · rw [(pw_eq hj).1, unpack_getElem!, if_pos hp42]
      exact Nat.eq_of_beq_eq_true hfix
  · have e := allN_spec hB q hq
    by_cases hqp : q = p
    · simp [hqp]
    · have hb : Nat.beq q p = false := by
        cases h : Nat.beq q p
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hqp
      rw [hb] at e
      obtain ⟨w, hw, hmv⟩ := List.any_eq_true.1 e
      have hj := letters_of ((bAnd_iff _ _).1 (hA' w hw)).1
      rw [Bool.or_eq_true]
      right
      rw [List.any_eq_true]
      refine ⟨w, hw, ?_⟩
      rw [(pw_eq hj).1, unpack_getElem!, if_pos hq, bne_iff_ne, ne_eq]
      intro he
      rw [he, Nat.beq_refl] at hmv
      exact absurd hmv (by decide)

theorem check23000 : betaOK = true ∧ outerOK = true ∧ pinOK = true :=
  ⟨betaOK_true, outerOK_true, pinOK_true⟩

end CertificateChecks.KernelSpor.Suz23000

end
