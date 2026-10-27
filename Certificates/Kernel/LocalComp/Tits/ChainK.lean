module

public import Certificates.Kernel.LocalComp.Tits.Chain0a
public import Certificates.Kernel.LocalComp.Tits.Chain0b
public import Certificates.Kernel.LocalComp.Tits.Chain1
public import Certificates.Kernel.LocalComp.Tits.ChainBfs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.Tits

open CFSG.KC.Enum CFSG.KS CFSG.KC.LocalComp.Tits CFSG.KC.LocalComp.TitsChain
open CFSG.SectionRank.Native.Tits CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem kLetters : lettersOK TG TL chainWords = true := by quickRfl

theorem kGens : allN 4 (fun s => permOK 1755 11 (mask 11) (1755 * 11) (TG s)
    (pinvS 1755 11 (mask 11) (TG s))) = true := by quickRfl

theorem kPairs : allN 14 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TL (2 * j))
    (TL (2 * j + 1))) = true := by quickRfl

theorem kLevel0 : levelOK 56 TL TTf TSf TWf szf CP 0 = true := by quickRfl

theorem kLevel1 : levelOK 56 TL TTf TSf TWf szf CP 1 = true := by quickRfl

theorem kLevel2 : levelOK 56 TL TTf TSf TWf szf CP 2 = true := by quickRfl

theorem kLevel3 : levelOK 56 TL TTf TSf TWf szf CP 3 = true := by quickRfl

theorem kTerminal : terminalOK 56 TL CP = true := by quickRfl

theorem kSpan : spanK TP CP TM = true := by quickRfl

theorem kCPV : ∀ t < CP.length, CP.getD t 0 < 1755 ∧ TP (CP.getD t 0) < 2 ^ 52 := by
  decide +kernel

theorem letters_eq : chainLetters = Array.ofFn (n := 28) fun l => tabP 1755 (TL l.val) :=
  letters_sound gens_eq kLetters

theorem chainFacts :
    chainOK 1755 chainLetters chainBase checkPts checkBase chainTreesT 3 = true ∧
      orbitSizes chainTreesT = (List.range 4).map szf :=
  chain_sound (TT := TTf) (TS := TSf) (TW := TWf) letters_eq (fun j hj => allN_spec kPairs j hj)
    rfl (fun t ht => (kCPV t ht).1) base_eq check_eq (by simp [checkBase, chainBase, baseVecs])
    (fun i hi => by
      match i, hi with
      | 0, _ => exact kLevel0
      | 1, _ => exact kLevel1
      | 2, _ => exact kLevel2
      | 3, _ => exact kLevel3)
    kBfs kDepth
    (fun i hi c hc => by
      change schC i c = true
      rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h2
      · rcases Nat.lt_or_ge c 14 with h | h
        · exact sch0a c h
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' h
          exact sch0b d (by omega)
      · exact sch1 c hc
      · exact sRest i hi c hc (Or.inr h2))
    kTerminal

theorem h1 : orbitOK nPts orbitPts genCols genTables = true := by
  rw [pts_eq, gens_eq]
  exact (orbit_sound kOrbit).2.2

theorem h3 : allIn 0 4 (fun s => invOK nPts genTables[s]! (invT nPts genTables[s]!)) = true := by
  rw [gens_eq]
  have e : ∀ s < 4, invOK 1755 (tabP 1755 (TG s)) (invT 1755 (tabP 1755 (TG s))) = true :=
    fun s hs => invOK_tabP (allN_spec kGens s hs) (by decide)
  simp only [allIn, Nat.all_succ, Nat.all_zero, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact e 0 (by decide)
  · exact e 1 (by decide)
  · exact e 2 (by decide)
  · exact e 3 (by decide)

theorem h7 : spanOK checkVecs (spanMasks checkVecs) = true := by
  change spanOK (checkPts.map fun i => orbitPts[i]!) (spanMasks (checkPts.map fun i => orbitPts[i]!)) =
    true
  rw [check_eq, pts_eq]
  exact span_sound kCPV kSpan

theorem h8 : allIn 0 4 (fun s => chainWords[s]! == [(s : Int) + 1]) = true := by
  simp only [allIn, Nat.all_succ, Nat.all_zero, Bool.true_and]
  decide

theorem chain : titsChainCheck = true := by
  have h5 : chainOK nPts chainLetters chainBase checkPts checkBase chainTreesT 3 = true :=
    chainFacts.1
  have h6 : (orbitSizes chainTreesT == [1755, 1024, 5, 4]) = true := by
    rw [chainFacts.2]
    rfl
  have h4 : (chainBase.size == 4) = true := by simp [chainBase, baseVecs]
  have h2 : ((genCols ()).size == 4) = true := rfl
  simp only [titsChainCheck, h1, h2, h3, h4, h5, h6, h7, h8, Bool.and_self]

end CertificateChecks.KernelLC.Tits
