module

public import Certificates.Kernel.LocalComp.Fi24TwoB.Ch15027
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC
open CFSG.Sporadic.FischerOddCore (fi24KStrong)
open CFSG.RankThree.Native (commutatorA)

@[expose] noncomputable def letK (z : Int) : Nat :=
  if z = 1 then Fi24KC.S 0 else if z = -1 then Fi24KC.SI 0 else if z = 2 then Fi24KC.S 1
  else Fi24KC.SI 1

@[expose] noncomputable def wordK (w : List Int) : Nat :=
  w.foldr (fun z t => pcomp 504 9 (mask 9) (letK z) t) (pidn 504 9)

theorem kIdK : idK 504 9 (mask 9) = true := by quickRfl

theorem kIdC : canonK 504 9 (mask 9) (504 * 9) (pidn 504 9) = true := by quickRfl

theorem strongK {j : Nat} (hj : j < 12) : fi24KStrong[j]! = unpack 504 9 (Fi24KC.S j) := by
  rw [kS]
  exact ofFn_get hj

theorem letter_eq (z : Int) : fi24KLetterA z = unpack 504 9 (letK z) ∧ Cn 504 9 (letK z) := by
  obtain ⟨c0, ci0, p0⟩ := cnK' 0 (by norm_num)
  obtain ⟨c1, ci1, p1⟩ := cnK' 1 (by norm_num)
  unfold fi24KLetterA letK
  split_ifs
  · exact ⟨strongK (by norm_num), c0⟩
  · rw [strongK (by norm_num)]
    exact ⟨(invEqK_sound p0).1, ci0⟩
  · exact ⟨strongK (by norm_num), c1⟩
  · rw [strongK (by norm_num)]
    exact ⟨(invEqK_sound p1).1, ci1⟩

theorem word_eq : ∀ w : List Int, fi24KWordA w = unpack 504 9 (wordK w) ∧ Cn 504 9 (wordK w)
  | [] => by
    rw [fi24KWordA_nil]
    exact ⟨(idK_sound kIdK).symm, kIdC⟩
  | z :: w => by
    obtain ⟨ih1, ih2⟩ := word_eq w
    obtain ⟨l1, l2⟩ := letter_eq z
    rw [fi24KWordA_cons, ih1, l1, compA_unpack l2 ih2]
    exact ⟨rfl, canonK_pcomp l2 ih2⟩

theorem kGen : allN 5 (fun k => Nat.beq (Fi24BKd.S k) (wordK fi24KdGenWords[k]!)) = true := by
  quickRfl

theorem kComm : allN 10 (fun m => Nat.beq (Fi24BKdd.S m)
    (pcomp 504 9 (mask 9) (pcomp 504 9 (mask 9) (Fi24BKd.S (fi24KdPairs[m]!).1)
      (Fi24BKd.S (fi24KdPairs[m]!).2))
      (pcomp 504 9 (mask 9) (Fi24BKd.SI (fi24KdPairs[m]!).1)
        (Fi24BKd.SI (fi24KdPairs[m]!).2)))) = true := by quickRfl

theorem kCanD : allN 16 (fun j => bAnd(canonK 504 9 (mask 9) (504 * 9) (Fi24BKd.S j),
    canonK 504 9 (mask 9) (504 * 9) (Fi24BKd.SI j))) = true := by quickRfl

theorem kCanDD : allN 21 (fun j => canonK 504 9 (mask 9) (504 * 9) (Fi24BKdd.S j)) = true := by
  quickRfl

theorem pairs_lt {m : Nat} (hm : m < 10) : (fi24KdPairs[m]!).1 < 5 ∧ (fi24KdPairs[m]!).2 < 5 := by
  interval_cases m <;> decide

theorem gens_ok : ∀ k < 5, eqA 504 fi24KdStrong[k]! (fi24KWordA fi24KdGenWords[k]!) = true := by
  intro k hk
  obtain ⟨w1, w2⟩ := word_eq fi24KdGenWords[k]!
  have hc := (bAnd_iff _ _).1 (allN_spec kCanD k (by omega))
  rw [dS, ofFn_get (by omega : k < 16), w1, eqA_unpack hc.1 w2]
  exact allN_spec kGen k hk

theorem comm_ok : ∀ m < 10, eqA 504 fi24KddStrong[m]! (commutatorA 504
    fi24KdStrong[(fi24KdPairs[m]!).1]! fi24KdStrong[(fi24KdPairs[m]!).2]!) = true := by
  intro m hm
  obtain ⟨ha, hb⟩ := pairs_lt hm
  generalize ea : (fi24KdPairs[m]!).1 = a at ha
  generalize eb : (fi24KdPairs[m]!).2 = b at hb
  have hm' := allN_spec kComm m hm
  simp only [ea, eb] at hm'
  have ca := (bAnd_iff _ _).1 (allN_spec kCanD a (by omega))
  have cb := (bAnd_iff _ _).1 (allN_spec kCanD b (by omega))
  have ia := (invEqK_sound (allN_spec permD a (by omega))).1
  have ib := (invEqK_sound (allN_spec permD b (by omega))).1
  unfold commutatorA
  rw [ddS, dS, ofFn_get (by omega : m < 21), ofFn_get (by omega : a < 16),
    ofFn_get (by omega : b < 16), ia, ib, compA_unpack ca.1 cb.1, compA_unpack ca.2 cb.2,
    compA_unpack (canonK_pcomp ca.1 cb.1) (canonK_pcomp ca.2 cb.2),
    eqA_unpack (allN_spec kCanDD m (by omega))
      (canonK_pcomp (canonK_pcomp ca.1 cb.1) (canonK_pcomp ca.2 cb.2))]
  exact hm'

theorem chainsOK : fi24KdChainsOK = true := by
  unfold fi24KdChainsOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨by rw [sizeD]; norm_num, by rw [sizeDD]; norm_num⟩, chainD⟩, sizesD⟩, chainDD⟩,
    sizesDD⟩, allLt_iff.2 gens_ok⟩, allLt_iff.2 comm_ok⟩

end CertificateChecks.KernelLC.Fi24B

end
