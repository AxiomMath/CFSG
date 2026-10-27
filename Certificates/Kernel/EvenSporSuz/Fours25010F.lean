module

public import Certificates.Kernel.EvenSporSuz.Fours25010
public import CFSG.Certificates.Kernel.EvenSporSuz.OuterSound
public import CFSG.Certificates.Kernel.EvenSporSuz.CoverSound
public import Certificates.Kernel.Sporadic.OddCore.Suz26990F
import Certificates.Kernel.EvenSporSuz.Bridge
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz

theorem fwLines : foursWitnessLines = fwW.toArray := by
  unfold foursWitnessLines fwW
  rw [FW.eq, lines_ofList, List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun L hL => ?_
  exact outerParseWord_ofList L (List.all_eq_true.1 ch25010M_lines L hL)

theorem fw_getD (i : ℕ) : foursWitnessLines.getD i [] = fwW.getD i [] := by
  rw [fwLines, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem fwX : foursWitnessX = fwW.getD 0 [] := fw_getD 0

theorem fwL2 : foursWitnessL 2 = fwW.getD 1 [] := fw_getD 1

theorem fwC2 : foursWitnessC 2 = fwW.getD 2 [] := fw_getD 2

theorem fwL3 : foursWitnessL 3 = fwW.getD 3 [] := fw_getD 3

theorem fwC3 : foursWitnessC 3 = fwW.getD 4 [] := fw_getD 4

theorem lvl0Canon : CanonGS outerLvl0 := by
  refine ⟨canonB_getD fun x hx => ?_, canonB_getD fun x hx => ?_⟩
  · simp only [outerLvl0, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact canonB_mulM _ _
  · simp only [outerLvl0, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact canonB_invM _

theorem lvl0Mats : outerLvl0.mats.toList.map rowsOf = l0M := by
  simp only [outerLvl0, l0M, List.map_cons, List.map_nil]
  rw [rowsOf_mulM canonB_negM hA, rowsOf_mulM canonB_negM hB, rowsOf_negM, rowsA, rowsB]

theorem lvl0Invs : outerLvl0.invs.toList.map rowsOf = l0I := by
  simp only [outerLvl0, l0I, l0M, List.map_cons, List.map_nil]
  rw [rowsOf_invM (canonB_mulM _ _), rowsOf_invM (canonB_mulM _ _), rowsOf_mulM canonB_negM hA,
    rowsOf_mulM canonB_negM hB, rowsOf_negM, rowsA, rowsB]

theorem lvl0Valid : outerLvl0.valid = true := by
  rw [valid_eq lvl0Canon, lvl0Mats, lvl0Invs]
  exact ch25010M_valid

theorem lvl0Sq :
    (mulM (outerLvl0.eval (foursWitnessX.map zCode)) (outerLvl0.eval (foursWitnessX.map zCode)) ==
      oneM) = true := by
  rw [beq_rows (canonB_mulM _ _) canonB_oneM, rowsOf_mulM (canonB_eval _ _) (canonB_eval _ _),
    rowsOf_eval lvl0Canon, lvl0Mats, lvl0Invs, rowsOf_oneM, fwX]
  exact ch25010M_sq

theorem fwLetters (i : ℕ) (hi : i < 5) :
    CFSG.Monster.B.Co2.Native.lettersOK 2 (fwW.getD i []) = true :=
  List.all_eq_true.1 ch25010M_letters i (List.mem_range.2 hi)

end CertificateChecks.KernelSuz

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSuz
open CFSG.EvenSporadicStandard.TwoSuz CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
open CFSG.KLie.CT (andB orB notB)

attribute [local irreducible] idA

theorem pair_bind : (#[b0Arr, b1Arr] : Array (Array Nat)).size = 2 ∧
    ∀ j < 2, (#[b0Arr, b1Arr] : Array (Array Nat))[j]! = unpack 1782 11 (triS j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [← tri_bind.2 j (by omega)]
  interval_cases j <;> rfl

theorem fourArr {w : List Int} (hl : lettersK 2 w = true) :
    foursWordArr w = unpack 1782 11 (W3 w) := by
  unfold foursWordArr wordArr W3
  exact word_of pair_bind (fun j hj => tri_p j (by omega)) hl

theorem fparts (i : Nat) (hi : i < 5) :
    foursWordArr (fwW.getD i []) = unpack 1782 11 (F i) ∧
      foursWordArr (outerInvW (fwW.getD i [])) = unpack 1782 11 (FI i) ∧ Cn (F i) ∧ Cn (FI i) := by
  have hl := List.all_eq_true.1 ch25010P_letters i (List.mem_range.2 hi)
  have hc := List.all_eq_true.1 ch25010P_canon i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at hl hc
  exact ⟨fourArr hl.1, fourArr hl.2, hc.1, hc.2⟩

theorem permOK2 : foursWitnessPermOK 2 = true := by
  obtain ⟨hT, cT, hsq, -, -⟩ := rep_facts (i := 2) (by decide)
  obtain ⟨h0, -, c0, -⟩ := fparts 0 (by decide)
  obtain ⟨h1, h1i, c1, c1i⟩ := fparts 1 (by decide)
  obtain ⟨h2, h2i, c2, c2i⟩ := fparts 2 (by decide)
  unfold foursWitnessPermOK
  rw [hsq, fwL2, fwC2, fwX, h0, h1, h1i, h2, h2i, hT, compA_u c1 cT, compA_u (cpc c1 cT) c1i,
    compA_u (cpc (cpc c1 cT) c1i) cT, compA_u c2 c0, compA_u (cpc c2 c0) c2i,
    eqA_u (cpc (cpc (cpc c1 cT) c1i) cT) (cpc (cpc c2 c0) c2i), ch25010P_t2]
  rfl

theorem permOK3 : foursWitnessPermOK 3 = true := by
  obtain ⟨hT, cT, hsq, -, -⟩ := rep_facts (i := 3) (by decide)
  obtain ⟨h0, -, c0, -⟩ := fparts 0 (by decide)
  obtain ⟨h1, h1i, c1, c1i⟩ := fparts 3 (by decide)
  obtain ⟨h2, h2i, c2, c2i⟩ := fparts 4 (by decide)
  unfold foursWitnessPermOK
  rw [hsq, fwL3, fwC3, fwX, h0, h1, h1i, h2, h2i, hT, compA_u c1 cT, compA_u (cpc c1 cT) c1i,
    compA_u (cpc (cpc c1 cT) c1i) cT, compA_u c2 c0, compA_u (cpc c2 c0) c2i,
    eqA_u (cpc (cpc (cpc c1 cT) c1i) cT) (cpc (cpc c2 c0) c2i), ch25010P_t3]
  rfl

theorem xNe : (!eqA 1782 (foursWordArr foursWitnessX) (idA 1782)) = true := by
  obtain ⟨h0, -, c0, -⟩ := fparts 0 (by decide)
  rw [fwX, h0, hidA, eqA_u c0 cE, ch25010P_x]
  rfl

theorem check25010 : foursWitnessCheck = true := by
  unfold foursWitnessCheck
  rw [lvl0Valid, lvl0Sq, xNe, permOK2, permOK3, fwX, fwL2, fwC2, fwL3, fwC3,
    fwLetters 0 (by decide), fwLetters 1 (by decide), fwLetters 2 (by decide),
    fwLetters 3 (by decide), fwLetters 4 (by decide)]
  rfl

end CertificateChecks.KernelSpor.S26990

end
