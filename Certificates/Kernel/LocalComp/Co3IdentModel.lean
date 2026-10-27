module

public import Certificates.Kernel.LocalComp.Co3IdentHR
public import Certificates.Kernel.LocalComp.Co3IdentCR
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CertificateChecks.KernelLC CertificateChecks.KernelSpor CFSG.Sporadic.Schreier.Co3.Native

theorem eqA_self (t : Array Nat) : eqA 276 t t = true := by
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem gsize : gArrs.size = 3 := by simp [gArrs]

theorem msize : mGenArrs.size = 7 := by
  unfold mGenArrs
  rw [Array.size_extract, Co3M.binds.2.2.2.1]
  rfl

theorem mGen_eq (i : Nat) (hi : i < 7) : mGenArrs[i]! = unpack 276 9 (Co3M.S i) := by
  have hs : co3MArrs.size = 14 := Co3M.binds.2.2.2.1
  have e : mGenArrs[i]! = co3MArrs[i]! := by
    unfold mGenArrs
    simp [getElem!_def, hs, hi]
    rw [Array.getElem?_eq_getElem (by rw [hs]; omega)]
  rw [e, mS_eq i hi]

theorem mGenI_eq (i : Nat) (hi : i < 7) :
    (mGenArrs.map (invCand 276))[i]! = unpack 276 9 (Co3M.SI i) := by
  have h1 : i < (mGenArrs.map (invCand 276)).size := by rw [Array.size_map, msize]; exact hi
  rw [getElem!_pos _ i h1, Array.getElem_map, ← getElem!_pos mGenArrs i (by rw [msize]; exact hi),
    mGen_eq i hi]
  exact (invEqK_sound (allN_spec Co3M.perm i (by omega))).1

theorem e0 : HR.E 0 = pidn 276 9 := Nat.eq_of_beq_eq_true kRootE

theorem ce0 : CR.E 0 = P0 := Nat.eq_of_beq_eq_true kCRootE

theorem treeTab : treeTabOK 276 gArrs hPar hLab hList 4608 = true := by
  unfold treeTabOK
  rw [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hList_get 0 (by omega), e0, idK_sound kId]
    exact eqA_self _
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · have hs := (hAll_spec j (by rw [hc]; exact hj)).2.1 hj0
      unfold stepR at hs
      obtain ⟨h1, hs⟩ := (bAnd_iff _ _).1 hs
      obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 hs
      have hp : HR.P j < j := Nat.le_of_ble_eq_true h1
      have hl : HR.L j < 3 := Nat.le_of_ble_eq_true h2
      rw [hPar_get j hj, hLab_get j hj, hList_get j hj, hList_get (HR.P j) (by omega),
        g_eq (HR.L j) hl, prodOK_eq h3, gsize]
      simp [hp, hl, eqA_self]

theorem hKeys : keysOK [0, 1] hList 4608 = true := by
  refine keysOK_of_inj fun a b ha hb e => ?_
  rw [hList_get a ha, hList_get b hb, keyOf_unpack2, keyOf_unpack2] at e
  exact inj_of_sort (fun m hm => (hAll_spec m hm).2.2.2.1) a b (by rw [hc]; exact ha)
    (by rw [hc]; exact hb) e

theorem mInv (i : Nat) (hi : i < 7) :
    isInvA 276 mGenArrs[i]! (invCand 276 mGenArrs[i]!) = true := by
  obtain ⟨e1, e2⟩ := invEqK_sound (allN_spec Co3M.perm i (by omega))
  rw [mGen_eq i hi, e1]
  exact e2

theorem conjTab : conjTabOK 276 mGenArrs (mGenArrs.map (invCand 276)) cBFS.2.1 cBFS.2.2 cBFS.1
    (genArr 0) 630 = true := by
  unfold conjTabOK
  rw [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [cList_get 0 (by omega), ce0, ← bind0]
    exact eqA_self _
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · have hs := (cAll_spec j (by rw [cc]; exact hj)).2.1 hj0
      unfold stepC at hs
      obtain ⟨h1, hs⟩ := (bAnd_iff _ _).1 hs
      obtain ⟨h2, hs⟩ := (bAnd_iff _ _).1 hs
      rw [CFSG.KC.Fendel.strictB_eq] at hs
      obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 hs
      have hp : CR.P j < j := Nat.le_of_ble_eq_true h1
      have hl : CR.L j < 7 := Nat.le_of_ble_eq_true h2
      rw [cPar_get j hj, cLab_get j hj, cList_get j hj, cList_get (CR.P j) (by omega),
        mGen_eq (CR.L j) hl, mGenI_eq (CR.L j) hl, prodOK_eq h3, prodOK_eq h4, msize]
      simp [hp, hl, eqA_self]

theorem cKeys : keysOK [0, 1, 2, 3] cBFS.1 630 = true := by
  refine keysOK_of_inj fun a b ha hb e => ?_
  rw [cList_get a ha, cList_get b hb, keyOf_unpack4, keyOf_unpack4] at e
  exact inj_of_sort (fun m hm => (cAll_spec m hm).2.2.2.1) a b (by rw [cc]; exact ha)
    (by rw [cc]; exact hb) e

theorem kEdge : allN 6 (fun k => bAnd(wordOK (pos (edgeFirst k)),
    commK 276 9 (mask 9) (276 * 9) (wordP (pos (edgeFirst k))) P0)) = true := by quickRfl

theorem edgeComm (k : Nat) (hk : k < 6) :
    commutesA 276 (posArr (edgeFirst k)) (genArr 0) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kEdge k hk)
  unfold posArr
  rw [wordArr_eq _ h1, bind0]
  exact commK_sound h2

theorem facts3093 : treeTabOK 276 gArrs hPar hLab hList 4608 = true ∧
    keysOK [0, 1] hList 4608 = true ∧
    (∀ i < 7, isInvA 276 mGenArrs[i]! (invCand 276 mGenArrs[i]!) = true) ∧
    conjTabOK 276 mGenArrs (mGenArrs.map (invCand 276)) cBFS.2.1 cBFS.2.2 cBFS.1 (genArr 0)
      630 = true ∧
    keysOK [0, 1, 2, 3] cBFS.1 630 = true ∧
    (∀ k < 6, commutesA 276 (posArr (edgeFirst k)) (genArr 0) = true) :=
  ⟨treeTab, hKeys, mInv, conjTab, cKeys, edgeComm⟩

end CertificateChecks.KernelLC.Co3Id

end
