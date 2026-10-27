module

public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Sporadic.Co3.CP
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Order

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] noncomputable def WP : Nat :=
  wordK 276 9 (mask 9) (pidn 276 9) Co3C.S Co3C.SI co3CoprimeWord

@[expose] noncomputable def WPI : Nat := pinvS 276 9 (mask 9) WP

@[expose] noncomputable def C1L : Nat := pcomp 276 9 (mask 9) WPI (Co3C.S 1)

@[expose] noncomputable def C1P : Nat := pcomp 276 9 (mask 9) C1L WP

@[expose] noncomputable def ABP : Nat := pcomp 276 9 (mask 9) (Co3CP.S 0) (Co3CP.S 1)

theorem hW : wordEqK 276 9 (mask 9) (pidn 276 9) Co3C.S Co3C.SI 14 co3CoprimeWord WP = true := by
  quickRfl
theorem hWl : lettersK 2 co3CoprimeWord = true := by quickRfl
theorem hWI : invEqK 276 9 (mask 9) (276 * 9) WP WPI = true := by quickRfl
theorem hC1L : compEqK 276 9 (mask 9) (276 * 9) WPI (Co3C.S 1) C1L = true := by quickRfl
theorem hC1 : compEqK 276 9 (mask 9) (276 * 9) C1L WP C1P = true := by quickRfl
theorem hE0 : eqK (Co3CP.S 0) (Co3C.S 0) = true := by quickRfl
theorem hE1 : eqK (Co3CP.S 1) C1P = true := by quickRfl
theorem hid : idK 276 9 (mask 9) = true := by quickRfl
theorem hP0 : powEqK 276 9 (mask 9) (276 * 9) (pidn 276 9) (Co3CP.S 0) 3 (pidn 276 9) = true := by
  quickRfl
theorem hN0 : neK 276 9 (mask 9) (276 * 9) (Co3CP.S 0) (pidn 276 9) = true := by quickRfl
theorem hP1 : powEqK 276 9 (mask 9) (276 * 9) (pidn 276 9) (Co3CP.S 1) 4 (pidn 276 9) = true := by
  quickRfl
theorem hN1 : neK 276 9 (mask 9) (276 * 9) (ppow 276 9 (mask 9) (pidn 276 9) (Co3CP.S 1) 2)
    (pidn 276 9) = true := by quickRfl
theorem hQ1 : powEqK 276 9 (mask 9) (276 * 9) (pidn 276 9) (Co3CP.S 1) 2
    (ppow 276 9 (mask 9) (pidn 276 9) (Co3CP.S 1) 2) = true := by quickRfl
theorem hAB : compEqK 276 9 (mask 9) (276 * 9) (Co3CP.S 0) (Co3CP.S 1) ABP = true := by quickRfl
theorem hPAB : powEqK 276 9 (mask 9) (276 * 9) (pidn 276 9) ABP 23 (pidn 276 9) = true := by
  quickRfl
theorem hNAB : neK 276 9 (mask 9) (276 * 9) ABP (pidn 276 9) = true := by quickRfl

theorem levels0 : ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[0]!).pts.size = 276 := by
  have h := rawOrbitSizesK_sound Co3C.binds Co3C.perm Co3C.hl
  have h' : (rawLevels 276 co3ChainArrs co3ChainBaseArr).toList.map (fun L => L.pts.size) =
      (List.range 7).map fun i => Raw.rcnt (Co3C.LR i) := h
  have e : (List.range 7).map (fun i => Raw.rcnt (Co3C.LR i)) = [276, 275, 112, 81, 20, 18, 2] := by
    decide
  rw [e] at h'
  rw [← Array.getElem!_toList]
  cases hx : (rawLevels 276 co3ChainArrs co3ChainBaseArr).toList with
  | nil => rw [hx] at h'; simp at h'
  | cons L0 rest =>
    rw [hx] at h'
    simp only [List.map_cons, List.cons.injEq] at h'
    simpa using h'.1

theorem facts : (rawChainOK 276 (co3ChainArrs.extract 0 co3ChainGenCount) co3ChainArrs co3ChainBaseArr
        (wordsArr co3ChainGenCount co3ChainStrongCount co3ChainDerivations) 4 = true ∧
      rawOrbitSizes 276 co3ChainArrs co3ChainBaseArr = [276, 275, 112, 81, 20, 18, 2] ∧
      ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[0]!).pts.size = 276
    )
    ∧ (rawChainOK 276 (co3CoprimeArrs.extract 0 co3CoprimeGenCount) co3CoprimeArrs
        co3CoprimeBaseArr (wordsArr co3CoprimeGenCount co3CoprimeStrongCount co3CoprimeDerivations)
        4 = true ∧
      rawOrbitSizes 276 co3CoprimeArrs co3CoprimeBaseArr = [276, 275, 112, 81, 20, 18, 2]
    )
    ∧ (lettersOK 2 co3CoprimeWord = true ∧
      isInvA 276 co3WordArr (invCand 276 co3WordArr) = true ∧
      eqA 276 co3CoprimeArrs[0]! co3ChainArrs[0]! = true ∧
      eqA 276 co3CoprimeArrs[1]! co3C1Arr = true ∧
      eqA 276 (co3PowA 276 co3CoprimeArrs[0]! 3) (idA 276) = true ∧
      eqA 276 co3CoprimeArrs[0]! (idA 276) = false ∧
      eqA 276 (co3PowA 276 co3CoprimeArrs[1]! 4) (idA 276) = true ∧
      eqA 276 (co3PowA 276 co3CoprimeArrs[1]! 2) (idA 276) = false ∧
      eqA 276 (co3PowA 276 (compA 276 co3CoprimeArrs[0]! co3CoprimeArrs[1]!) 23) (idA 276) = true ∧
      eqA 276 (compA 276 co3CoprimeArrs[0]! co3CoprimeArrs[1]!) (idA 276) = false
    ) := by
  have hw := (wordEqK_sound ⟨Co3C.binds.2.2.2.1, Co3C.binds.2.2.2.2.1⟩ Co3C.perm hW).1
  have hwa : co3WordArr = unpack 276 9 WP := hw
  have hi := invEqK_sound hWI
  have hc1 : co3C1Arr = unpack 276 9 C1P := by
    change compA 276 (compA 276 (invCand 276 co3WordArr) co3ChainArrs[1]!) co3WordArr = _
    rw [hwa, hi.1, Co3C.binds.2.2.2.2.1 1 (by norm_num), compEqK_sound hC1L, compEqK_sound hC1]
  have hidA := (idK_sound hid).symm
  have cp0 := Co3CP.arr_eq 0 (by norm_num)
  have cp1 := Co3CP.arr_eq 1 (by norm_num)
  refine ⟨⟨rawChainK_sound (NS := 18) (CH := 16) Co3C.binds Co3C.head Co3C.hl (by norm_num)
      Co3C.hs, by rw [rawOrbitSizesK_sound Co3C.binds Co3C.perm Co3C.hl]; decide, levels0⟩,
    ⟨rawChainK_sound (NS := 18) (CH := 16) Co3CP.binds Co3CP.head Co3CP.hl (by norm_num)
      Co3CP.hs, by rw [rawOrbitSizesK_sound Co3CP.binds Co3CP.perm Co3CP.hl]; decide⟩,
    lettersK_sound hWl, by rw [hwa, hi.1]; exact hi.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cp0, Co3C.binds.2.2.2.2.1 0 (by norm_num)]
    exact eqK_sound hE0
  · rw [cp1, hc1]
    exact eqK_sound hE1
  · rw [cp0, powEqK_sound hP0, hidA]
    exact eqK_sound (by quickRfl)
  · rw [cp0, hidA]
    exact neK_sound hN0
  · rw [cp1, powEqK_sound hP1, hidA]
    exact eqK_sound (by quickRfl)
  · rw [cp1, powEqK_sound hQ1, hidA]
    exact neK_sound hN1
  · rw [cp0, cp1, compEqK_sound hAB, powEqK_sound hPAB, hidA]
    exact eqK_sound (by quickRfl)
  · rw [cp0, cp1, compEqK_sound hAB, hidA]
    exact neK_sound hNAB

end CertificateChecks.KernelSpor.Co3Order

end
