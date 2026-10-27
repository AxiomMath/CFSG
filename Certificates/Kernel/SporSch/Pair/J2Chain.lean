module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSporSch.j2SA : Array (Array Nat) :=
  CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ()

namespace CertificateChecks.KernelSporSch.PJ2Words

@[expose] def D : List (List Int) :=
  [[-2, -2, 1, 2, 2], [-2, 1, -2, -2, 1, 2, 2, 1, 2], [1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1],
    [3, 5, 3, 4, 3, 4], [3, 4, 3, 5, 3, 4]]

end CertificateChecks.KernelSporSch.PJ2Words

#ks_chars CertificateChecks.KernelSporSch.PJ2Text CFSG.Sporadic.Schreier.PairNative.j2StrongHex

#ks_rawchain CertificateChecks.KernelSporSch.PJ2 315 9 8 CertificateChecks.KernelSporSch.j2SA
  CFSG.Sporadic.Schreier.PairJ2.baseArr 2 CertificateChecks.KernelSporSch.PJ2Words.D

namespace CertificateChecks.KernelSporSch.PJ2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem tab : hexTabK PJ2Text.chars 4 315 9 7 S = true := by quickRfl

theorem perm : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (S j) (SI j)) = true := by quickRfl

theorem arr_eq (j : Nat) (hj : j < 7) : (j2StrongArrs ())[j]! = unpack 315 9 (S j) := by
  have h := hexTabK_sound tab j hj
  rw [← PJ2Text.eq] at h
  rw [j2StrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem binds : Binds 315 9 S 7 3 BP (j2StrongArrs ()) baseArr :=
  ⟨by decide, by decide, by decide, by simp [j2StrongArrs], arr_eq, by decide, by decide⟩

theorem words_eq : j2Words () = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 PJ2Words.D := by
  decide

theorem chain : rawChainOK 315 ((j2StrongArrs ()).extract 0 2) (j2StrongArrs ()) baseArr
    (j2Words ()) 1 = true := by
  rw [words_eq]
  exact rawChainK_sound (NS := 40) (CH := 8) binds head hl (by decide) hs

theorem orbits : rawOrbitSizes 315 (j2StrongArrs ()) baseArr = [315, 160, 12] := by
  rw [rawOrbitSizesK_sound binds perm hl]
  decide +kernel

theorem o1 : ordWK 315 9 bs [S 0] 2 = true := by quickRfl
theorem o2 : ordWK 315 9 bs [S 1] 3 = true := by quickRfl
theorem o3 : ordWK 315 9 bs [S 1, S 0] 7 = true := by quickRfl
theorem o4 : ordWK 315 9 bs [S 1, S 1, S 0, S 1, S 0] 12 = true := by quickRfl

theorem wA_eq : wA = [unpack 315 9 (S 0)] := by
  rw [wA, arr_eq 0 (by omega)]

theorem wB_eq : wB = [unpack 315 9 (S 1)] := by
  rw [wB, arr_eq 1 (by omega)]

theorem ords : ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 7 = true ∧
    ordB bs (patW wA wB commPat) 12 = true := by
  have e3 : patW [unpack 315 9 (S 0)] [unpack 315 9 (S 1)] [false, true] =
      [S 1, S 0].map (unpack 315 9) := rfl
  have e4 : patW [unpack 315 9 (S 0)] [unpack 315 9 (S 1)] commPat =
      [S 1, S 1, S 0, S 1, S 0].map (unpack 315 9) := rfl
  have e1 : [unpack 315 9 (S 0)] = [S 0].map (unpack 315 9) := rfl
  have e2 : [unpack 315 9 (S 1)] = [S 1].map (unpack 315 9) := rfl
  rw [wA_eq, wB_eq, e3, e4, e1, e2]
  exact ⟨ordWK_sound o1, ordWK_sound o2, ordWK_sound o3, ordWK_sound o4⟩

end CertificateChecks.KernelSporSch.PJ2

end
