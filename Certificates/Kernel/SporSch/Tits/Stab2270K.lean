module

public import Certificates.Kernel.SporSch.Tits.GenStab
public import Certificates.Kernel.Sporadic.Tits.Texts2268
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Certificates.Kernel.SporSch.TitsStabSound
meta import CFSG.Sporadic.Schreier.TitsData
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.TitsChain

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kst_stab CertificateChecks.KernelSporSch.TitsSF 8775 14 CertificateChecks.KernelSpor.T8775.F
  CFSG.Sporadic.Schreier.Tits.titsDerivedDerivations CFSG.Sporadic.Schreier.Tits.titsDerivedComm
#kst_stab CertificateChecks.KernelSporSch.TitsSS 2925 12 CertificateChecks.KernelSpor.T2925.F
  CFSG.Sporadic.Schreier.Tits.titsDerivedDerivations CFSG.Sporadic.Schreier.Tits.titsDerivedComm

namespace CertificateChecks.KernelSporSch.TitsStab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem fG : allN 4 (fun j => permW 8775 14 (T8775.F j) (TitsSF.GI j)) =
    true := by quickRfl
theorem fU0u : wordW 8775 14 T8775.F TitsSF.GI 4 (titsU 0) (TitsSF.U 0) = true := by
  quickRfl
theorem fU0v : wordW 8775 14 T8775.F TitsSF.GI 4 (titsV 0) (TitsSF.V 0) = true := by
  quickRfl
theorem fU1u : wordW 8775 14 T8775.F TitsSF.GI 4 (titsU 1) (TitsSF.U 1) = true := by
  quickRfl
theorem fU1v : wordW 8775 14 T8775.F TitsSF.GI 4 (titsV 1) (TitsSF.V 1) = true := by
  quickRfl
theorem fU : allN 2 (fun j => bAnd(wordW 8775 14 T8775.F TitsSF.GI 4 (titsU j) (TitsSF.U j),
    wordW 8775 14 T8775.F TitsSF.GI 4 (titsV j) (TitsSF.V j))) = true :=
  allN_of_forall fun j hj => by
    match j, hj with
    | 0, _ => exact (bAnd_iff _ _).2 ⟨fU0u, fU0v⟩
    | 1, _ => exact (bAnd_iff _ _).2 ⟨fU1u, fU1v⟩
theorem fUp : allN 2 (fun j => bAnd(permW 8775 14 (TitsSF.U j) (TitsSF.UI j),
    permW 8775 14 (TitsSF.V j) (TitsSF.VI j))) = true := by quickRfl
theorem fC0 : bAnd(eq2W 8775 14 (TitsSF.A 0) (TitsSF.UI 0) (TitsSF.VI 0),
    bAnd(eq2W 8775 14 (TitsSF.B 0) (TitsSF.A 0) (TitsSF.U 0),
    bAnd(eq2W 8775 14 (TitsSF.T 0) (TitsSF.B 0) (TitsSF.V 0),
    Nat.beq (TitsSF.T 0) (T8775.F (4 + 0))))) = true := by quickRfl
theorem fC1 : bAnd(eq2W 8775 14 (TitsSF.A 1) (TitsSF.UI 1) (TitsSF.VI 1),
    bAnd(eq2W 8775 14 (TitsSF.B 1) (TitsSF.A 1) (TitsSF.U 1),
    bAnd(eq2W 8775 14 (TitsSF.T 1) (TitsSF.B 1) (TitsSF.V 1),
    Nat.beq (TitsSF.T 1) (T8775.F (4 + 1))))) = true := by quickRfl
theorem fC : allN 2 (fun j => bAnd(eq2W 8775 14 (TitsSF.A j) (TitsSF.UI j) (TitsSF.VI j),
    bAnd(eq2W 8775 14 (TitsSF.B j) (TitsSF.A j) (TitsSF.U j),
    bAnd(eq2W 8775 14 (TitsSF.T j) (TitsSF.B j) (TitsSF.V j),
    Nat.beq (TitsSF.T j) (T8775.F (4 + j)))))) = true :=
  allN_of_forall fun j hj => by
    match j, hj with
    | 0, _ => exact fC0
    | 1, _ => exact fC1
theorem fTp0 : permW 8775 14 (TitsSF.T 0) (TitsSF.TI 0) = true := by quickRfl
theorem fTp1 : permW 8775 14 (TitsSF.T 1) (TitsSF.TI 1) = true := by quickRfl
theorem fTp2 : permW 8775 14 (TitsSF.T 2) (TitsSF.TI 2) = true := by quickRfl
theorem fTp3 : permW 8775 14 (TitsSF.T 3) (TitsSF.TI 3) = true := by quickRfl
theorem fTp4 : permW 8775 14 (TitsSF.T 4) (TitsSF.TI 4) = true := by quickRfl
theorem fTp5 : permW 8775 14 (TitsSF.T 5) (TitsSF.TI 5) = true := by quickRfl
theorem fTp6 : permW 8775 14 (TitsSF.T 6) (TitsSF.TI 6) = true := by quickRfl
theorem fTp7 : permW 8775 14 (TitsSF.T 7) (TitsSF.TI 7) = true := by quickRfl
theorem fTp8 : permW 8775 14 (TitsSF.T 8) (TitsSF.TI 8) = true := by quickRfl
theorem fTp9 : permW 8775 14 (TitsSF.T 9) (TitsSF.TI 9) = true := by quickRfl
theorem fTp10 : permW 8775 14 (TitsSF.T 10) (TitsSF.TI 10) = true := by quickRfl
theorem fTp11 : permW 8775 14 (TitsSF.T 11) (TitsSF.TI 11) = true := by quickRfl
theorem fTp12 : permW 8775 14 (TitsSF.T 12) (TitsSF.TI 12) = true := by quickRfl
theorem fTp : allN 13 (fun j => permW 8775 14 (TitsSF.T j) (TitsSF.TI j)) = true :=
  allN_of_forall fun j hj => by
    match j, hj with
    | 0, _ => exact fTp0
    | 1, _ => exact fTp1
    | 2, _ => exact fTp2
    | 3, _ => exact fTp3
    | 4, _ => exact fTp4
    | 5, _ => exact fTp5
    | 6, _ => exact fTp6
    | 7, _ => exact fTp7
    | 8, _ => exact fTp8
    | 9, _ => exact fTp9
    | 10, _ => exact fTp10
    | 11, _ => exact fTp11
    | 12, _ => exact fTp12
theorem fS0 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 0) titsDerivedDerivations[0]!
    (TitsSF.T (2 + 0)) = true := by quickRfl
theorem fS1 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 1) titsDerivedDerivations[1]!
    (TitsSF.T (2 + 1)) = true := by quickRfl
theorem fS2 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 2) titsDerivedDerivations[2]!
    (TitsSF.T (2 + 2)) = true := by quickRfl
theorem fS3 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 3) titsDerivedDerivations[3]!
    (TitsSF.T (2 + 3)) = true := by quickRfl
theorem fS4 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 4) titsDerivedDerivations[4]!
    (TitsSF.T (2 + 4)) = true := by quickRfl
theorem fS5 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 5) titsDerivedDerivations[5]!
    (TitsSF.T (2 + 5)) = true := by quickRfl
theorem fS6 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 6) titsDerivedDerivations[6]!
    (TitsSF.T (2 + 6)) = true := by quickRfl
theorem fS7 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 7) titsDerivedDerivations[7]!
    (TitsSF.T (2 + 7)) = true := by quickRfl
theorem fS8 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 8) titsDerivedDerivations[8]!
    (TitsSF.T (2 + 8)) = true := by quickRfl
theorem fS9 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 9) titsDerivedDerivations[9]!
    (TitsSF.T (2 + 9)) = true := by quickRfl
theorem fS10 : wordW 8775 14 TitsSF.T TitsSF.TI (2 + 10) titsDerivedDerivations[10]!
    (TitsSF.T (2 + 10)) = true := by quickRfl
theorem fS : strongK 8775 14 TitsSF.T TitsSF.TI titsDerivedDerivations 2 = true :=
  strongK_of fun i hi => by
    have h11 : i < 11 := hi
    match i, h11 with
    | 0, _ => exact fS0
    | 1, _ => exact fS1
    | 2, _ => exact fS2
    | 3, _ => exact fS3
    | 4, _ => exact fS4
    | 5, _ => exact fS5
    | 6, _ => exact fS6
    | 7, _ => exact fS7
    | 8, _ => exact fS8
    | 9, _ => exact fS9
    | 10, _ => exact fS10
theorem fF : forest1K 8775 14 TitsSF.T 2 0 TitsSF.DEP TitsSF.PAR TitsSF.GL = true := by
  quickRfl

theorem aG : allN 4 (fun j => permW 2925 12 (T2925.F j) (TitsSS.GI j)) =
    true := by quickRfl
theorem aU0u : wordW 2925 12 T2925.F TitsSS.GI 4 (titsU 0) (TitsSS.U 0) = true := by
  quickRfl
theorem aU0v : wordW 2925 12 T2925.F TitsSS.GI 4 (titsV 0) (TitsSS.V 0) = true := by
  quickRfl
theorem aU1u : wordW 2925 12 T2925.F TitsSS.GI 4 (titsU 1) (TitsSS.U 1) = true := by
  quickRfl
theorem aU1v : wordW 2925 12 T2925.F TitsSS.GI 4 (titsV 1) (TitsSS.V 1) = true := by
  quickRfl
theorem aU : allN 2 (fun j => bAnd(wordW 2925 12 T2925.F TitsSS.GI 4 (titsU j) (TitsSS.U j),
    wordW 2925 12 T2925.F TitsSS.GI 4 (titsV j) (TitsSS.V j))) = true :=
  allN_of_forall fun j hj => by
    match j, hj with
    | 0, _ => exact (bAnd_iff _ _).2 ⟨aU0u, aU0v⟩
    | 1, _ => exact (bAnd_iff _ _).2 ⟨aU1u, aU1v⟩
theorem aUp : allN 2 (fun j => bAnd(permW 2925 12 (TitsSS.U j) (TitsSS.UI j),
    permW 2925 12 (TitsSS.V j) (TitsSS.VI j))) = true := by quickRfl
theorem aC0 : bAnd(eq2W 2925 12 (TitsSS.A 0) (TitsSS.UI 0) (TitsSS.VI 0),
    bAnd(eq2W 2925 12 (TitsSS.B 0) (TitsSS.A 0) (TitsSS.U 0),
    bAnd(eq2W 2925 12 (TitsSS.T 0) (TitsSS.B 0) (TitsSS.V 0),
    Nat.beq (TitsSS.T 0) (T2925.F (4 + 0))))) = true := by quickRfl
theorem aC1 : bAnd(eq2W 2925 12 (TitsSS.A 1) (TitsSS.UI 1) (TitsSS.VI 1),
    bAnd(eq2W 2925 12 (TitsSS.B 1) (TitsSS.A 1) (TitsSS.U 1),
    bAnd(eq2W 2925 12 (TitsSS.T 1) (TitsSS.B 1) (TitsSS.V 1),
    Nat.beq (TitsSS.T 1) (T2925.F (4 + 1))))) = true := by quickRfl
theorem aC : allN 2 (fun j => bAnd(eq2W 2925 12 (TitsSS.A j) (TitsSS.UI j) (TitsSS.VI j),
    bAnd(eq2W 2925 12 (TitsSS.B j) (TitsSS.A j) (TitsSS.U j),
    bAnd(eq2W 2925 12 (TitsSS.T j) (TitsSS.B j) (TitsSS.V j),
    Nat.beq (TitsSS.T j) (T2925.F (4 + j)))))) = true :=
  allN_of_forall fun j hj => by
    match j, hj with
    | 0, _ => exact aC0
    | 1, _ => exact aC1
theorem aTp0 : permW 2925 12 (TitsSS.T 0) (TitsSS.TI 0) = true := by quickRfl
theorem aTp1 : permW 2925 12 (TitsSS.T 1) (TitsSS.TI 1) = true := by quickRfl
theorem aTp2 : permW 2925 12 (TitsSS.T 2) (TitsSS.TI 2) = true := by quickRfl
theorem aTp3 : permW 2925 12 (TitsSS.T 3) (TitsSS.TI 3) = true := by quickRfl
theorem aTp4 : permW 2925 12 (TitsSS.T 4) (TitsSS.TI 4) = true := by quickRfl
theorem aTp5 : permW 2925 12 (TitsSS.T 5) (TitsSS.TI 5) = true := by quickRfl
theorem aTp6 : permW 2925 12 (TitsSS.T 6) (TitsSS.TI 6) = true := by quickRfl
theorem aTp7 : permW 2925 12 (TitsSS.T 7) (TitsSS.TI 7) = true := by quickRfl
theorem aTp8 : permW 2925 12 (TitsSS.T 8) (TitsSS.TI 8) = true := by quickRfl
theorem aTp9 : permW 2925 12 (TitsSS.T 9) (TitsSS.TI 9) = true := by quickRfl
theorem aTp10 : permW 2925 12 (TitsSS.T 10) (TitsSS.TI 10) = true := by quickRfl
theorem aTp11 : permW 2925 12 (TitsSS.T 11) (TitsSS.TI 11) = true := by quickRfl
theorem aTp12 : permW 2925 12 (TitsSS.T 12) (TitsSS.TI 12) = true := by quickRfl
theorem aTp : allN 13 (fun j => permW 2925 12 (TitsSS.T j) (TitsSS.TI j)) = true :=
  allN_of_forall fun j hj => by
    match j, hj with
    | 0, _ => exact aTp0
    | 1, _ => exact aTp1
    | 2, _ => exact aTp2
    | 3, _ => exact aTp3
    | 4, _ => exact aTp4
    | 5, _ => exact aTp5
    | 6, _ => exact aTp6
    | 7, _ => exact aTp7
    | 8, _ => exact aTp8
    | 9, _ => exact aTp9
    | 10, _ => exact aTp10
    | 11, _ => exact aTp11
    | 12, _ => exact aTp12
theorem aS0 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 0) titsDerivedDerivations[0]!
    (TitsSS.T (2 + 0)) = true := by quickRfl
theorem aS1 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 1) titsDerivedDerivations[1]!
    (TitsSS.T (2 + 1)) = true := by quickRfl
theorem aS2 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 2) titsDerivedDerivations[2]!
    (TitsSS.T (2 + 2)) = true := by quickRfl
theorem aS3 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 3) titsDerivedDerivations[3]!
    (TitsSS.T (2 + 3)) = true := by quickRfl
theorem aS4 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 4) titsDerivedDerivations[4]!
    (TitsSS.T (2 + 4)) = true := by quickRfl
theorem aS5 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 5) titsDerivedDerivations[5]!
    (TitsSS.T (2 + 5)) = true := by quickRfl
theorem aS6 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 6) titsDerivedDerivations[6]!
    (TitsSS.T (2 + 6)) = true := by quickRfl
theorem aS7 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 7) titsDerivedDerivations[7]!
    (TitsSS.T (2 + 7)) = true := by quickRfl
theorem aS8 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 8) titsDerivedDerivations[8]!
    (TitsSS.T (2 + 8)) = true := by quickRfl
theorem aS9 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 9) titsDerivedDerivations[9]!
    (TitsSS.T (2 + 9)) = true := by quickRfl
theorem aS10 : wordW 2925 12 TitsSS.T TitsSS.TI (2 + 10) titsDerivedDerivations[10]!
    (TitsSS.T (2 + 10)) = true := by quickRfl
theorem aS : strongK 2925 12 TitsSS.T TitsSS.TI titsDerivedDerivations 2 = true :=
  strongK_of fun i hi => by
    have h11 : i < 11 := hi
    match i, h11 with
    | 0, _ => exact aS0
    | 1, _ => exact aS1
    | 2, _ => exact aS2
    | 3, _ => exact aS3
    | 4, _ => exact aS4
    | 5, _ => exact aS5
    | 6, _ => exact aS6
    | 7, _ => exact aS7
    | 8, _ => exact aS8
    | 9, _ => exact aS9
    | 10, _ => exact aS10
theorem aF : forest1K 2925 12 TitsSS.T 2 0 TitsSS.DEP TitsSS.PAR TitsSS.GL = true := by
  quickRfl

@[expose] noncomputable def fixW (w : Nat) (T TI : Nat → Nat) (L : List Nat) (wd : List Int) :
    Bool :=
  bAnd(lettersK 13 wd, allL (fun f => Nat.beq (wPtG w T TI wd f) f) L)

theorem kH : allA (fixW 11 TitsD.S TitsD.SI [0]) titsHWords = true := by quickRfl
theorem kS : allA (fixW 14 TitsSF.T TitsSF.TI [0]) titsSWords = true := by quickRfl
theorem kR : allA (fixW 14 TitsSF.T TitsSF.TI [0]) titsRWords = true := by quickRfl
theorem kN : allA (fixW 12 TitsSS.T TitsSS.TI [0]) titsNWords = true := by quickRfl
theorem kJ : allA (fixW 14 TitsSF.T TitsSF.TI titsFiveFlags) titsJWords = true := by quickRfl
theorem kK : allA (fixW 14 TitsSF.T TitsSF.TI titsThreeFlags) titsKWords = true := by quickRfl

@[expose] noncomputable def gF (wd : List Int) : Nat → Nat := wPtG 14 TitsSF.T TitsSF.TI wd

@[expose] noncomputable def rngW (wd : List Int) (k : Nat) (L : List Nat) : Bool :=
  bAnd(lettersK 13 wd, allL (fun p => itRng 8775 (gF wd) k p) L)

@[expose] noncomputable def powW (wd : List Int) (k : Nat) (L : List Nat) : Bool :=
  allL (fun p => Nat.beq (itN (gF wd) k p) p) L

theorem r1 : rngW [3] 4 titsFiveFlags = true := by quickRfl
theorem r2 : rngW [3, 4, 13] 5 titsFiveFlags = true := by quickRfl
theorem r3 : rngW titsNWords[2]! 2 titsThreeFlags = true := by quickRfl
theorem r4 : rngW (titsNWords[2]! ++ titsNWords[3]!) 3 titsThreeFlags = true := by quickRfl
theorem p1 : powW [3] 4 titsFiveFlags = true := by quickRfl
theorem p2 : bIf(powW [3] 2 titsFiveFlags, false, true) = true := by quickRfl
theorem p3 : powW [3, 4, 13] 5 titsFiveFlags = true := by quickRfl
theorem p4 : bIf(powW [3, 4, 13] 1 titsFiveFlags, false, true) = true := by quickRfl
theorem p5 : powW titsNWords[2]! 2 titsThreeFlags = true := by quickRfl
theorem p6 : bIf(powW titsNWords[2]! 1 titsThreeFlags, false, true) = true := by quickRfl
theorem p7 : powW (titsNWords[2]! ++ titsNWords[3]!) 3 titsThreeFlags = true := by quickRfl
theorem p8 : bIf(powW (titsNWords[2]! ++ titsNWords[3]!) 1 titsThreeFlags, false, true) = true := by
  quickRfl

theorem kB : allN 8775 (fun j => beqB (Nat.beq (pgW 12 (TMaps.F 0) j) 0)
    (memN j titsFiveFlags)) = true := by quickRfl
theorem kK3 : allN 8775 (fun j => beqB (Nat.beq (pgW 12 (TMaps.F 1) j) 0)
    (memN j titsThreeFlags)) = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsStab

end
