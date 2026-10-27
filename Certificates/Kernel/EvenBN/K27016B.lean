module

public import Certificates.Kernel.EvenBN.CNtAux
public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Data.TitsAschbacherSecFour
public import Certificates.Data.Kernel.EvenBN.BaseTw
meta import Certificates.Data.TitsAschbacherSecFour
meta import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherSecFour

meta def aArr : Array Nat := CFSG.Quasithin.RuRank3.titsAuxArr
meta def aiArr : Array Nat := invCand 1755 aArr
meta def conjArr (x : Array Nat) : Array Nat := compA 1755 aiArr (compA 1755 x aArr)
meta def q1Arr : Array Nat := qArrs.getD 0 #[]
meta def q2Arr : Array Nat := qArrs.getD 1 #[]
meta def q3Arr : Array Nat := qArrs.getD 2 #[]
meta def au1Arr : Array Nat := conjArr u1A
meta def au2Arr : Array Nat := conjArr u2A
meta def au3Arr : Array Nat := conjArr u3A
meta def aq1Arr : Array Nat := conjArr q1Arr
meta def aq2Arr : Array Nat := conjArr q2Arr
meta def aq3Arr : Array Nat := conjArr q3Arr

end CertificateChecks.Batch27016

#ks_perm CertificateChecks.Batch27016.U1L 11 Certificates.TitsAschbacherSecFour.u1A
#ks_perm CertificateChecks.Batch27016.U2L 11 Certificates.TitsAschbacherSecFour.u2A
#ks_perm CertificateChecks.Batch27016.U3L 11 Certificates.TitsAschbacherSecFour.u3A
#ks_perm CertificateChecks.Batch27016.Q1L 11 CertificateChecks.Batch27016.q1Arr
#ks_perm CertificateChecks.Batch27016.Q2L 11 CertificateChecks.Batch27016.q2Arr
#ks_perm CertificateChecks.Batch27016.Q3L 11 CertificateChecks.Batch27016.q3Arr
#ks_perm CertificateChecks.Batch27016.AU1 11 CertificateChecks.Batch27016.au1Arr
#ks_perm CertificateChecks.Batch27016.AU2 11 CertificateChecks.Batch27016.au2Arr
#ks_perm CertificateChecks.Batch27016.AU3 11 CertificateChecks.Batch27016.au3Arr
#ks_perm CertificateChecks.Batch27016.AQ1 11 CertificateChecks.Batch27016.aq1Arr
#ks_perm CertificateChecks.Batch27016.AQ2 11 CertificateChecks.Batch27016.aq2Arr
#ks_perm CertificateChecks.Batch27016.AQ3 11 CertificateChecks.Batch27016.aq3Arr
#ks_perm CertificateChecks.Batch27016.AI 11 CertificateChecks.Batch27016.aiArr

namespace CertificateChecks.Batch27016

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherSecFour

theorem kLit : (Nat.beq U1L (wP TitsN.S u1Word) && Nat.beq U2L (wP TitsN.S u2Word) &&
    ([Q1L, Q2L, Q3L] == qWords.map (wP TitsN.S))) = true := by quickRfl

theorem kLit3 : Nat.beq U3L (pcomp 1755 11 (mask 11) U1L U2L) = true := by quickRfl

theorem kConj : (Nat.beq (pcomp 1755 11 (mask 11) U1L (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) AU1) &&
    Nat.beq (pcomp 1755 11 (mask 11) U2L (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) AU2) &&
    Nat.beq (pcomp 1755 11 (mask 11) U3L (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) AU3) &&
    Nat.beq (pcomp 1755 11 (mask 11) Q1L (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) AQ1) &&
    Nat.beq (pcomp 1755 11 (mask 11) Q2L (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) AQ2) &&
    Nat.beq (pcomp 1755 11 (mask 11) Q3L (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) AQ3)) =
      true := by quickRfl

theorem kInv : allN 1755 (fun i =>
    Nat.beq (pg 11 (mask 11) AI (pg 11 (mask 11) (TAux.F 0) i)) i) = true := by quickRfl

theorem cU1 : C U1L := by quickRfl
theorem cU2 : C U2L := by quickRfl
theorem cU3 : C U3L := by quickRfl
theorem cQ1 : C Q1L := by quickRfl
theorem cQ2 : C Q2L := by quickRfl
theorem cQ3 : C Q3L := by quickRfl
theorem cAU1 : C AU1 := by quickRfl
theorem cAU2 : C AU2 := by quickRfl
theorem cAU3 : C AU3 := by quickRfl
theorem cAQ1 : C AQ1 := by quickRfl
theorem cAQ2 : C AQ2 := by quickRfl
theorem cAQ3 : C AQ3 := by quickRfl

theorem kS0 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    U1L = true := by quickRfl
theorem kS1 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    U2L = true := by quickRfl
theorem kS2 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    U3L = true := by quickRfl
theorem kS3 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    Q1L = true := by quickRfl
theorem kS4 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    Q2L = true := by quickRfl
theorem kS5 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    Q3L = true := by quickRfl
theorem kS6 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    AU1 = true := by quickRfl
theorem kS7 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    AU2 = true := by quickRfl
theorem kS8 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    AU3 = true := by quickRfl
theorem kS9 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    AQ1 = true := by quickRfl
theorem kS10 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    AQ2 = true := by quickRfl
theorem kS11 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    AQ3 = true := by quickRfl

end CertificateChecks.Batch27016

end
