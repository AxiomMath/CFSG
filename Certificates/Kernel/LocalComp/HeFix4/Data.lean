module

public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixFourCheckInputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixFourCheckInputs
meta import CFSG.Sporadic.HeldB.InnerCheckInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelLC.HeFix4

open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.HeldB

meta def orbGensM : Array (Array Nat) := hfOrbGens

meta def t1M : Array Nat := heT1Arr
meta def kM : Array Nat := hfKTab
meta def c1M1 : Array Nat := heInnerC1 1
meta def c1M2 : Array Nat := heInnerC1 2
meta def c1M3 : Array Nat := heInnerC1 3
meta def c1M8 : Array Nat := heInnerC1 8
meta def c1p (j a p : Nat) : Array Nat :=
  CFSG.Monster.B.Co2.Native.wordA 8330 heInnerLetters1
    (heInnerLetters1.map (CFSG.Monster.B.Co2.Native.invCand 8330))
    (((heInnerWords1.getD j []).drop a).take p)
meta def p1M : Array Nat := c1p 1 5 12
meta def p2M : Array Nat := c1p 2 0 8
meta def p3M : Array Nat := c1p 3 4 10
meta def p8M : Array Nat := c1p 8 8 18
meta def tM1 : Array Nat := hfTTabs[1]!
meta def tM2 : Array Nat := hfTTabs[2]!
meta def tM3 : Array Nat := hfTTabs[3]!
meta def tM4 : Array Nat := hfTTabs[4]!
meta def bM0 : Array Nat := hfB1Tabs[0]!
meta def bM1 : Array Nat := hfB1Tabs[1]!
meta def eM : Array Nat := hfE2Tab
meta def invM (t : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 8330 t
meta def t1iM : Array Nat := invM heT1Arr
meta def kiM : Array Nat := invM hfKTab
meta def tiM1 : Array Nat := invM hfTTabs[1]!
meta def tiM2 : Array Nat := invM hfTTabs[2]!
meta def tiM3 : Array Nat := invM hfTTabs[3]!
meta def tiM4 : Array Nat := invM hfTTabs[4]!
meta def oM0 : Array Nat := hfOrbGens[0]!
meta def oM1 : Array Nat := hfOrbGens[1]!
meta def oM2 : Array Nat := hfOrbGens[2]!
meta def oM3 : Array Nat := hfOrbGens[3]!
meta def oM4 : Array Nat := hfOrbGens[4]!
meta def oM5 : Array Nat := hfOrbGens[5]!
meta def oM6 : Array Nat := hfOrbGens[6]!
meta def oM7 : Array Nat := hfOrbGens[7]!

end CertificateChecks.KernelLC.HeFix4

#lc_forest CertificateChecks.KernelLC.HeFix4.F 8330 CertificateChecks.KernelLC.HeFix4.orbGensM [7750]

#ks_perm CertificateChecks.KernelLC.HeFix4.T1P 14 CertificateChecks.KernelLC.HeFix4.t1M
#ks_perm CertificateChecks.KernelLC.HeFix4.KP 14 CertificateChecks.KernelLC.HeFix4.kM
#ks_perm CertificateChecks.KernelLC.HeFix4.T1I 14 CertificateChecks.KernelLC.HeFix4.t1iM
#ks_perm CertificateChecks.KernelLC.HeFix4.KI 14 CertificateChecks.KernelLC.HeFix4.kiM
#ks_perm CertificateChecks.KernelLC.HeFix4.TI1 14 CertificateChecks.KernelLC.HeFix4.tiM1
#ks_perm CertificateChecks.KernelLC.HeFix4.TI2 14 CertificateChecks.KernelLC.HeFix4.tiM2
#ks_perm CertificateChecks.KernelLC.HeFix4.TI3 14 CertificateChecks.KernelLC.HeFix4.tiM3
#ks_perm CertificateChecks.KernelLC.HeFix4.TI4 14 CertificateChecks.KernelLC.HeFix4.tiM4
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L1 14 CertificateChecks.KernelLC.HeFix4.c1M1
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L2 14 CertificateChecks.KernelLC.HeFix4.c1M2
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L3 14 CertificateChecks.KernelLC.HeFix4.c1M3
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L8 14 CertificateChecks.KernelLC.HeFix4.c1M8
#ks_perm CertificateChecks.KernelLC.HeFix4.P1 14 CertificateChecks.KernelLC.HeFix4.p1M
#ks_perm CertificateChecks.KernelLC.HeFix4.P2 14 CertificateChecks.KernelLC.HeFix4.p2M
#ks_perm CertificateChecks.KernelLC.HeFix4.P3 14 CertificateChecks.KernelLC.HeFix4.p3M
#ks_perm CertificateChecks.KernelLC.HeFix4.P8 14 CertificateChecks.KernelLC.HeFix4.p8M
#ks_perm CertificateChecks.KernelLC.HeFix4.TL1 14 CertificateChecks.KernelLC.HeFix4.tM1
#ks_perm CertificateChecks.KernelLC.HeFix4.TL2 14 CertificateChecks.KernelLC.HeFix4.tM2
#ks_perm CertificateChecks.KernelLC.HeFix4.TL3 14 CertificateChecks.KernelLC.HeFix4.tM3
#ks_perm CertificateChecks.KernelLC.HeFix4.TL4 14 CertificateChecks.KernelLC.HeFix4.tM4
#ks_perm CertificateChecks.KernelLC.HeFix4.BL0 14 CertificateChecks.KernelLC.HeFix4.bM0
#ks_perm CertificateChecks.KernelLC.HeFix4.BL1 14 CertificateChecks.KernelLC.HeFix4.bM1
#ks_perm CertificateChecks.KernelLC.HeFix4.E2P 14 CertificateChecks.KernelLC.HeFix4.eM
#ks_perm CertificateChecks.KernelLC.HeFix4.OL0 14 CertificateChecks.KernelLC.HeFix4.oM0
#ks_perm CertificateChecks.KernelLC.HeFix4.OL1 14 CertificateChecks.KernelLC.HeFix4.oM1
#ks_perm CertificateChecks.KernelLC.HeFix4.OL2 14 CertificateChecks.KernelLC.HeFix4.oM2
#ks_perm CertificateChecks.KernelLC.HeFix4.OL3 14 CertificateChecks.KernelLC.HeFix4.oM3
#ks_perm CertificateChecks.KernelLC.HeFix4.OL4 14 CertificateChecks.KernelLC.HeFix4.oM4
#ks_perm CertificateChecks.KernelLC.HeFix4.OL5 14 CertificateChecks.KernelLC.HeFix4.oM5
#ks_perm CertificateChecks.KernelLC.HeFix4.OL6 14 CertificateChecks.KernelLC.HeFix4.oM6
#ks_perm CertificateChecks.KernelLC.HeFix4.OL7 14 CertificateChecks.KernelLC.HeFix4.oM7

end
