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
meta def c1w (j k : Nat) : Array Nat :=
  CFSG.Monster.B.Co2.Native.wordA 8330 heInnerLetters1
    (heInnerLetters1.map (CFSG.Monster.B.Co2.Native.invCand 8330)) ((heInnerWords1.getD j []).drop k)
meta def c3A : Array Nat := c1w 3 74
meta def c3B : Array Nat := c1w 3 34
meta def c8A : Array Nat := c1w 8 130
meta def c8B : Array Nat := c1w 8 90
meta def c8C : Array Nat := c1w 8 50
meta def c8D : Array Nat := c1w 8 10
meta def tM1 : Array Nat := hfTTabs[1]!
meta def tM2 : Array Nat := hfTTabs[2]!
meta def tM3 : Array Nat := hfTTabs[3]!
meta def tM4 : Array Nat := hfTTabs[4]!
meta def bM0 : Array Nat := hfB1Tabs[0]!
meta def bM1 : Array Nat := hfB1Tabs[1]!
meta def eM : Array Nat := hfE2Tab
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
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L1 14 CertificateChecks.KernelLC.HeFix4.c1M1
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L2 14 CertificateChecks.KernelLC.HeFix4.c1M2
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L3 14 CertificateChecks.KernelLC.HeFix4.c1M3
#ks_perm CertificateChecks.KernelLC.HeFix4.C1L8 14 CertificateChecks.KernelLC.HeFix4.c1M8
#ks_perm CertificateChecks.KernelLC.HeFix4.C3A 14 CertificateChecks.KernelLC.HeFix4.c3A
#ks_perm CertificateChecks.KernelLC.HeFix4.C3B 14 CertificateChecks.KernelLC.HeFix4.c3B
#ks_perm CertificateChecks.KernelLC.HeFix4.C8A 14 CertificateChecks.KernelLC.HeFix4.c8A
#ks_perm CertificateChecks.KernelLC.HeFix4.C8B 14 CertificateChecks.KernelLC.HeFix4.c8B
#ks_perm CertificateChecks.KernelLC.HeFix4.C8C 14 CertificateChecks.KernelLC.HeFix4.c8C
#ks_perm CertificateChecks.KernelLC.HeFix4.C8D 14 CertificateChecks.KernelLC.HeFix4.c8D
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
