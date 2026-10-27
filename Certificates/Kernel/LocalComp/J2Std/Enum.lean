module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Tests
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Tests

namespace CertificateChecks.KernelLC.J2Std

open CFSG.ComponentClassification.RankTwoClassical.J2Std

meta def c1Gens : List (Array Nat) := j2StdC1.toList
meta def c2Gens : List (Array Nat) := j2StdC2.toList
meta def hGens : List (Array Nat) := j2StdH.toList
meta def chGens : List (Array Nat) := j2StdCH.toList
meta def rGens : List (Array Nat) := j2A4RGens.toList
meta def crGens : List (Array Nat) := j2A4CR.toList
meta def lGens : List (Array Nat) := j2A4L.toList
meta def c3Gens : List (Array Nat) := j2A4C3.toList

end CertificateChecks.KernelLC.J2Std

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelLC.J2Std.C1 CertificateChecks.KernelLC.J2Std.c1Gens 315 9 12
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.C2 CertificateChecks.KernelLC.J2Std.c2Gens 315 9 10
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.H CertificateChecks.KernelLC.J2Std.hGens 315 9 15
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.CH CertificateChecks.KernelLC.J2Std.chGens 315 9 10
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.R CertificateChecks.KernelLC.J2Std.rGens 315 9 4
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.CR CertificateChecks.KernelLC.J2Std.crGens 315 9 8
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.L CertificateChecks.KernelLC.J2Std.lGens 315 9 10
#lc_bfs_sl CertificateChecks.KernelLC.J2Std.C3 CertificateChecks.KernelLC.J2Std.c3Gens 315 9 9

end
