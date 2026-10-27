module

public import Certificates.Data.Kernel.FiveTwoK
public import CFSG.RankThree.Native.FiveTwoData
public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Kernel.AlphaMc.SeedsF2
public import Certificates.Kernel.SectionRankHS.Seeds
public import Certificates.Kernel.LocalComp.ThOrder
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelFT.J3A CFSG.Blueprint.NativeSporadic.J3Seed1
#lc_m1 CertificateChecks.KernelFT.J3A CFSG.Blueprint.NativeSporadic.J3Seed1 80
#ks_chars CertificateChecks.KernelFT.J3B CFSG.Blueprint.NativeSporadic.J3Seed2
#lc_m1 CertificateChecks.KernelFT.J3B CFSG.Blueprint.NativeSporadic.J3Seed2 80

namespace CertificateChecks.KernelFT

open CFSG.KC.FiveTwoK CFSG.KC.OpsK CFSG.RankThree.Native

theorem j3_K : fiveN (opsF2K 80) J3A.M J3B.M j3FiveTwo = true := by quickRfl

theorem co1_K : fiveN (opsF2K 24) KernelAM.C1A.M KernelAM.C1B.M co1FiveTwo = true := by quickRfl

theorem co2_K : fiveN (opsF2K 22) KernelAM.C2A.M KernelAM.C2B.M co2FiveTwo = true := by quickRfl

theorem co3_K : fiveN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M co3FiveTwo = true := by quickRfl

theorem hs_K : fiveN (opsF2K 20) KernelSRHS.SA.M KernelSRHS.SB.M hsFiveTwo = true := by quickRfl

theorem th_K : fiveN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thFiveTwo = true := by quickRfl

theorem hs_neg_w : (!fiveN (opsF2K 20) KernelSRHS.SA.M KernelSRHS.SB.M
    { hsFiveTwo with w := 0 }) = true := by quickRfl

theorem hs_neg_tests : (!fiveN (opsF2K 20) KernelSRHS.SA.M KernelSRHS.SB.M
    { hsFiveTwo with base := { hsFiveTwo.base with tests := [] } }) = true := by quickRfl

theorem hs_neg_range : (!fiveN (opsF2K 20) KernelSRHS.SA.M KernelSRHS.SB.M
    { hsFiveTwo with w := 4 }) = true := by quickRfl

end CertificateChecks.KernelFT

end
