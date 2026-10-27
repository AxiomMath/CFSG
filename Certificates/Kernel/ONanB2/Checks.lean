module

public import Certificates.Data.Kernel.ONanB2K
public import Certificates.Kernel.ONanB2.Data

public section

namespace CertificateChecks.ONanB2

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK CFSG.OddStandard.ONanRec.B2K

theorem ck6149_base : b2Base = cmChain.map ChainLevel.base := by decide +kernel

theorem ck6149_fz : fzK = true := by decide +kernel

theorem ck6149_r : rK = true := by decide +kernel

theorem ck6149_irred : irredK = true := by decide +kernel

theorem ck6149_s : sK = true := by decide +kernel

theorem ck6149_t : tK = true := by decide +kernel

theorem ck6149_tcent : tCentK = true := by decide +kernel

theorem ck6149_y : yK = true := by decide +kernel

theorem ck6149_orbR : orbK [r1W] ptsR 2240 CFSG.KD.ONanB2.orbR = true := by decide +kernel

theorem ck6149_orbS : orbK [zW, dW] ptsS 2240 CFSG.KD.ONanB2.orbS = true := by decide +kernel

theorem ck6149_rs : allNeB rsWords = true := by decide +kernel

theorem ck6149_cs : allNeB csWords = true := by decide +kernel

theorem ck6149_cent : centK = true := by decide +kernel

theorem ck6149_ord : ordK = true := by decide +kernel

end CertificateChecks.ONanB2
