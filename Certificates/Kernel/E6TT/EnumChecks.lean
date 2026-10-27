module

public import Certificates.Data.Kernel.E6TT.Enum
public import Certificates.Kernel.E6TT.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT

theorem dataOK : grOK (Certificates.Data.E6TableT.roots ()) D.GR D.FL = true := by quickRfl

theorem enumA2 : repOK D.GR D.FL 0 D.L0 D.N01 D.N02 D.N03 D.N04 D.N05 1296 = true := by quickRfl

theorem enumA4A1 : repOK D.GR D.FL 1 D.L1 D.N11 D.N12 D.N13 D.N14 D.N15 240 = true := by quickRfl

theorem enumD4 : repOK D.GR D.FL 2 D.L2 D.N21 D.N22 D.N23 D.N24 D.N25 1152 = true := by quickRfl

theorem enumA5 : repOK D.GR D.FL 3 D.L3 D.N31 D.N32 D.N33 D.N34 D.N35 1440 = true := by quickRfl

theorem enumD5 : repOK D.GR D.FL 4 D.L4 D.N41 D.N42 D.N43 D.N44 D.N45 1920 = true := by quickRfl

end CertificateChecks.KernelE6TT

end
