module

public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Data.Inputs2711eJ3
public import Certificates.Data.Kernel.GenWf
public import Certificates.Data.Kernel.OpsMcertTX
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGen2711J3

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.Asc83Table.J3 CFSG.KC.OpsK CFSG.KC.OpsMT CertificateChecks.KernelJ3L

theorem gen271101T_K : seedsXT (opsF2K 80) JA.M JB.M
    ⟨j3GenData.nregs, j3GenData.prog, j3GenData.facts⟩ 0 1
    ⟨j3Cert.nregs, j3Cert.prog, []⟩ [(4, basisW j3Cert.rb 9), (5, basisW j3Cert.rb 10)] =
      true := by
  quickRfl

theorem gen271101T_D : genWf 3 j3GenData = true := by
  decide +kernel

end CertificateChecks.KernelGen2711J3

end
