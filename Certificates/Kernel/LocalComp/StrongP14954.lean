module

public import Certificates.Kernel.LocalComp.F3.McL
public import Certificates.Kernel.LocalComp.F3.ON
public import Certificates.Kernel.LocalComp.Co2Ops
public import Certificates.Kernel.LocalComp.Co3Ops

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.StrongP14954

open CFSG.SectionRank.Native CFSG.KD.LC.F3 CertificateChecks.KernelLC

theorem mcl_K : CFSG.KC.OpsLayK.cubK McL.lay McL.A McL.B mclSylow5Data = true := by
  decide +kernel

theorem on_K : CFSG.KC.OpsLayK.cubK ON.lay ON.A ON.B onSylow7Data = true := by decide +kernel

theorem co3_K : CFSG.KC.LocalComp.Cub.cubicK 22 Co3Ops.SA.M Co3Ops.SB.M co3Sylow5Data = true := by
  decide +kernel

theorem co2_K : CFSG.KC.LocalComp.Cub.cubicK 22 Co2Ops.SA.M Co2Ops.SB.M co2Sylow5Data = true := by
  decide +kernel

theorem mcl_neg_seeds : (!CFSG.KC.OpsLayK.cubK McL.lay McL.B McL.A mclSylow5Data) = true := by
  decide +kernel

theorem mcl_neg_r :
    (!CFSG.KC.OpsLayK.cubK McL.lay McL.A McL.B { mclSylow5Data with r := 4 }) = true := by
  decide +kernel

theorem on_neg_r :
    (!CFSG.KC.OpsLayK.cubK ON.lay ON.A ON.B { onSylow7Data with r := 6 }) = true := by
  decide +kernel

theorem co3_neg_seeds :
    (!CFSG.KC.LocalComp.Cub.cubicK 22 Co3Ops.SB.M Co3Ops.SA.M co3Sylow5Data) = true := by
  decide +kernel

theorem co2_neg_r :
    (!CFSG.KC.LocalComp.Cub.cubicK 22 Co2Ops.SA.M Co2Ops.SB.M { co2Sylow5Data with r := 4 }) =
      true := by
  decide +kernel

end CertificateChecks.KernelLC.StrongP14954

end
