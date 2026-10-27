module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.J2Cent
public import Certificates.Kernel.Sporadic.OddCore.MN
public import CFSG.GH74.Generic.S45.PerfWitData
public import Certificates.Data.Kernel.PerfWitK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PerfWit5148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PerfWitK CFSG.GH74.Generic.S45

theorem j3_base : bAnd(canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13),
    bAnd(idK 6156 13 (mask 13), allN 5 (fun j =>
      bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3CentP (Nat.add 10 j)),
        canonK 6156 13 (mask 13) (6156 * 13) (J3CentI (Nat.add 10 j)))))) = true := by
  quickRfl

theorem j2_base : bAnd(canonK 315 9 (mask 9) (315 * 9) (pidn 315 9),
    bAnd(idK 315 9 (mask 9), allN 4 (fun j =>
      bAnd(canonK 315 9 (mask 9) (315 * 9) (J2CentT.F (Nat.add 32 j)),
        canonK 315 9 (mask 9) (315 * 9) (J2CentI (Nat.add 32 j)))))) = true := by
  quickRfl

theorem j3_perf : perfK 6156 13 5 (fun j => J3CentP (10 + j)) (fun j => J3CentI (10 + j))
    j3PerfWit2A = true := by
  quickRfl

theorem mcl_in : perfK 275 9 2 (fun j => McLCT.F (5 + j)) (fun j => MNI (5 + j))
    mclPerfWitIn = true := by
  quickRfl

theorem mcl_out : perfK 275 9 4 (fun j => McLCT.F (18 + j)) (fun j => MNI (18 + j))
    mclPerfWitOut = true := by
  quickRfl

theorem j2_perf : perfK 315 9 4 (fun j => J2CentT.F (32 + j)) (fun j => J2CentI (32 + j))
    j2PerfWit2A = true := by
  quickRfl

end CertificateChecks.KernelSpor.PerfWit5148

end
