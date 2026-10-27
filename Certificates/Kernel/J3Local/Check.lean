module

public import Certificates.Data.Kernel.J3LocalK
public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Kernel.Sporadic.J3K.Defs
public import CFSG.RankThree.Asc83Table.J3Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PChainSound

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelJ3L

open CFSG.KC.J3Loc CFSG.KC.OpsK CFSG.KC.M1F2

theorem full_K : fullK JA.M JB.M KernelSpor.J3K.PJ 20520 CFSG.RankThree.Asc83Table.J3.j3Cert =
    true := by
  quickRfl

theorem range_neg : (!rangeK { CFSG.RankThree.Asc83Table.J3.j3Cert with nregs := 3 }) = true := by
  quickRfl

theorem moved_neg : (!Nat.beq (movedL (tF (idF 80))
    (lanesP KernelSpor.J3K.PJ 4) (onesL 4)) (onesL 4)) = true := by
  quickRfl

end CertificateChecks.KernelJ3L

end
