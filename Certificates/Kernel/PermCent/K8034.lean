module

public import Certificates.Data.Kernel.PermCent.L34MaxTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34MaxT

open CFSG.GH74.KGroups.L34 CFSG.RankThree.PartTwo.KFacts.L34Max CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates

theorem kQN0 : schP QN0 = true ∧ orderV QN0 = 72 := by decide +kernel

theorem kQE0 : schP QE0 = true ∧ orderV QE0 = 9 := by decide +kernel

theorem kNorm : ([n0a, n0b].all fun n => [e0a, e0b].all fun e => siftP QE0 (n * e * n⁻¹) 0) =
    true := by
  decide +kernel

theorem kOut : (!(siftP QE0 (pa * e0a * pa⁻¹) 0)) = true := by decide +kernel

theorem kGen : genCheck = true := by decide +kernel

theorem kStab : stabC = true := by decide +kernel

theorem kKey1 : keyN 1 = orL u0L := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.L34MaxT
