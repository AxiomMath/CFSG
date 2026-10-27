module

public import Certificates.Data.Kernel.PermCent.SmallK12
public import CFSG.GH74.KGroups.TwoM12CheckInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.K5131

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover CFSG.GH74.KGroups.TwoM12

theorem k5131 : ((elemsC m12CentQ2).all fun a => (elemsC m12CentQ2).all fun b =>
    siftC fixedDQ (cOf gzPerm * (a * b * a⁻¹ * b⁻¹) * (cOf gzPerm)⁻¹) 0) = true := by
  decide +kernel

theorem k5131_neg : ((elemsC m12CentQ2).all fun a =>
    siftC fixedDQ (cOf gzPerm * a * (cOf gzPerm)⁻¹) 0) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.K5131
