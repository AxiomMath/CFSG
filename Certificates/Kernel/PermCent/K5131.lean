module

public import Certificates.Data.Kernel.PermCent.SmallK12
public import Certificates.Data.Kernel.PermCent.SmallB
public import CFSG.GH74.KGroups.TwoM12CheckInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.K5131

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.ComponentClassification.M12Cover
  CFSG.GH74.KGroups.TwoM12

@[expose] noncomputable def gensC : List (CV 12) :=
  m12CentWords2.map (evCodesB ([m12gA, m12gB].map cOf))

theorem k5131N : gensC.all (fun s => (elemsC fixedDQ).all fun d =>
    siftC fixedDQ (cOf gzPerm * s * (cOf gzPerm)⁻¹ * d * (cOf gzPerm * s * (cOf gzPerm)⁻¹)⁻¹) 0) =
      true := by
  decide +kernel

theorem k5131G : gensC.all (fun s => gensC.all fun t =>
    siftC fixedDQ (cOf gzPerm * (s * t * s⁻¹ * t⁻¹) * (cOf gzPerm)⁻¹) 0) = true := by
  decide +kernel

theorem k5131_neg : ((elemsC m12CentQ2).all fun a =>
    siftC fixedDQ (cOf gzPerm * a * (cOf gzPerm)⁻¹) 0) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.K5131
