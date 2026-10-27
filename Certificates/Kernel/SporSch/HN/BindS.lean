module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit

public section

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native

theorem bindS : hnxShapeK (hnsOrbitData ()) = true := by decide +kernel

theorem neg_shape : (!shapeOK 2 (.branch 2 (.leaf 1 1 0) (.leaf 1 1 0))) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNXBind

end
