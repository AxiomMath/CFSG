module

public import CFSG.Sporadic.ThSchreier.GlobalData
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.PlaneChainDataInputs
import Certificates.Kernel.SporSch.Th.PlaneText
public import Certificates.Certificate1022
public import CFSG.Certificates.Kernel.ThCent.PlaneSound
public import Certificates.Kernel.ThCent.Consumers
public import Certificates.Data.Kernel.ThCent.Pin
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Certificates.Kernel.Th.Spec.FwdPlane
public import CFSG.Sporadic.Th.KernelSimple

public section

namespace CertificateChecks.KernelThPlane

open CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.ThCent CFSG.KD.ThCent CFSG.KD Pointwise

set_option maxRecDepth 100000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

end CertificateChecks.KernelThPlane

end
