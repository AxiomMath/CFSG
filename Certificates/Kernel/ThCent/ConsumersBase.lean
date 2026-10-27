
module

public import Certificates.Kernel.ThCent.LeavesBase
public import Certificates.Kernel.ThCent.Pin
public import CFSG.Certificates.Kernel.ThCent.PinSoundBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByList
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.Th.KernelPlanesBase
public import CFSG.Sporadic.Th.KernelSimpleBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase

@[expose] public section

namespace CertificateChecks.KernelThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec
  CFSG.KC.Th.Spec.FwdRel CFSG.SectionRank.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.KD

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


end CertificateChecks.KernelThCent

end
