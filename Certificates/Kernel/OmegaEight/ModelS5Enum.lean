module

public import Certificates.Data.Kernel.O8.ModelW
public import Certificates.Kernel.OmegaEight.CPChains
public import Certificates.Kernel.OmegaEight.ModelData
public import Certificates.Kernel.OmegaEight.NatData
public import Certificates.Kernel.LocalComp.Omega1Chain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.Stage1.Model CertificateChecks.KernelLC.W3185

theorem kEnumP : s5EnumOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩
    ⟨Om1.LR, Om1.TRI, Om1.BP, 7⟩ Om1.S Om1.SI MdCLSP MdNCP MdADJP MdSZP
    (psiK false NSP NIP 120 9 5665569 1) (cands .plus) = true := by
  quickRfl

theorem kEnumM : s5EnumOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩
    ⟨LMn.LR, LMn.TRI, LMn.BP, 7⟩ LMn.S LMn.SI MdCLSM MdNCM MdADJM MdSZM
    (psiK true NSM NIM 136 8 4552225 1) (cands .minus) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
