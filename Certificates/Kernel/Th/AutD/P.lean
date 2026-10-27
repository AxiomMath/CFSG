module

public import Certificates.Kernel.Th.AutD.Defs
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.AutD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def eSl (s : Nat) : Bool :=
  penumSlK 51 6 (mask 6) (51 * 6) false ADE.G ADE.GI ADE.k ADE.cnt ADE.T ADE.PL ADE.POS ADE.SRT
    ADE.SRI (Nat.mul s 384) 384

@[expose] noncomputable def pSl (s : Nat) : Bool :=
  allN 384 fun d => strictB (Nat.add (Nat.mul 384 s) d) pt

end CertificateChecks.KernelTh.AutD

#kon_slices CertificateChecks.KernelTh.AutD.eSl 0 9
#kon_join CertificateChecks.KernelTh.AutD.eAll CertificateChecks.KernelTh.AutD.eSl 9
#kon_slices CertificateChecks.KernelTh.AutD.pSl 0 9
#kon_join CertificateChecks.KernelTh.AutD.pAll CertificateChecks.KernelTh.AutD.pSl 9

end
