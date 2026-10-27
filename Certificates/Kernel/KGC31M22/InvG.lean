module

public import Certificates.Kernel.KGC31M22.Defs
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KS.SporSch.MOC

@[expose] noncomputable def invOneG (k : Nat) : Bool :=
  permOK 22 5 (mask 5) (22 * 5) (D.ST k) (pinv 22 5 (D.ST k)) &&
    porbOne 22 5 5 X5 C5 (D.ST k) && porbOne 22 5 7 X7 C7 (D.ST k) &&
    pactOne 22 5 11 X11 (D.ST k)

@[expose] noncomputable def invBlkG (k : Nat) : Bool :=
  (List.range' (600 * k) (min 600 (D.c - 600 * k))).all invOneG

end CertificateChecks.KernelKGC31M22

#kc_each CertificateChecks.KernelKGC31M22.invBlkG 0 2

end
