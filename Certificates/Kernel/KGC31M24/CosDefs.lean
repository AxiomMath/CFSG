module

public import Certificates.Kernel.KGC31M24.Defs7217
public import Certificates.Data.Kernel.KGC31PNorm

public section

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P

@[expose] noncomputable def cos0K : Bool :=
  Nat.beq (cb0P.countP fun c => pnormAll 24 5 r2P c (pinv 24 5 c)) 21504 &&
    Nat.beq cb0P.length 21504

@[expose] noncomputable def cosNK : Bool :=
  Nat.beq (rsP.getD 0 0) (pidn 24 5) && pspanOK 24 5 r2P &&
    (List.range 14).all fun j =>
      !(pnormAll 24 5 r2P (rsP.getD (j + 1) 0) (pinv 24 5 (rsP.getD (j + 1) 0)))

end CertificateChecks.KernelKGC31M24

end
