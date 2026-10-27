module

public import Certificates.Data.Kernel.MonsterB.Rem3069
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMonB.R3069 RT
  "Certificates/Kernel/MonsterB/Rem3069/data/recs.bin" 14000 4 9729720 8290780596000295823

namespace CertificateChecks.KernelMonB.R3069

@[expose] noncomputable def chk (c : Nat) : Bool := CFSG.KC.Rem3069.chunkOK RT c

end CertificateChecks.KernelMonB.R3069

end
