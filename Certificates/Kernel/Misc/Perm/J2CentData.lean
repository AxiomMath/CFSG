module

public import Certificates.Data.Kernel.J2Cent
public import Certificates.Kernel.Misc.Perm.J2Fam
public import Certificates.Kernel.J2Cover.AutChain
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.J2Cent "Certificates/Kernel/Misc/Perm/data/j2cent.json.gz" 1358 9904999915967177123
  (CT : List Nat)

public section

namespace CertificateChecks.KernelMisc.J2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Cent CertificateChecks.KernelJ2Cover
open CertificateChecks.KernelMisc.J2C3 (X)
open CertificateChecks.KernelMisc.J2Fam (V1)

@[expose] noncomputable def fC (a : Nat) : Bool :=
  Nat.beq (blkCent 315 9 PA.LR PA.TR PA.BP X V1 a) (lget CT (blkKey 315 9 PA.LR PA.TR PA.BP a))

end CertificateChecks.KernelMisc.J2Cent

end
