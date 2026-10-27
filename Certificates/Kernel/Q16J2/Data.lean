module

public import Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelQ16J2
  "Certificates/Kernel/Q16J2/data/q16J2.json.gz" 9971 9645416590715843374
  (q16J2O : Array Nat) (q16J2G : Array Nat) (q16J2PS : List Nat) (q16J2C : ArrCertP)
