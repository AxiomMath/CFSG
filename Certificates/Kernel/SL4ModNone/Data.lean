module

public import Certificates.Data.Kernel.SL4ModNoneCerts
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open CFSG.LargeExtraspecial.SL4Mod.Native in
#kc_repo #kc_json_gz CertificateChecks.KernelSL4ModNone
  "Certificates/Kernel/SL4ModNone/data/none.json.gz" 671244 14466168426059978844
  (C00 : List (Nat × NoneTup × NoneTup)) (C01 : List (Nat × NoneTup × NoneTup))
  (C02 : List (Nat × NoneTup × NoneTup)) (C10 : List (Nat × NoneTup × NoneTup))
  (C11 : List (Nat × NoneTup × NoneTup)) (C12 : List (Nat × NoneTup × NoneTup))
  (C20 : List (Nat × NoneTup × NoneTup)) (C21 : List (Nat × NoneTup × NoneTup))
  (C22 : List (Nat × NoneTup × NoneTup))

end
