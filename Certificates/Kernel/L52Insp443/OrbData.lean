module

public import Certificates.Data.Kernel.L52Insp443.Inv
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelL52I.O
  "Certificates/Kernel/L52Insp443/data/orb.json.gz" 62935 2736699241247984551
  (inv : List (List Nat)) (px : List (List Nat)) (qx : List (List Nat))
  (cs : List (List (List Nat)))
