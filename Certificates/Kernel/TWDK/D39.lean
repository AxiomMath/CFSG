module

public import Certificates.Data.Kernel.TWDK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.TWDK in
#kc_repo #kc_json_gz CFSG.KD.TWDK39 "Certificates/Kernel/TWDK/data/d39.json.gz" 10325
  9971309588384127254
  (F : List GGDepANPair) (S : List KSingleE) (R : List KResE)

end
