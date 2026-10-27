module

public import Certificates.Data.Kernel.TWDK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.TWDK in
#kc_repo #kc_json_gz CFSG.KD.TWDK55 "Certificates/Kernel/TWDK/data/d55.json.gz" 32184
  8100098328792743191
  (F : List GGDepANPair) (S : List KSingleE) (R : List KResE)

end
