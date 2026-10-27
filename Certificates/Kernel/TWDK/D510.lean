module

public import Certificates.Data.Kernel.TWDK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.TWDK in
#kc_repo #kc_json_gz CFSG.KD.TWDK510 "Certificates/Kernel/TWDK/data/d510.json.gz" 45034
  10205028405487016105
  (F : List GGDepANPair) (S : List KSingleE) (R : List KResE)

end
