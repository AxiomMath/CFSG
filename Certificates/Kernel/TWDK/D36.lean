module

public import Certificates.Data.Kernel.TWDK36
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.TWDK36 in
#kc_repo #kc_json_gz CFSG.KD.TWDK36 "Certificates/Kernel/TWDK/data/d36.json.gz" 27667
  8679247850977276108
  (F : List GGDepANPair) (O : List KOut) (S : List KOneE) (T : List KTwoE)

end
