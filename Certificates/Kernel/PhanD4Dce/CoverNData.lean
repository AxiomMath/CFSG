module

public import Certificates.Kernel.PhanD4Dce.Data
public import Certificates.Kernel.PhanD4Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.CoverNet
import CFSG.Certificates.Kernel.Common.Benes
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_benes CFSG.KD.PhanD4Dce NO 0 12 15 fun _ c => CFSG.KC.TwDce3.tabPlanesN 15 22680 (CFSG.KD.PhanD4Dce.FO c)

#kc_select CFSG.KD.PhanD4Dce NS NO 12

#kc_repo #kc_json_gz CFSG.KD.PhanD4Dce "Certificates/Kernel/PhanD4Dce/data/covern.json.gz" 75127 18092069593194726121
  (CR : List (List Nat)) (CA : List (List Nat))
