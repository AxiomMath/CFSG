module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.Misc.Lines "Certificates/Kernel/Misc/Fischer1000/lines.json.gz"
  640219 7930651413050063132 (PP : Nat)
#kc_repo #kc_json_family_gz CFSG.KD.Misc.Lines
  "Certificates/Kernel/Misc/Fischer1000/lines.json.gz" 640219 7930651413050063132
  (PB : Nat) (PL : List Nat)

#kc_select CFSG.KD.Misc.Lines PB PB 693
#kc_listDispatch CFSG.KD.Misc.Lines PL PL 693
