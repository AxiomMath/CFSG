module

import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.Spor.WordProg

set_option maxRecDepth 400000

#kc_repo #kc_ktree_gz CFSG.KD.Fi23Kt RS "Certificates/Kernel/Fi23Kt/data/mats.bin.gz" 16003 4
  240045 9984671587133669909
#kc_repo #kc_json_family_gz CFSG.KD.Fi23Kt "Certificates/Kernel/Fi23Kt/data/lists.json.gz"
  57968 3482138779258662995 (PS : List Nat) (WC : List Nat) (PE : List Nat) (PF : List Nat)

#kc_listDispatch CFSG.KD.Fi23Kt PS PS 15
#kc_listDispatch CFSG.KD.Fi23Kt WC WC 15
#kc_listDispatch CFSG.KD.Fi23Kt PE PE 41
#kc_listDispatch CFSG.KD.Fi23Kt PF PF 41
