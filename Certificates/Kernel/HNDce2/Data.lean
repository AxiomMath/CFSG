module

public import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.HNDce2 "Certificates/Kernel/HNDce2/data/dce.items.gz" 71373 17743229387822092569
  RD[498] RW[498] RA[498] RJ[498] L[12] WD[55] INVM BS NB

#kc_select CFSG.KD.HNDce2 RD RD 498
#kc_select CFSG.KD.HNDce2 RW RW 498
#kc_select CFSG.KD.HNDce2 RA RA 498
#kc_select CFSG.KD.HNDce2 RJ RJ 498
#kc_select CFSG.KD.HNDce2 F L 12
#kc_select CFSG.KD.HNDce2 WD WD 55

#kc_repo #kc_json_gz CFSG.KD.HNDce2 "Certificates/Kernel/HNDce2/data/cover.json.gz" 158178 6166977595118779264
  (CV : List (List Nat)) (CG : List (List Nat)) (CW : List (List (List Nat)))
  (CB : List (List (List Nat))) (CS : List (List (List Nat))) (CT : List (List (List Nat)))
  (CN : List Nat)
