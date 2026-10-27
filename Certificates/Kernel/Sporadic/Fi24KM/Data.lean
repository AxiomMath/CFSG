module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Br.Data

#kc_repo #kc_ktree CFSG.KD.KMFi24 MS "Certificates/Kernel/Sporadic/Fi24KM/data/mats.bin" 152491 5 4422239 7696517299870014248
#kc_repo #kc_json_family_gz CFSG.KD.KMFi24 "Certificates/Kernel/Sporadic/Fi24KM/data/km.json.gz" 8483
  18124322490807724207 (PS : List Nat) (WC : List Nat) (QR : List Nat) (QM : List Nat)
#kc_listDispatch CFSG.KD.KMFi24 PS PS 29
#kc_listDispatch CFSG.KD.KMFi24 WC WC 29
#kc_listDispatch CFSG.KD.KMFi24 QR QR 3
#kc_listDispatch CFSG.KD.KMFi24 QM QM 8

@[expose] public noncomputable def CFSG.KD.KMFi24.RS (k : Nat) : Nat := CFSG.KD.KMFi24.MS k
