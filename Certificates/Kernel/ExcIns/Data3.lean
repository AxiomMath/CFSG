module

public import Certificates.Data.Kernel.ExcIns.Grow
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.ExcInsK in
#kc_repo #kc_jsonc_gz CFSG.ExcInsK.D3 "Certificates/Kernel/ExcIns/data/ins3.json.gz" 5586 16534798416656868258
  (gm : Nat) (nr : Nat) (R : Nat) (PL : List Nat) (S : List (Nat × List Nat))
  (G0 : List (Nat × List Nat)) (G1 : List (Nat × List Nat)) (G2 : List (Nat × List Nat))
  (G3 : List (Nat × List Nat)) (G4 : List (Nat × List Nat)) (G5 : List (Nat × List Nat))
