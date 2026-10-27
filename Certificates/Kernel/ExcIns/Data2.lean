module

public import Certificates.Data.Kernel.ExcIns.Grow
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.ExcInsK in
#kc_repo #kc_jsonc_gz CFSG.ExcInsK.D2 "Certificates/Kernel/ExcIns/data/ins2.json.gz" 11767 14661113213288386270
  (gm : Nat) (nr : Nat) (R : Nat) (PL : List Nat) (S : List (Nat × List Nat))
  (G0 : List (Nat × List Nat)) (G1 : List (Nat × List Nat)) (G2 : List (Nat × List Nat))
  (G3 : List (Nat × List Nat)) (G4 : List (Nat × List Nat)) (G5 : List (Nat × List Nat))
  (G6 : List (Nat × List Nat)) (G7 : List (Nat × List Nat))
