module

public import Init
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CFSG.KD.J3C TT "Certificates/Kernel/J3Coset/data/tabs.bin.gz" 64 4 517120 6694840402817147040

#kc_repo #kc_ktree_gz CFSG.KD.J3C FT "Certificates/Kernel/J3Coset/data/forests.bin.gz" 128 4 8273920 17453194104161903987

#kc_repo #kc_json_gz CFSG.KD.J3C "Certificates/Kernel/J3Coset/data/recs.json.gz" 155910 10560658086987011674
  (rels : List (List Nat)) (phiA : List Nat) (phiB : List Nat) (xW : List Nat) (d1W : List Nat)
  (d2W : List Nat) (gW : List Nat) (uW : List Nat) (wK1 : List Nat) (wK2 : List Nat)
  (wP1 : List Nat) (wP2 : List Nat) (ordP1 : Nat) (ordP2 : Nat) (beta0 : Nat) (roots : List Nat)
  (gws : List (List Nat)) (Qr : List (Nat × List Nat)) (Zr : List (Nat × List Nat))
  (sw1 : List Bool) (sw2 : List Bool)
  (Oc : List (List (Nat × List Nat × Nat × Nat × List Nat × List Nat)))
  (phiW1 : List Nat) (phiW2 : List Nat) (cw1 : List Nat) (cw2 : List Nat) (zc : List Nat)
  (zk : List Nat)
