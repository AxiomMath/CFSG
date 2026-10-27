module

public import Certificates.Data.Kernel.SporSch.HNXPt
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_root CFSG.KD.HNXK.FIX2094
  "Certificates/Kernel/SporSch/HN/data/hnx_fix2094.bin" 176 4968491712764863109
#kc_repo #kc_items_root CFSG.KD.HNXK.FIX2103
  "Certificates/Kernel/SporSch/HN/data/hnx_fix2103.bin" 37 10741733212166213795
#kc_repo #kc_items_root CFSG.KD.HNXK.FIX2109
  "Certificates/Kernel/SporSch/HN/data/hnx_fix2109.bin" 160 13510576159257613662

public noncomputable section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX

@[expose] def fixLen (k : Nat) : Nat := nIf(Nat.blt k 7, 2227, 2224)

@[expose] def fixOk (G : Nat) (V : Nat → Nat) (m k : Nat) : Bool :=
  Nat.beq (fixSum TX CM3 M G (2227 * k) (fixLen k)) (V (8 * m + k))

end CFSG.KD.HNXK

end
