module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.C13608Data
public import Certificates.Data.Kernel.SporSch.HNXDot
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_root CFSG.KD.HNXK.DOT13608
  "Certificates/Kernel/SporSch/HN/data/hnx_dot13608.bin" 58 16468383201016039702
#kc_repo #kc_items_root CFSG.KD.HNXK.FIX13608
  "Certificates/Kernel/SporSch/HN/data/hnx_fix13608.bin" 40 706725800108023671

public noncomputable section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX CFSG.KD.HN13608

@[expose] def dot13608 (k : Nat) : Bool :=
  Nat.beq (dotSum TX CM3 M MR L1 ONES GQ (nat_lit 1) (Nat.mul (nat_lit 2227) k) (fixLen k))
    (DOT13608 k)

@[expose] def fix13608 (k : Nat) : Bool := fixOk GE FIX13608 0 k

end CFSG.KD.HNXK

end
