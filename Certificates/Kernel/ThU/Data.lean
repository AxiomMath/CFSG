module

public import CFSG.Certificates.Kernel.Bounds.LoadRoot
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.ThU.RB "Certificates/Kernel/ThU/data/regs.items"
  5200046 9699726443159445674
#kc_repo #kc_list_root CFSG.KD.ThU.slp1 "Certificates/Kernel/ThU/data/slp1.items" 1000
  1117 14407977994090521664
#kc_repo #kc_list_root CFSG.KD.ThU.slp2 "Certificates/Kernel/ThU/data/slp2.items" 1000
  1185 15840984221441473336
#kc_repo #kc_items_root CFSG.KD.ThU.PTS "Certificates/Kernel/ThU/data/pts.items"
  1400 10870978053755254036
#kc_repo #kc_items_root CFSG.KD.ThU.TC "Certificates/Kernel/ThU/data/tcs.items"
  122 5161204274327578067
#kc_repo #kc_items_root CFSG.KD.ThU.SC "Certificates/Kernel/ThU/data/scs.items"
  98 7693331501198036587
#kc_repo #kc_nat_items CFSG.KD.ThU "Certificates/Kernel/ThU/data/consts.items"
  101 2433818553685924461 PR BL GR M n1 nend

namespace CFSG.KD.ThU

@[expose] noncomputable def PT (o : Nat) : Nat → Nat := fun k => PTS (o + k)

@[expose] def blocks : List (Nat × Nat × Nat × Nat) :=
  [(0, 0, 1, 3), (3, 1, 3, 3), (12, 3, 5, 3), (21, 5, 6, 3), (24, 6, 7, 3), (27, 7, 8, 3),
    (30, 8, 9, 3), (33, 9, 10, 3), (36, 10, 12, 2)]

end CFSG.KD.ThU

end
