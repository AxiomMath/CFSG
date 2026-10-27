module

public import Certificates.Data.Kernel.ThRank10508.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.ThRk10508 "Certificates/Kernel/Th/Rank10508/data/L.items.gz"
    95268 16243392093392414290
    (L 0 12)
#kc_select CFSG.KD.ThRk10508 LB L 12

namespace CFSG.KD.ThRk10508

@[expose] def Cl : List Nat :=
  [0, 1, 24, 25, 160, 161, 184, 185, 326, 327, 350, 351, 486, 487, 510, 511]

@[expose] def Ks : List Nat := [76, 0, 0, 76, 40, 102, 96, 40, 74, 68, 68, 74]

@[expose] def Es : List Nat :=
  [374182135485765, 93549841696020, 23387460424005, 1496728541943060, 92721118467156,
    5570926232913, 22283704931652, 23180279616789, 74378727765, 22874589161132369,
    91498356644529476, 297514911060]

@[expose] def Ws : List Nat := [25, 24, 23, 26, 24, 22, 23, 23, 19, 28, 29, 20]

@[expose] def Ds : List (List Nat) :=
  [[0, 1, 24, 25, 486, 487, 510, 511], [0, 1, 24, 25, 486, 487, 510, 511],
    [0, 1, 24, 25, 486, 487, 510, 511], [0, 1, 24, 25, 486, 487, 510, 511],
    [0, 1, 24, 25, 160, 161, 184, 185], [0, 1, 24, 25, 160, 161, 184, 185],
    [0, 1, 24, 25, 160, 161, 184, 185], [0, 1, 24, 25, 160, 161, 184, 185],
    [0, 1, 24, 25, 326, 327, 350, 351], [0, 1, 24, 25, 326, 327, 350, 351],
    [0, 1, 24, 25, 326, 327, 350, 351], [0, 1, 24, 25, 326, 327, 350, 351]]

@[expose] def Ts : List Nat := [1, 2, 5, 6, 9, 10]

end CFSG.KD.ThRk10508

end
