module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi23K TR "Certificates/Kernel/Fi23K/data/trees.bin" 128 4 2331904 6258477217162204088

public section

namespace CFSG.KD.Fi23K

@[expose] noncomputable def off (i t : Nat) : Nat :=
  List.getD (List.getD [[0, 990, 1980, 2970, 3960], [4950, 5060, 6050, 6160, 6270],
    [6380, 7172, 8162, 8954, 9746], [10538, 10547, 11537, 11546, 11555],
    [11564, 11604, 12594, 12634, 12674], [12714, 12715, 13705, 13706, 13707],
    [13708, 14588, 15578, 16458, 17338]] i []) t (nat_lit 0)

@[expose] noncomputable def TT (i t : Nat) (r : Nat) : Nat := TR (Nat.add (off i t) r)

@[expose] noncomputable def CNT (i : Nat) : Nat :=
  List.getD [31671, 3510, 25344, 288, 1260, 4, 28160] i (nat_lit 0)

end CFSG.KD.Fi23K
