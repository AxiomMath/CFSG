module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK
public import Certificates.Data.Kernel.Spor.Fi24G2d

#kc_repo #kc_ktree CFSG.KD.Fi24G2d FLT "Certificates/Kernel/Sporadic/Fi24G2d/data/fix.bin" 3072 4 6144 15468354031306618739
#kc_repo #kc_natList CFSG.KD.Fi24G2d K2C "Certificates/Kernel/Sporadic/Fi24G2d/data/K2C.txt" 298 9420623175708812646
#kc_repo #kc_natList CFSG.KD.Fi24G2d K2A "Certificates/Kernel/Sporadic/Fi24G2d/data/K2A.txt" 202 10306730744757999555
#kc_repo #kc_natList CFSG.KD.Fi24G2d K2D "Certificates/Kernel/Sporadic/Fi24G2d/data/K2D.txt" 171 9087386211145172180
#kc_repo #kc_natList CFSG.KD.Fi24G2d K2B "Certificates/Kernel/Sporadic/Fi24G2d/data/K2B.txt" 170 17401110211972761528

public section

namespace CFSG.KD.Fi24G2d

@[expose] def WN : List Nat := []

@[expose] def W2C : List Nat := [2]

@[expose] def W2A : List Nat := [0, 2]

@[expose] def W2D : List Nat := [0, 2, 4]

@[expose] def W2B : List Nat := [0, 2, 4, 6]

@[expose] noncomputable def F2B (j : Nat) : Nat :=
  fld(FLT (nat_lit 0), Nat.mul j (nat_lit 24), nat_lit 16777215)

@[expose] noncomputable def F2D (j : Nat) : Nat :=
  fld(FLT (nat_lit 1), Nat.mul j (nat_lit 24), nat_lit 16777215)

end CFSG.KD.Fi24G2d

end
