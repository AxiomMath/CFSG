module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Fix.Data
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.Sel
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.SelJL
public import Certificates.Data.Kernel.Spor.Fi24FixK

#kc_repo #kc_ktree CFSG.KD.Fi24Fix XT "Certificates/Kernel/Sporadic/Fi24Fix/data/clos.bin" 512 4 570078 2173058401473398647

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KD.FamFi24Act

@[expose] noncomputable def IX (r : Nat) : Nat :=
  fld(XT (Nat.shiftRight r (nat_lit 8)), Nat.mul (Nat.land r (nat_lit 255)) (nat_lit 16),
    nat_lit 65535)

@[expose] noncomputable def TG (g i : Nat) : Nat :=
  nIf(Nat.beq g (nat_lit 0), T0 i, nIf(Nat.beq g (nat_lit 1), T1 i, nIf(Nat.beq g (nat_lit 2), T2 i,
  nIf(Nat.beq g (nat_lit 3), T3 i, nIf(Nat.beq g (nat_lit 4), T4 i, nIf(Nat.beq g (nat_lit 5), T5 i,
  nIf(Nat.beq g (nat_lit 6), T6 i, nIf(Nat.beq g (nat_lit 7), T7 i, nIf(Nat.beq g (nat_lit 8), T8 i,
  nIf(Nat.beq g (nat_lit 9), TJ i, nIf(Nat.beq g (nat_lit 10), T9 i, TL i)))))))))))

@[expose] def PW : List Nat :=
  [9, 6, 5, 4, 3, 2, 1, 0, 10, 11, 7, 8, 3, 7, 4, 3, 2, 1, 0, 10, 3, 7, 4, 5, 3, 4, 2, 3, 7, 2, 1, 0]

@[expose] def AW : List Nat := [11, 0, 8, 0]

@[expose] noncomputable def R1 : Nat := Nat.land R CFSG.KD.BrFi24.LO

@[expose] noncomputable def R2 : Nat := Nat.shiftRight R (nat_lit 609961)

end CFSG.KD.Fi24Fix

end
