module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.Loop

#kc_repo #kc_ktree CFSG.KD.RouteP CG "Certificates/Kernel/RouteP/Text/data/covergens.bin" 4096 4 2455488 11097566736004829424
#kc_repo #kc_ktree CFSG.KD.RouteP PXT "Certificates/Kernel/RouteP/Text/data/planesx.bin" 4096 4 85536 18278442703540884355
#kc_repo #kc_ktree CFSG.KD.RouteP PGT "Certificates/Kernel/RouteP/Text/data/planegens.bin" 4096 4 60588 14753191158047957107

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def CGR (p : Nat) : Nat :=
  fld(CG (Nat.shiftRight p (nat_lit 9)), Nat.mul (Nat.land p (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def CGD (k p : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), Nat.succ (fld(CGR p, nat_lit 0, nat_lit 524287)),
    nIf(Nat.beq k (nat_lit 1), fld(CGR p, nat_lit 19, nat_lit 3),
      nIf(Nat.beq k (nat_lit 2), Nat.succ (fld(CGR p, nat_lit 32, nat_lit 524287)),
        fld(CGR p, nat_lit 51, nat_lit 3))))

@[expose] noncomputable def rec32 (T : Nat → Nat) (r : Nat) : Nat :=
  fld(T (Nat.shiftRight r (nat_lit 10)), Nat.mul (Nat.land r (nat_lit 1023)) (nat_lit 32),
    nat_lit 4294967295)

@[expose] noncomputable def PXE (i j : Nat) : Nat := rec32 PXT (Nat.add (Nat.mul i (nat_lit 24)) j)

@[expose] noncomputable def PGE (i j : Nat) : Nat := rec32 PGT (Nat.add (Nat.mul i (nat_lit 891)) j)

end CFSG.KD.RouteP
