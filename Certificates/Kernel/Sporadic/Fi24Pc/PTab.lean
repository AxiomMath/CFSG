module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Pc.Data

#kc_repo #kc_ktree CFSG.KD.Fi24Pc XTab "Certificates/Kernel/Sporadic/Fi24Pc/data/ptab.bin" 4096 4 39321600 9813157852701324377

public section

namespace CFSG.KD.Fi24Pc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt

@[expose] noncomputable def XTj (j c : Nat) : Nat := XTab (Nat.add (Nat.mul j (nat_lit 600)) c)

@[expose] noncomputable def xtRec (j x : Nat) : Nat :=
  fld(XTj j (Nat.shiftRight x (nat_lit 9)), Nat.mul (Nat.land x (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def letPX (l x : Nat) : Nat :=
  nIf(andB (Nat.blt x (nat_lit 306936))
      (andB (Nat.blt l (nat_lit 32)) (Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0))),
    Nat.land (xtRec (Nat.shiftRight l (nat_lit 1)) x) (nat_lit 524287),
    letN XW l x)

@[expose] noncomputable def xtckF (g : Nat) : Bool :=
  (fun j => genOK (XTj j) (XW j) (nat_lit 0) (Nat.mod g (nat_lit 19))) (Nat.div g (nat_lit 19))

end CFSG.KD.Fi24Pc

end
