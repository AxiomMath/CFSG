module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24NetPt

#kc_repo #kc_ktree CFSG.KD.Fi24Net PTab "Certificates/Kernel/Sporadic/Fi24Net/data/ptab.bin" 4096 4 31948800 979299285210845299

public section

namespace CFSG.KD.Fi24Net

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt

@[expose] noncomputable def PTj (j c : Nat) : Nat := PTab (Nat.add (Nat.mul j (nat_lit 600)) c)

@[expose] noncomputable def NWr (j l : Nat) : Nat := NW j (Nat.sub (nat_lit 36) l)

@[expose] noncomputable def ptRec (j x : Nat) : Nat :=
  fld(PTj j (Nat.shiftRight x (nat_lit 9)), Nat.mul (Nat.land x (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def letPT (l x : Nat) : Nat :=
  nIf(andB (Nat.blt x (nat_lit 306936)) (Nat.blt l (nat_lit 26)),
    strictN (ptRec (Nat.shiftRight l (nat_lit 1)) x) (fun e =>
      nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), Nat.land e (nat_lit 524287),
        Nat.land (Nat.shiftRight e (nat_lit 19)) (nat_lit 524287))),
    letN NW l x)

@[expose] noncomputable def tckF (g : Nat) : Bool :=
  (fun j => genOK (PTj j) (NW j) (nat_lit 0) (Nat.mod g (nat_lit 19))) (Nat.div g (nat_lit 19))

@[expose] noncomputable def tckR (g : Nat) : Bool :=
  (fun j => genOK (PTj j) (NWr j) (nat_lit 19) (Nat.mod g (nat_lit 19))) (Nat.div g (nat_lit 19))

end CFSG.KD.Fi24Net

end
