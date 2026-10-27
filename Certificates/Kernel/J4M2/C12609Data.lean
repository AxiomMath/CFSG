module

public import Certificates.Data.Kernel.J4Q.RRep
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QT2AData
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.J4RR

#kc_repo #kc_nat_items_gz CFSG.KD.J4RR
  "Certificates/Kernel/J4M2/data/rr12609.items.gz" 1283513 12782080997176720420
  E LO[] HI[] GL0[] GL1[] GL2[] HG0[] HG1[] HG2[] HZ0[] HZ1[] HZ2[]

@[expose] noncomputable def GLs : List (List Nat) := [GL0, GL1, GL2]

@[expose] noncomputable def HGs : List (List Nat) := [HG0, HG1, HG2]

@[expose] noncomputable def HZs : List (List Nat) := [HZ0, HZ1, HZ2]

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4RR in
@[expose] noncomputable def rrIdx (idx : Nat) : Bool := rrIdxK c rm ZM LO HI GLs HGs HZs E idx

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4RR in
@[expose] noncomputable def rrBlk (k : Nat) : Bool := rrBlkK c rm ZM LO HI GLs HGs HZs E k

@[expose] noncomputable def rrBlkLo (k : Nat) : Bool := rrBlk k

@[expose] noncomputable def rrBlkHi (k : Nat) : Bool := rrBlk (32 + k)

end CFSG.KD.J4RR

end
