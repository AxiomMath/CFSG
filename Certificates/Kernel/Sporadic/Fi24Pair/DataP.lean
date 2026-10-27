module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Pair.Data
public import Certificates.Data.Kernel.Spor.Fi24PairP

#kc_repo #kc_ktree CFSG.KD.Fi24Pair CF "Certificates/Kernel/Sporadic/Fi24Pair/data/cf.bin" 65536 4 2424832 1791521532310076560

public section

namespace CFSG.KD.Fi24Pair

open CFSG.KC.Fi24PairP

@[expose] noncomputable def cfc : Bool := cfOK CF FP

@[expose] noncomputable def sgp (k : Nat) : Bool :=
  sigP CFSG.KD.Fi24Net.NW CF (NT k) (Nat.add (nat_lit 8) k)

end CFSG.KD.Fi24Pair

end
