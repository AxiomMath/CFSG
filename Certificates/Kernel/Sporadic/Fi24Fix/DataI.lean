module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import Certificates.Data.CFSGNative.Fi24.Data
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.StrChunks

#kc_repo #kc_ktree CFSG.KD.Fi24Fix CTT "Certificates/Kernel/Sporadic/Fi24Fix/data/digits.bin" 512 4 33396 6201639572807327096

public section

set_option maxRecDepth 10000000

#str_chunks CFSG.KD.Fi24Fix.IA CFSG.Sporadic.Fi24.Native.initData 65536 10000000 1024

namespace CFSG.KD.Fi24Fix

@[expose] noncomputable def CT (t : Nat) : Nat :=
  fld(CTT (Nat.shiftRight t (nat_lit 9)), Nat.mul (Nat.land t (nat_lit 511)) (nat_lit 8), nat_lit 255)

end CFSG.KD.Fi24Fix

end
