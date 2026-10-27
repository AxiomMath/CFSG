module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24Kit

#kc_repo #kc_ktree CFSG.KD.Fi24Kit NT "Certificates/Kernel/Sporadic/Fi24Kit/data/nett.bin" 65536 4 2424832 11818244943076483190

public section

namespace CFSG.KD.Fi24Kit

open CFSG.KC CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KD.Fi24Net

@[expose] noncomputable def wA : List Nat :=
  [0, 6, 14, 25, 16, 4, 19, 9, 9, 15, 8, 8, 22, 15, 15, 15, 24, 14, 12, 23, 24, 19]

@[expose] noncomputable def wB : List Nat :=
  [4, 16, 12, 5, 2, 11, 11, 20, 6, 13, 9, 25, 20, 18, 8, 12, 15, 13, 14, 21, 14, 16, 21, 24, 16, 24]

@[expose] noncomputable def nck : Bool := netOK NT

@[expose] noncomputable def tck (k : Nat) : Bool := tpOK NW NT wA wB k

@[expose] noncomputable def t0 : Bool := Nat.beq (ptF NT (nat_lit 0)) (nat_lit 0)

end CFSG.KD.Fi24Kit

end
