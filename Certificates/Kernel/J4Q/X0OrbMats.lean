module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.X0OrbData
import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.X0O

@[expose] def root : Bool × Nat × Nat × Nat := (true, CFSG.KD.J4Q.one, 0, 0)

@[expose] noncomputable def run (_ : List Nat) (k : Nat) (s : Bool × Nat × Nat × Nat) :
    Bool × Nat × Nat × Nat :=
  (true, CFSG.KC.J4Q.mulJ CFSG.KD.J4Q.c CFSG.KD.J4Q.rm s.2.1
    (CFSG.KC.J4Q.getN CFSG.KD.J4Q.one CFSG.KD.J4Q.XG (Nat.land (Nat.shiftRight k 20) 1048575)), 0, 0)

end CFSG.KD.X0O

end

#kc_chain CFSG.KD.X0O CFSG.KD.X0O.run "x0orb.plan.txt" 223021 1037156666053900029

#kc_select CFSG.KD.X0O MSF X 6720
