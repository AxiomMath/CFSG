module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QTData
import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.ETA

@[expose] def root : Bool × Nat × Nat × Nat := (true, CFSG.KD.J4Q.one, 0, 0)

@[expose] def us : List Nat :=
  [CFSG.KD.J4Q.U0, CFSG.KD.J4Q.U1, CFSG.KD.J4Q.U2, CFSG.KD.J4Q.U3, CFSG.KD.J4Q.U4, CFSG.KD.J4Q.U5,
    CFSG.KD.J4Q.U6, CFSG.KD.J4Q.U7, CFSG.KD.J4Q.U8, CFSG.KD.J4Q.U9, CFSG.KD.J4Q.U10]

@[expose] noncomputable def run (_ : List Nat) (k : Nat) (s : Bool × Nat × Nat × Nat) :
    Bool × Nat × Nat × Nat :=
  (true, CFSG.KC.J4Q.mulJ CFSG.KD.J4Q.c CFSG.KD.J4Q.rm s.2.1
    (CFSG.KC.J4Q.getN CFSG.KD.J4Q.one us (Nat.land (Nat.shiftRight k 20) 1048575)), 0, 0)

end CFSG.KD.ETA

end

#kc_chain CFSG.KD.ETA CFSG.KD.ETA.run "eta.plan.txt" 66220 16299135465146397507

#kc_select CFSG.KD.ETA EF X 2048
