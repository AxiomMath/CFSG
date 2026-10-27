module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Kernel.Misc.GL4.EAData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4Cls CW
  "Certificates/Kernel/Misc/GL4/Cls/data/cw.bin" 4 4 80640 6533662977534425703
#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4Cls CB
  "Certificates/Kernel/Misc/GL4/Cls/data/cb.bin" 4 4 161280 10008691819578716409

namespace CertificateChecks.KernelMisc.GL4Cls

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.GL4
open CertificateChecks.KernelMisc.GL4EA (EA)

@[expose] noncomputable def clA0 (i : Nat) : Nat := lAt [5160, 4680] i

@[expose] noncomputable def clX (f : Nat) : Nat := lAt [8580, 18479] f

@[expose] noncomputable def clY (f : Nat) : Nat := lAt [32306, 9240] f

@[expose] noncomputable def invWit (a w : Nat) : Bool :=
  letB (fld w (nat_lit 0) (nat_lit 15)) fun j => letB (Nat.shiftRight w (nat_lit 15)) fun i =>
    andB (Nat.blt j (nat_lit 20160)) (andB (Nat.blt i (nat_lit 2))
      (Nat.beq (mul4F (EA j) a) (mul4F (clA0 i) (EA j))))

@[expose] noncomputable def pairWit (x b w : Nat) : Bool :=
  letB (fld w (nat_lit 0) (nat_lit 15)) fun h => letB (Nat.shiftRight w (nat_lit 15)) fun f =>
    andB (Nat.blt h (nat_lit 20160)) (andB (Nat.blt f (nat_lit 2))
      (andB (Nat.beq (mul4F (EA h) x) (mul4F (clX f) (EA h)))
        (Nat.beq (mul4F (EA h) b) (mul4F (clY f) (EA h)))))

@[expose] noncomputable def clAt (k : Nat) : Bool :=
  letB (EA k) fun a => letB (mul4F a a) fun a2 =>
    andB (impB (andB (Nat.beq a2 id4) (notB (Nat.beq a id4))) (invWit a (CW k)))
      (impB (Nat.beq (mul4F a2 a) id4) (allN (nat_lit 2) fun i =>
        impB (Nat.beq (pow4F (mul4F (clA0 i) a) (nat_lit 5)) id4)
          (pairWit (clA0 i) a (CB (Nat.add (Nat.mul (nat_lit 2) k) i)))))

@[expose] noncomputable def clS (s : Nat) : Bool := allR (Nat.mul (nat_lit 5040) s) (nat_lit 5040) clAt

end CertificateChecks.KernelMisc.GL4Cls

end
