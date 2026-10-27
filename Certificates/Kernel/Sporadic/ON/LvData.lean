module

public import Certificates.Kernel.Sporadic.ON.GenLv
public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Data.Kernel.Spor.CBfsK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

meta def baseM : Array Nat := CFSG.ONSchreier.Data.baseList.toArray

end CertificateChecks.KernelSpor.ON

#kon_levels CertificateChecks.KernelSpor.ONL CertificateChecks.KernelSpor.ON.strongM
  CertificateChecks.KernelSpor.ON.baseM 3

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB

@[expose] noncomputable def bK (i : Nat) : Nat := List.getD CFSG.ONSchreier.Data.baseList i 0

@[expose] noncomputable def off (i : Nat) : Nat :=
  nIf(Nat.beq i 0, nat_lit 0, nIf(Nat.beq i 1, nat_lit 2, nat_lit 5))

@[expose] noncomputable def len (i : Nat) : Nat :=
  nIf(Nat.beq i 0, nat_lit 7, nIf(Nat.beq i 1, nat_lit 5, nIf(Nat.beq i 2, nat_lit 2, nat_lit 0)))

@[expose] noncomputable def stepF (i j x : Nat) : Nat :=
  nIf(Nat.blt j (len i), TT (Nat.add (off i) j) x, UU (Nat.add (off i) (Nat.sub j (len i))) x)

@[expose] noncomputable def invF (i j x : Nat) : Nat :=
  nIf(Nat.blt j (len i), UU (Nat.add (off i) j) x, TT (Nat.add (off i) (Nat.sub j (len i))) x)

@[expose] noncomputable def Mf (i : Nat) : Nat :=
  nIf(Nat.beq i 0, ONL.M0, nIf(Nat.beq i 1, ONL.M1, nIf(Nat.beq i 2, ONL.M2, nat_lit 1)))

@[expose] noncomputable def PTSf (i k : Nat) : Nat :=
  nIf(Nat.beq i 0, tab ONL.PTS0 k, nIf(Nat.beq i 1, tab ONL.PTS1 k, nIf(Nat.beq i 2, tab ONL.PTS2 k,
    bK i)))

@[expose] noncomputable def POSf (i z : Nat) : Nat :=
  nIf(Nat.beq i 0, tab ONL.POS0 z, nIf(Nat.beq i 1, tab ONL.POS1 z, nIf(Nat.beq i 2, tab ONL.POS2 z,
    nIf(Nat.beq z (bK i), nat_lit 0, nat_lit 245520))))

@[expose] noncomputable def PARf (i k : Nat) : Nat :=
  nIf(Nat.beq i 0, tab ONL.PAR0 k, nIf(Nat.beq i 1, tab ONL.PAR1 k, nIf(Nat.beq i 2, tab ONL.PAR2 k,
    nat_lit 0)))

@[expose] noncomputable def LABf (i k : Nat) : Nat :=
  nIf(Nat.beq i 0, tab ONL.LAB0 k, nIf(Nat.beq i 1, tab ONL.LAB1 k, nIf(Nat.beq i 2, tab ONL.LAB2 k,
    nat_lit 0)))

@[expose] noncomputable def ptS (i s : Nat) : Bool :=
  cbPtRange (nat_lit 245520) (Mf i) (Nat.mul (nat_lit 2) (len i)) (stepF i) (PTSf i) (POSf i)
    (PARf i) (LABf i) (Nat.mul s (nat_lit 240)) (nat_lit 240)

@[expose] noncomputable def pt0S (s : Nat) : Bool := ptS (nat_lit 0) s

@[expose] noncomputable def pt1S (s : Nat) : Bool := ptS (nat_lit 1) s

@[expose] noncomputable def pt2S (s : Nat) : Bool := ptS (nat_lit 2) s

@[expose] noncomputable def posS (i s : Nat) : Bool :=
  allN (nat_lit 30690) fun d => cbPos (nat_lit 245520) (Mf i) (PTSf i) (POSf i)
    (Nat.add (Nat.mul s (nat_lit 30690)) d)

@[expose] noncomputable def pos0S (s : Nat) : Bool := posS (nat_lit 0) s

@[expose] noncomputable def pos1S (s : Nat) : Bool := posS (nat_lit 1) s

@[expose] noncomputable def pos2S (s : Nat) : Bool := posS (nat_lit 2) s

@[expose] noncomputable def posT (i : Nat) : Bool :=
  bAnd(cbHead (nat_lit 245520) (Mf i) (bK i) (PTSf i) (PARf i) (LABf i),
    bAnd(cbPt (nat_lit 245520) (Mf i) (Nat.mul (nat_lit 2) (len i)) (stepF i) (PTSf i) (POSf i)
      (PARf i) (LABf i) (nat_lit 0),
    allN (nat_lit 245520) fun z => cbPos (nat_lit 245520) (Mf i) (PTSf i) (POSf i) z))

end CertificateChecks.KernelSpor.ON

end
