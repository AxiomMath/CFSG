module

public import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Sporadic.Schreier.ONCheckChainInputs
public meta import CFSG.Sporadic.Schreier.ONCheckChainInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

meta def orbM : CFSG.Sporadic.ON.Native.VOrbit :=
  CFSG.ONSchreier.Native.vorbit (CFSG.ONSchreier.Native.digitsW CFSG.ONSchreier.Data.rootDigits)

meta def strongM : Array (Array Nat) := CFSG.ONSchreier.qonStrongArrs

meta def colsAM : Array CFSG.Sporadic.Fi23.Native.W := CFSG.Sporadic.ON.Native.colsA

meta def colsBM : Array CFSG.Sporadic.Fi23.Native.W := CFSG.Sporadic.ON.Native.colsB

end CertificateChecks.KernelSpor.ON

#kon_data CertificateChecks.KernelSpor.ONV CertificateChecks.KernelSpor.ON.orbM
  CertificateChecks.KernelSpor.ON.strongM CertificateChecks.KernelSpor.ON.colsAM
  CertificateChecks.KernelSpor.ON.colsBM CFSG.ONSchreier.Data.strongWords 240

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def TT (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tab ONV.A i, nIf(Nat.beq h 1, tab ONV.B i, nIf(Nat.beq h 2, tab ONV.T2 i,
    nIf(Nat.beq h 3, tab ONV.T3 i, nIf(Nat.beq h 4, tab ONV.T4 i, nIf(Nat.beq h 5, tab ONV.T5 i,
      tab ONV.T6 i))))))

@[expose] noncomputable def UU (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tab ONV.U0 i, nIf(Nat.beq h 1, tab ONV.U1 i, nIf(Nat.beq h 2, tab ONV.U2 i,
    nIf(Nat.beq h 3, tab ONV.U3 i, nIf(Nat.beq h 4, tab ONV.U4 i, nIf(Nat.beq h 5, tab ONV.U5 i,
      tab ONV.U6 i))))))

@[expose] noncomputable def mvS (s : Nat) : Bool :=
  mvRange ONV.K ONV.LA ONV.LB ONV.A ONV.B (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

@[expose] noncomputable def ordS (s : Nat) : Bool :=
  Nat.beq (ordRun ONV.A ONV.B (Nat.mul s (nat_lit 240)) (nat_lit 240) (ONV.NX s)) (ONV.NX (Nat.succ s))

@[expose] noncomputable def sortS (s : Nat) : Bool :=
  sortRange ONV.K ONV.SO ONV.SOI (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

@[expose] noncomputable def trS (s : Nat) : Bool :=
  trRange TT UU ONV.WC ONV.WL (nat_lit 245520) (nat_lit 7) (nat_lit 2) (Nat.mul s (nat_lit 240))
    (nat_lit 240)

end CertificateChecks.KernelSpor.ON

end
