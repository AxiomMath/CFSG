module

public import Certificates.Kernel.Sporadic.ON2.Data
public import Certificates.Kernel.Sporadic.ON2.Words
public meta import Certificates.Data.CFSGNative.Bridge.ONGPL

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

meta def imgInvM : Array (List Int) := (CFSG.Sporadic.Bridge.ONGPL.Native.imgWords ()).map fun w =>
  w.reverse.map fun z => -z

end CertificateChecks.KernelSpor.ON2

#kon_words CertificateChecks.KernelSpor.IIW CertificateChecks.KernelSpor.ON2.imgInvM

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def ST (h x : Nat) : Nat := nIf(Nat.beq h 0, tab ONW.A x, tab ONW.B x)

@[expose] noncomputable def SU (h x : Nat) : Nat := nIf(Nat.beq h 0, tab ONW.U0 x, tab ONW.U1 x)

@[expose] noncomputable def IMG (k x : Nat) : Nat := trace ST SU (IMW.WC k) (IMW.WL k) x

@[expose] noncomputable def IMGI (k x : Nat) : Nat := trace ST SU (IIW.WC k) (IIW.WL k) x

@[expose] noncomputable def invS (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 240)) (fun i =>
    bAnd(Nat.blt (tab ONW.A i) (nat_lit 245520), bAnd(Nat.blt (tab ONW.B i) (nat_lit 245520),
    bAnd(Nat.blt (tab ONW.U0 i) (nat_lit 245520), bAnd(Nat.blt (tab ONW.U1 i) (nat_lit 245520),
    bAnd(Nat.beq (tab ONW.U0 (tab ONW.A i)) i, bAnd(Nat.beq (tab ONW.U1 (tab ONW.B i)) i,
    bAnd(Nat.beq (tab ONW.A (tab ONW.U0 i)) i, Nat.beq (tab ONW.B (tab ONW.U1 i)) i))))))))
    (nat_lit 240)

@[expose] noncomputable def cq (t : Nat) : Nat := CFSG.Sporadic.ON.Native.chainQ[t]!

@[expose] noncomputable def relQ (t : Nat) : Bool :=
  strictB (cq t) fun x => allN RLW.N fun j => Nat.beq (trace IMG IMGI (RLW.WC j) (RLW.WL j) x) x

@[expose] noncomputable def surjQ (t : Nat) : Bool :=
  strictB (cq t) fun x => bAnd(Nat.beq (trace IMG IMGI (SRW.WC 0) (SRW.WL 0) x) (tab ONW.A x),
    Nat.beq (trace IMG IMGI (SRW.WC 1) (SRW.WL 1) x) (tab ONW.B x))

end CertificateChecks.KernelSpor.ON2

end
