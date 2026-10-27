module

public import Certificates.Kernel.Sporadic.ONW.Data
public import Certificates.Kernel.Sporadic.ON.Data
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON
open CertificateChecks.KernelSpor.ON (TT UU)

@[expose] noncomputable def PT (x : Nat) : Nat := tab ONWT.P x

@[expose] noncomputable def UT (x : Nat) : Nat := tab ONWT.U x

@[expose] noncomputable def Y (k x : Nat) : Nat := trace TT UU (ONWW.WC k) (ONWW.WL k) x

@[expose] noncomputable def uIt (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih UT) e

@[expose] noncomputable def ptAt (x : Nat) : Bool :=
  strictB (PT x) fun p => strictB (UT x) fun u =>
    bAnd(Nat.beq p (Y 0 (Y 1 x)), bAnd(Nat.beq u (PT (PT p)),
      Nat.beq (UT (UT (UT (UT u)))) x))

@[expose] noncomputable def chkS (s : Nat) : Bool :=
  allN (nat_lit 2046) fun i => ptAt (Nat.add (Nat.mul s (nat_lit 2046)) i)

@[expose] noncomputable def neOK : Bool :=
  bAnd(CFSG.KLie.CT.anyN (nat_lit 245520) (fun x => bIf(Nat.beq (UT x) x, false, true)),
    allN (nat_lit 4) fun k => CFSG.KLie.CT.anyN (nat_lit 245520) fun x =>
      bIf(Nat.beq (Y 0 (UT x)) (uIt (Nat.succ k) (Y 0 x)), false, true))

end CertificateChecks.KernelSpor.ONW

end
