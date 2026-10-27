module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Data.Kernel.WittFix

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.Enum CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl

@[expose] noncomputable def fix7T (e : List Nat) (y : Nat) : Bool :=
  bAnd(fixL e y, bAnd(Nat.ble (nat_lit 7) (fixC y), bIf(Nat.beq y I, false, true)))

@[expose] noncomputable def trOK (e : List Nat) (w : List Bool) : Bool :=
  strictB (pwp A B I w) fun D =>
    bAnd(Nat.beq (pt D (e.getD (nat_lit 0) (nat_lit 0))) (nat_lit 0),
      bAnd(Nat.beq (pt D (e.getD (nat_lit 1) (nat_lit 0))) (nat_lit 1),
        bAnd(Nat.beq (pt D (e.getD (nat_lit 2) (nat_lit 0))) (nat_lit 2),
          Nat.beq (wcB (fix7T e) D (fun x => Nat.beq x (e.getD (nat_lit 0) (nat_lit 0)))
            (fun _ x => Nat.beq x (e.getD (nat_lit 1) (nat_lit 0)))
            (fun _ _ x => Nat.beq x (e.getD (nat_lit 2) (nat_lit 0)))) (nat_lit 0))))

@[expose] noncomputable def trAll (L : List (List Nat × List Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(trOK p.1 p.2, ih)) L

end CertificateChecks.KernelLC.Witt

end
