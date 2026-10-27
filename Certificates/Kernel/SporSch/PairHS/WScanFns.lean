module

public import Certificates.Kernel.SporSch.PairHS.CntFns
public import Certificates.Data.Kernel.SporSch.PairHSWScan

public section

namespace CertificateChecks.KernelSporSch.PHSW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def scAt (Z ZI : Nat → Nat) (q : Nat) : Nat :=
  scanWR 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSCn.bs PHST.c PHSCl.XA Z ZI (Nat.mul q (nat_lit 512))
    (nat_lit 512)

@[expose] def VZ (q : Nat) : Nat := [2, 1, 1, 1, 0, 2, 1, 1, 1, 0, 1, 0].getD q 0

@[expose] noncomputable def scZ (g r : Nat) : Bool :=
  Nat.beq (scAt PHSCn.zP PHSCn.ziP (Nat.add (Nat.mul g 4) r)) (VZ (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def scZI (g r : Nat) : Bool :=
  Nat.beq (scAt PHSCn.ziP PHSCn.zP (Nat.add (Nat.mul g 4) r)) (VZ (Nat.add (Nat.mul g 4) r))

end CertificateChecks.KernelSporSch.PHSW

end
