module

public import Certificates.Kernel.SporSch.PairJ3.CntFns
public import Certificates.Data.Kernel.SporSch.PairJ3WScan

public section

namespace CertificateChecks.KernelSporSch.PJ3W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def ziP (x : Nat) : Nat := powF PJ3Cn.zP (nat_lit 18) x

@[expose] noncomputable def zi2P (x : Nat) : Nat := powF PJ3Cn.zP (nat_lit 17) x

@[expose] noncomputable def scAt (Z ZI : Nat → Nat) (q : Nat) : Nat :=
  scanJR 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3Cn.bs PJ3T.c PJ3Cl.X Z ZI (Nat.mul q (nat_lit 512))
    (nat_lit 512)

@[expose] def VW (q : Nat) : Nat := [15, 3, 1].getD q 0

@[expose] def VW2 (q : Nat) : Nat := [10, 2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1].getD q 0

@[expose] noncomputable def scW (g r : Nat) : Bool :=
  Nat.beq (scAt PJ3Cn.zP ziP (Nat.add (Nat.mul g 4) r)) (VW (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def scW2 (g r : Nat) : Bool :=
  Nat.beq (scAt PJ3Cn.z2P zi2P (Nat.add (Nat.mul g 4) r)) (VW2 (Nat.add (Nat.mul g 4) r))

end CertificateChecks.KernelSporSch.PJ3W

end
