module

public import Certificates.Kernel.SporSch.Co2M.OrbZD
public import Certificates.Data.Kernel.SporSch.SetTree

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def ozK (i : Nat) : Bool :=
  bIf(Nat.blt i (nat_lit 56925), bAnd(strictB (OZX i) (eltK (nat_lit 2300) (nat_lit 12) (nat_lit 284)),
    bAnd(treeK (nat_lit 12) (nat_lit 284) Co2OZ.G OZX (nat_lit 2) i,
      sortMK (nat_lit 12) (nat_lit 284) OZX OZS (nat_lit 56925) i)), true)

end CertificateChecks.KernelSporSch.Co2M

end
