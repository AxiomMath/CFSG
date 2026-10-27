module

public import Certificates.Kernel.W4C2.Data
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelW4C2

open CFSG.KC.W4C2K

@[expose] noncomputable def ch330390pn (i : Nat) : Bool :=
  (GL.getD i []).flatMap (stabPK bNK) == PNs.getD i []

@[expose] noncomputable def ch330390pm (i : Nat) : Bool :=
  (GL.getD i []).flatMap (stabPK bMK) == PMs.getD i []

#kc_each ch330390pn 0 16

#kc_each ch330390pm 0 16

theorem ch330390pnJoin : ((List.range 16).flatMap (fun i => PNs.getD i []) == PN) = true := by
  quickRfl

theorem ch330390pmJoin : ((List.range 16).flatMap (fun i => PMs.getD i []) == PM) = true := by
  quickRfl

end CertificateChecks.KernelW4C2
