module

public import Certificates.Kernel.Sporadic.McLC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def cmOK : Bool :=
  allN (nat_lit 275) fun x =>
    bAnd(Nat.beq (LJ (nat_lit 0) (r32 McLK.AL x)) (r32 McLK.AL (LJ (nat_lit 0) x)),
      Nat.beq (LJ (nat_lit 2) (r32 McLK.AL x)) (r32 McLK.AL (LJ (nat_lit 2) x)))

@[expose] noncomputable def alMv : Bool :=
  bIf(allN (nat_lit 275) fun x => Nat.beq (r32 McLK.AL x) x, false, true)

@[expose] noncomputable def cmV (x : Nat) : Nat :=
  LJ (nat_lit 0) (LJ (nat_lit 2) (LJ (nat_lit 1) (LJ (nat_lit 3) x)))

@[expose] noncomputable def cmMv : Bool :=
  bAnd(bIf(allN (nat_lit 275) fun x => Nat.beq (cmV x) x, false, true),
    bIf(allN (nat_lit 275) fun x => Nat.beq (cmV x) (r32 McLK.AL x), false, true))

theorem cmOK_ok : cmOK = true := by quickRfl
theorem alMv_ok : alMv = true := by quickRfl
theorem cmMv_ok : cmMv = true := by quickRfl

end CertificateChecks.KernelSpor.McLC

end
