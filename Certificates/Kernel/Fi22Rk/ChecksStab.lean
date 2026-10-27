module

public import Certificates.Kernel.Fi22Rk.Data
public import Certificates.Data.Kernel.Fi22Rk.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Rk.K

open CFSG.KC.Enum CFSG.KC.Fi22Rk CertificateChecks.KernelFi22Rk

@[expose] noncomputable def stab (c : Nat) : Bool :=
  allN (nat_lit 64) fun r => strictB (Nat.add (Nat.mul (nat_lit 64) c) r) fun q =>
    bIf(Nat.blt q (nat_lit 3510), stabAt 12 D.IK D.SMK q, true)

theorem cls : classK 3510 73 D.SMK D.CLK D.CMK = true := by quickRfl

theorem blk : blockK 3510 D.CLK D.POK D.POIK D.STK = true := by quickRfl

@[expose] noncomputable def uniq (c : Nat) : Bool :=
  allN (nat_lit 64) fun r => strictB (Nat.add (Nat.mul (nat_lit 64) c) r) fun q =>
    bIf(Nat.blt q (nat_lit 3510), bIf(Nat.beq (D.PK q) (nat_lit 0),
      uniqAtK 12 D.IK D.CLK D.POK D.STK D.WK q, true), true)

theorem pos : posChk 3510 12 486 T.C.F D.PK = true := by quickRfl

open CFSG.KLie.CT (notB) in
theorem negStab : bAnd(notB (stabAt 12 D.IK (fun q => Nat.xor (D.SMK q) (nat_lit 1)) 5),
    bAnd(notB (classK 3510 73 D.SMK (fun q => Nat.succ (D.CLK q)) D.CMK),
      notB (uniqAtK 12 D.IK D.CLK D.POK D.STK (fun q => Nat.succ (D.WK q)) 0))) = true := by
  quickRfl

end CertificateChecks.KernelFi22Rk.K

#kc_each CertificateChecks.KernelFi22Rk.K.stab 0 55
#kc_each CertificateChecks.KernelFi22Rk.K.uniq 0 55

end
