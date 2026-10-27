module

public import Certificates.Kernel.Fi24Rk.Data
public import Certificates.Kernel.Sporadic.Fi24K.K2077
public import Certificates.Data.Kernel.Fi22Rk.Defs
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi24Rk.K

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Raw CertificateChecks.KernelFi24Rk
open CertificateChecks.KernelSpor

@[expose] noncomputable def stab (c : Nat) : Bool :=
  allN (nat_lit 64) fun r => strictB (Nat.add (Nat.mul (nat_lit 64) c) r) fun q =>
    bIf(Nat.blt q (nat_lit 504), stabAt 9 D.IK D.SMK q, true)

theorem cls : classK 504 32 D.SMK D.CLK D.CMK = true := by quickRfl

theorem blk : blockK 504 D.CLK D.POK D.POIK D.STK = true := by quickRfl

@[expose] noncomputable def uniq (c : Nat) : Bool :=
  allN (nat_lit 64) fun r => strictB (Nat.add (Nat.mul (nat_lit 64) c) r) fun q =>
    bIf(Nat.blt q (nat_lit 504), uniqAtK 9 D.IK D.CLK D.POK D.STK D.WK q, true)

@[expose] noncomputable def SK (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 5), D.AK k, D.GK (Nat.sub k (nat_lit 5)))

@[expose] noncomputable def siftF (G : Nat) : Bool :=
  siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24KC.LR Fi24KC.TRI Fi24KC.BP 7 0 G

theorem sift : allN 7 (fun k => siftF (SK k)) = true := by quickRfl

open CFSG.KLie.CT (notB) in
theorem negStab : bAnd(notB (stabAt 9 D.IK (fun q => Nat.xor (D.SMK q) (nat_lit 1)) 5),
    bAnd(notB (classK 504 32 D.SMK (fun q => Nat.succ (D.CLK q)) D.CMK),
      notB (uniqAtK 9 D.IK D.CLK D.POK D.STK (fun q => Nat.succ (D.WK q)) 0))) = true := by
  quickRfl

end CertificateChecks.KernelFi24Rk.K

#kc_each CertificateChecks.KernelFi24Rk.K.stab 0 8
#kc_each CertificateChecks.KernelFi24Rk.K.uniq 0 8

end
