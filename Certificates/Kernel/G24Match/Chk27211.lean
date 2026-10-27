module

public import Certificates.Kernel.EvenSporG24.TblText
public import Certificates.Kernel.G24Match.Pack27211
public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Data.Kernel.G24Key
public import Certificates.Data.Kernel.DigitScan
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.Match27211

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G24Key CFSG.KC.DigitScan
  CertificateChecks.KernelG24.Tri27206

@[expose] def wdN : Nat := 0xADB3F5515155

@[expose] noncomputable def f27211 (i v : Nat) : Bool :=
  bIf(Nat.blt i (nat_lit 5866), true,
  bIf(Nat.blt i (nat_lit 27706), strictB (Nat.sub i (nat_lit 5866)) (fun t =>
      Nat.beq v (ap (PG (Nat.div t (nat_lit 1365))) (Nat.mod t (nat_lit 1365)))),
  Nat.beq v (Nat.land (Nat.shiftRight wdN (Nat.mul (nat_lit 4) (Nat.sub i (nat_lit 27706))))
    (nat_lit 15))))

@[expose] noncomputable def prodWa : Nat :=
  pcomp 1365 11 (mask 11) (PG 5) (pcomp 1365 11 (mask 11) (PG 1) (pcomp 1365 11 (mask 11) (PG 5)
    (pcomp 1365 11 (mask 11) (PG 1) (pcomp 1365 11 (mask 11) (PG 5) (pidn 1365 11)))))

@[expose] noncomputable def prodWb : Nat :=
  pcomp 1365 11 (mask 11) (PG 15) (pcomp 1365 11 (mask 11) (PG 3) (pcomp 1365 11 (mask 11) (PG 11)
    (pcomp 1365 11 (mask 11) (PG 13) (pcomp 1365 11 (mask 11) (PG 10) (pidn 1365 11)))))

theorem kText : scanK f27211 (nat_lit 27718) CertificateChecks.EvenSporG24.G24T.chars = true := by
  quickRfl
theorem kCan : allN 16 (fun k => canonK 1365 11 (mask 11) (1365 * 11) (PG k)) = true := by quickRfl
theorem kWa : Nat.beq prodWa (LC.S 0) = true := by quickRfl
theorem kWb : Nat.beq prodWb (LC.S 1) = true := by quickRfl

end CertificateChecks.KernelG24.Match27211
