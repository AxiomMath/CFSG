module

public import Certificates.Kernel.S63K.HData
public import Certificates.Data.Kernel.S63K.Low
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.HD

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def im (k x : Nat) : Nat := pg 12 (mask 12) (PA k) x

@[expose] noncomputable def ptW (w : List Nat) (x : Nat) : Nat := w.foldr im x

@[expose] noncomputable def lp (l t : Nat) : Nat := pg 12 (mask 12) LT (3 * l + t)

theorem lowP : lowK PC 0 DP = true := by quickRfl

theorem lowL : lowK LC 0 DL = true := by quickRfl

theorem lenP : Nat.beq PC.length 19656 = true := by quickRfl

theorem lenL : Nat.beq LC.length 22113 = true := by quickRfl

theorem pa : (allN 8 fun j => allN 819 fun i =>
    bAnd(Nat.beq (dec3 DP (3 * (819 * j + i))) (im j i), Nat.blt (im j i) 819)) = true := by
  quickRfl

theorem lt : (allN 7371 fun i =>
    bAnd(Nat.beq (dec3 DL (3 * i)) (pg 12 (mask 12) LT i), Nat.blt (pg 12 (mask 12) LT i) 819)) =
    true := by
  quickRfl

end CertificateChecks.KernelS63.HD

end
