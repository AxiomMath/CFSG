module

public import Certificates.Kernel.S63K.IData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Kernel.S63K.GData
public import Certificates.Data.Kernel.S63K.Pick
public import Certificates.Data.Kernel.S63K.Sorted
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.KK

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CertificateChecks.KernelS63

@[expose] noncomputable def lineIs (v a b : Nat) : Bool :=
  bAnd(Nat.beq (HD.lp v 0) 0, bAnd(Nat.beq (HD.lp v 1) a, Nat.beq (HD.lp v 2) b))

@[expose] noncomputable def pl0 (k : Nat) : Nat := pg 12 (mask 12) (GD.G 0) k

@[expose] noncomputable def kleinAt (l : Nat) : Bool :=
  bAnd(eqM (CFSG.KC.F2W.mulW 24 (ID.ZP (HD.lp l 0)) (ID.ZP (HD.lp l 1))) (ID.ZP (HD.lp l 2)),
    eqM (CFSG.KC.F2W.mulW 24 (ID.ZP (HD.lp l 1)) (ID.ZP (HD.lp l 0))) (ID.ZP (HD.lp l 2)))

@[expose] noncomputable def klAt (q : Nat) : Bool :=
  bIf(Nat.beq q 0, true,
    strictB (Nat.mod (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q)) (2 ^ 576)) fun y =>
    bIf(Nat.beq y (Nat.mod (CFSG.KC.F2W.mulW 24 (ID.ZP q) (ID.ZP 0)) (2 ^ 576)),
      bIf(Nat.beq (memS ID.ZP ID.ZS 819 y) 0, true,
        strictB (ID.ZS (bsK ID.ZP ID.ZS y 32 0 819)) fun r =>
          bAnd(Nat.blt r 819, bAnd(Nat.beq (ID.ZP r) y,
            (List.range 9).any fun k => lineIs (pl0 k) (min q r) (max q r)))),
      true))

theorem ch4239L : (allN 2457 fun l => kleinAt l) = true := by quickRfl

theorem ch4239Q : (allN 819 fun q => klAt q) = true := by quickRfl

end CertificateChecks.KernelS63.KK

end
