module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTF1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCT

open CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KC.Misc.HexAt CFSG.Sporadic.SuzOddCore

set_option Elab.async false

theorem neg_sig : Bool.not (sigK 42 fix0L (SuzInvT0.F 33) (K0E.G 0) (K0I 0)) = true := by
  quickRfl

theorem neg_kpt : Bool.not (penumPtK 42 6 (mask 6) (42 * 6) false
    (fun j => K0E.G (nIf(Nat.beq j 0, 1, nIf(Nat.beq j 1, 0, j)))) K0E.GI 22 K0E.cnt K0E.T K0E.PL
    K0E.POS K0E.SRT K0E.SRI 5) = true := by quickRfl

theorem neg_dpt : Bool.not (penumPtK 42 6 (mask 6) (42 * 6) false DE.G DE.GI 5 DE.cnt
    (fun i => DE.T (Nat.succ i)) DE.PL DE.POS DE.SRT DE.SRI 7) = true := by quickRfl

theorem neg_qpt : Bool.not (penumPtK 54 6 (mask 6) (54 * 6) false QE.G QE.GI 6 QE.cnt
    (fun i => QE.T (Nat.succ i)) QE.PL QE.POS QE.SRT QE.SRI 3) = true := by quickRfl

theorem neg_cover : Bool.not (strictB (COV 100) (fun wk =>
    Nat.beq (offF OF.T (OF.TO (Nat.succ (Nat.shiftRight wk 16))) (Nat.land wk 65535))
      (DE.T 100))) = true := by quickRfl

theorem neg_act : Bool.not (allN 64 (fun p => strictB (pg 7 (mask 7) (AC.S 2) p) (fun q =>
    bAnd(Nat.blt q 64, Nat.beq (QE.T q)
      (pcomp 54 6 (mask 6) (pcomp 54 6 (mask 6) (K1C.S 3) (QE.T p)) (K1I 3)))))) = true := by
  quickRfl

theorem neg_sig1 : Bool.not (sigK 54 fix1L (SuzInvT1.F 18) (K1C.S 0) (K1I 1)) = true := by
  quickRfl

theorem neg_head : Bool.not (headK 54 6 (mask 6) (54 * 6) (pidn 54 6) K1C.S K1C.SI 18 10
    actWords 6 K1C.BP) = true := by quickRfl

theorem neg_prod : Bool.not (Nat.beq (((List.range 5).map fun i => rcnt (K1C.LR i)).prod)
    1658880) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzCT

end
