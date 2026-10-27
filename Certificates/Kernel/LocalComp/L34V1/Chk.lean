module

public import Certificates.Kernel.LocalComp.L34V1.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34V1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CertificateChecks.KernelLC.L34V1G
open CFSG.KLie.CT (fget andB orB notB)

theorem k_fe : bAnd(gensK (CFSG.PSL3Four.Native.fGens ()) 42 6 FE.k FE.G, bAnd(Nat.beq FE.cnt 16,
    bAnd(penumHdK (pidn 42 6) FE.cnt 16 FE.T FE.PL,
    bAnd(penumSlK 42 6 (mask 6) (42 * 6) false FE.G FE.GI FE.k FE.cnt FE.T FE.PL FE.POS FE.SRT
      FE.SRI 0 16,
    allN 16 (fun a => allN 16 (fun b => orB (Nat.beq a b)
      (notB (Nat.beq (FE.T a) (FE.T b))))))))) = true := by
  quickRfl

theorem k_y : bAnd(allN 360 yK, bAnd(Nat.beq YI.length 46, YI.all fun y => Nat.blt y 360)) =
    true := by
  quickRfl

theorem k_fix : allN 16 (fun q => allN 6 (fun j =>
    Nat.beq (pg 6 (mask 6) (FE.T q) (FX j)) (FX j))) = true := by
  quickRfl

theorem kNegV : notB (Nat.ble (CFSG.PSL3Four.Native.countBelow 16
    fun i => Nat.beq (pg 5 (mask 5) (pidn 16 5) i) i) 4) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34V1

end
