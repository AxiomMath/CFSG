
module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.L3150M
public import Certificates.Kernel.Sporadic.Fi22.G3147
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22F1M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem permG : permOK 3510 12 (mask 12) (3510 * 12) GO (inv GO) = true := by quickRfl
theorem cnId : cn (pidn 3510 12) = true := by quickRfl
theorem neId : bIf(Nat.beq GO (pidn 3510 12), false, true) = true := by quickRfl
theorem sqId : Nat.beq (c GO GO) (pidn 3510 12) = true := by quickRfl
theorem sGO : bIf(siftP GO, false, true) = true := by quickRfl
theorem cnA : allN 2 (fun k => cn (Fi22CGT.F k)) = true := by quickRfl
theorem sConj : allN 2 (fun k => siftP (c GO (c (Fi22CGT.F k) GO))) = true := by quickRfl
theorem moved : allN 3510 (fun p => bIf(Nat.beq p 0, true,
    bIf(Nat.beq (pg 12 (mask 12) (Fi22M3.MS 0) p) p,
      bIf(Nat.beq (pg 12 (mask 12) (Fi22M3.MS 1) p) p,
        Bool.not (Nat.beq (pg 12 (mask 12) (Fi22M3.MS 2) p) p), true), true))) = true := by
  quickRfl
theorem lenG : Fi22GOT.chars.length = 3 * 3510 := by decide +kernel

end CertificateChecks.KernelSpor.Fi22F1M

end
