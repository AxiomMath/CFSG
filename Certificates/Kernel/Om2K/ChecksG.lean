module

public import Certificates.Kernel.Om2K.Defs
public import Certificates.Kernel.OmegaEight.AutChainAP
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.SetOrb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.EvenSmallLie.OmegaEight.Weyl (pairArr pairRepArr)
open CertificateChecks.KernelO8 (AP.S)

@[expose] noncomputable def pinv3 (p : Nat) : Nat := pinvS 360 9 (mask 9) p

@[expose] noncomputable def cj3 (g y : Nat) : Nat :=
  pcomp 360 9 (mask 9) g (pcomp 360 9 (mask 9) y (pinv3 g))

theorem kG0 : allN 9 (fun j => bAnd(canonK 360 9 (mask 9) (360 * 9) (AP.S j),
    bAnd(permOK 360 9 (mask 9) (360 * 9) (AP.S j) (pinv3 (AP.S j)),
      canonK 360 9 (mask 9) (360 * 9) (pinv3 (AP.S j))))) = true := by quickRfl

theorem kG1 : allN 8 (fun i => allN 120 fun j => Nat.beq (pg 9 511 (cj3 (AP.S 8) (AP.S i)) j)
    (pairArr.getD (pg 8 255 (wAK (yW.getD i [])) (pairRepArr.getD j 0)) 0)) = true := by quickRfl

theorem kG2 : allN 120 (fun j => Nat.blt (pairRepArr.getD j 0) 240) = true := by quickRfl

theorem kG3 : allN 8 (fun i => permOK 240 8 (mask 8) (240 * 8) (wAK (yW.getD i []))
    (pinvS 240 8 (mask 8) (wAK (yW.getD i [])))) = true := by quickRfl

end CertificateChecks.KernelOm2

end
