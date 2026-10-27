module

public import Certificates.Kernel.LocalComp.Weyl3220
public import Certificates.Kernel.LocalComp.Weyl3189
public import CFSG.Certificates.Kernel.LocalCompCoordSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoordData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3187

open CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight.Weyl CertificateChecks.KernelLC

theorem kF : factsF E8.FT W3184.W.LR W3184.W.TRI W3184.W.BP = true := by quickRfl
theorem kS : factsS E8.ST W3184.W.LR W3184.W.TRI W3184.W.BP = true := by quickRfl
theorem kHF : homF E8.FT = true := by quickRfl
theorem kDF : distK E8.FT (fun _ => true) = true := by quickRfl
theorem kDS : distK E8.ST evenB = true := by quickRfl
theorem kL : linksOK E8.RT E8.ST E8.FT E8.PT E8.NEG W3220.KP = true := by quickRfl
theorem kPT : swapRowOK E8.RK 0 1 (E8.PT 0) = true := by quickRfl

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3187 : (coordCheck = true) := by
  rw [coordCheck_eq]
  exact coord_sound E8.bind E8.sorted E8.hrt E8.neg E8.hst E8.froots E8.ft0 E8.hft kPT W3220.kKP
    W3184.binds W3184.perm W3184.W.hl kF kS kHF kDF kDS kL

end CertificateChecks.KernelLC.W3187

end
