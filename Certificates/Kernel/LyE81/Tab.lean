module

public import Certificates.Kernel.LyE81.Data
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyE81Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyE81

open CFSG.KD.LyE81 CFSG.RankThree.PartTwo.Sec4.Item434SporLy

theorem tab : tabG 7 2187 (mulIdxK E PA LA 2187) (edK E) lyE81.idZ lyE81.sets = true := by
  quickRfl

end CertificateChecks.KernelLyE81

end
