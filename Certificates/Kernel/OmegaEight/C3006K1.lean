module

public import Certificates.Kernel.OmegaEight.C3006D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTab CFSG.KC.CycTabW

theorem genArrs_cyc : ((List.finRange 8).all fun j =>
    (genArrs[(j : ℕ)]!).toList == (List.range 360).map (cycsK 360 (genCycles j))) = true := by
  quickRfl

theorem tabX : tabsOKW 360 9 D.TX (fun r x => cycsK 360 (csX.getD r []) x) 8 = true := by
  quickRfl

theorem tabA : tabsOKW 360 9 D.TA (fun i x => wordW 360 9 D.TX (gcX.getD i []) x) 4 = true := by
  quickRfl

theorem tabR : tabsOKW 240 8 D.TR (fun i x => cycsK 240 (csR.getD i []) x) 4 = true := by
  quickRfl

end CertificateChecks.KernelO8.C3006

end
