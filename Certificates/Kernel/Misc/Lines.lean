module

public import Certificates.Kernel.Misc.LinesData
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Kernel.Misc.Unitary
public import Certificates.Data.Kernel.Misc.Lines
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.Lines

open CFSG.KC.Misc.Lines CFSG.KD.Misc.T46

theorem pos : posK CFSG.KD.Misc.Unitary.UL UP PP = true := by quickRfl
theorem pl : plK PB PL = true := by quickRfl
theorem twins : twinsK UP PP PB PL = true := by quickRfl
theorem perpAll : ∀ k < 21, perpK UP PB (33 * k) 33 = true := by kc_cover 1
theorem linesAll : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true := by kc_cover 1
theorem cnt : Nat.beq (lineCnt UP PP PL 0 693) 6237 = true := by quickRfl
theorem ppAll : ∀ k < 21, ppK UP PP PB PL (33 * k) 33 = true := by kc_cover 1

end CFSG.KD.Misc.Lines

end
