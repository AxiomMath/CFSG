module

public import CFSG.RankThree.Native.ONTripleLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Misc.ON.Wit0
public import Certificates.Kernel.Misc.ON.Wit1
public import Certificates.Kernel.Misc.ON.Wit2
public import Certificates.Kernel.Misc.ON.Wit3

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem chkP0MB : chkP0M = true := by quickRfl

theorem chkConjMB : chkConjM = true := by quickRfl

theorem chkK0MB : chkK0M = true := by quickRfl

theorem chkBlocksMB : chkBlocksM = true := by quickRfl

theorem chkVMB : chkVM = true := by quickRfl

theorem witsB : ∀ q < 12, chkWitM (9 * q) 9 = true := by
  intro q hq
  by_cases c0 : q < 3
  · exact wits0 q c0
  by_cases c1 : q < 6
  · exact wits1 q (by omega) c1
  by_cases c2 : q < 9
  · exact wits2 q (by omega) c2
  exact wits3 q (by omega) hq

theorem ptsB : ∀ q < 3, chkPtsM (20 * q) 20 = true := by
  intro q hq
  interval_cases q <;> quickRfl

end CertificateChecks.KernelMisc.ON

end
