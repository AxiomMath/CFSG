module

public import Certificates.Kernel.Misc.ON.Regs0
public import Certificates.Kernel.Misc.ON.Regs1
public import Certificates.Kernel.Misc.ON.Regs2
public import Certificates.Kernel.Misc.ON.Regs3
public import Certificates.Kernel.Misc.ON.Regs4
public import Certificates.Kernel.Misc.ON.Regs5
public import Certificates.Kernel.Misc.ON.Regs6
public import Certificates.Kernel.Misc.ON.Regs7

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem regsB : ∀ r, 8 ≤ r → r < 200 → chkRegM r = true := by
  intro r hlo hhi
  by_cases c0 : r < 32
  · exact regs0 r (by omega) c0
  by_cases c1 : r < 56
  · exact regs1 r (by omega) c1
  by_cases c2 : r < 80
  · exact regs2 r (by omega) c2
  by_cases c3 : r < 104
  · exact regs3 r (by omega) c3
  by_cases c4 : r < 128
  · exact regs4 r (by omega) c4
  by_cases c5 : r < 152
  · exact regs5 r (by omega) c5
  by_cases c6 : r < 176
  · exact regs6 r (by omega) c6
  exact regs7 r (by omega) hhi

end CertificateChecks.KernelMisc.ON

end
