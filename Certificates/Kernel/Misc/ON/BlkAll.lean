module

public import Certificates.Kernel.Misc.ON.Blk0
public import Certificates.Kernel.Misc.ON.Blk1
public import Certificates.Kernel.Misc.ON.Blk2
public import Certificates.Kernel.Misc.ON.Blk3
public import Certificates.Kernel.Misc.ON.Blk4
public import Certificates.Kernel.Misc.ON.Blk5
public import Certificates.Kernel.Misc.ON.Blk6
public import Certificates.Kernel.Misc.ON.Blk7
public import Certificates.Kernel.Misc.ON.Blk8
public import Certificates.Kernel.Misc.ON.Blk9

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem blkB : ∀ q < 120, ptsOK (1023 * q) 1023 = true := by
  intro q hq
  by_cases c0 : q < 12
  · exact blk0 q c0
  by_cases c1 : q < 24
  · exact blk1 q (by omega) c1
  by_cases c2 : q < 36
  · exact blk2 q (by omega) c2
  by_cases c3 : q < 48
  · exact blk3 q (by omega) c3
  by_cases c4 : q < 60
  · exact blk4 q (by omega) c4
  by_cases c5 : q < 72
  · exact blk5 q (by omega) c5
  by_cases c6 : q < 84
  · exact blk6 q (by omega) c6
  by_cases c7 : q < 96
  · exact blk7 q (by omega) c7
  by_cases c8 : q < 108
  · exact blk8 q (by omega) c8
  exact blk9 q (by omega) hq

end CertificateChecks.KernelMisc.ON

end
