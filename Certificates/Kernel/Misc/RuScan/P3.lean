module

public import Certificates.Data.Kernel.Misc.RuScanB
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.SporSch.Ru.Text4060
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan CertificateChecks.KernelSporSch

theorem ch7230p3_4 : p3K (HP 5) (RuT4060.L 0) (fun l => RuT4060.L (Nat.add 39 l)) 3 = true := by
  quickRfl

theorem ch7230p3_5 : p3K (HP 6) (RuT4060.L 0) (fun l => RuT4060.L (Nat.add 39 l)) 3 = true := by
  quickRfl

end CertificateChecks.KernelMisc.RuScan

end
