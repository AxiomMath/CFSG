module

public import Certificates.Data.Kernel.Misc.RuScanB
public import Certificates.Kernel.Misc.RuScan.DataL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Enum

theorem ch7230v0 : allN 60 (fun q => Nat.ble (V0 (Nat.succ q)) 24576) = true := by quickRfl
theorem ch7230v1 : allN 60 (fun q => Nat.ble (V1 (Nat.succ q)) 8704) = true := by quickRfl
theorem ch7230v2 : allN 60 (fun q => Nat.ble (V2 (Nat.succ q)) 512) = true := by quickRfl
theorem ch7230v3 : allN 60 (fun q => Nat.ble (V3 (Nat.succ q)) 3072) = true := by quickRfl
theorem ch7230v8 : allN 28 (fun q => Nat.ble (V8 (Nat.succ q)) 768) = true := by quickRfl

end CertificateChecks.KernelMisc.RuScan

end
