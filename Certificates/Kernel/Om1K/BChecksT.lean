module

public import Certificates.Kernel.Om1K.BDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.B

open CFSG.KC.Enum

theorem kKR : allN 8 krOK = true := by quickRfl

theorem kKS : allN 8 (ksOK BD.KS) = true := by quickRfl

theorem kLh : allN 57 (lhOK A.TG.G BD.LhG BD.LhI BD.LhW 7) = true := by quickRfl

theorem kLc : allN 31 (lhOK A.CC.G BD.LcG BD.LcI BD.LcW 5) = true := by quickRfl

theorem kDT : allN 204 (dtOK BD.DG BD.DF) = true := by quickRfl

theorem kW1 : allN 27 (witOK E1.T 27 BD.W1) = true := by quickRfl

theorem kC0 : Nat.ble (cntN 4096 (noWit BD.W0)) 64 = true := by quickRfl

theorem kC1 : Nat.ble (cntN 27 (noWit BD.W1)) 3 = true := by quickRfl

theorem kSq0 : allN 4096 (sqOK E0.T BD.SQ0 BD.RT0 T0 240) = true := by quickRfl

theorem kRt0 : allN 240 (rootOK E0.T BD.RT0 4096) = true := by quickRfl

theorem kSqa : allN 2048 (sqOK Ea.T BD.SQa BD.RTa TA 96) = true := by quickRfl

theorem kSba : allN 2048 (sqOK Ea.T BD.SBa BD.RTa TB 0) = true := by quickRfl

theorem kRta : allN 96 (rootOK Ea.T BD.RTa 2048) = true := by quickRfl

theorem kSqc : allN 1024 (sqOK Ec.T BD.SQc BD.RTc TC 48) = true := by quickRfl

theorem kRtc : allN 48 (rootOK Ec.T BD.RTc 1024) = true := by quickRfl

end CertificateChecks.KernelOm1.B

end
