module

public import Certificates.Kernel.Om2K.BDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum

theorem kKG : allN 8 kgOK = true := by quickRfl

theorem kZT : allN 4 zOK = true := by quickRfl

theorem kLh : allN 73 (lhOK TG.G BD.LhG BD.LhI BD.LhW 8) = true := by quickRfl

theorem kLc : allN 31 (lhOK CC.G BD.LcG BD.LcI BD.LcW 5) = true := by quickRfl

theorem kNodes : allN 409 (nodeOK BD.NG BD.NP BD.NF) = true := by quickRfl

theorem kW1 : allN 27 (witOK E1.T 27 BD.W1) = true := by quickRfl

theorem kC01 : Nat.ble (cntN 4096 (noWit BD.W0 0)) 8 = true := by quickRfl

theorem kC04 : Nat.ble (cntN 4096 (noWit BD.W0 10)) 1184 = true := by quickRfl

theorem kC11 : Nat.ble (cntN 27 (noWit BD.W1 0)) 1 = true := by quickRfl

theorem kC14 : Nat.ble (cntN 27 (noWit BD.W1 10)) 19 = true := by quickRfl

theorem kSq0 : allN 4096 (sqOK E0.T BD.SQ0 BD.RT0 (EL.G 0) 240) = true := by quickRfl

theorem kRt0 : allN 240 (rootOK E0.T BD.RT0 4096) = true := by quickRfl

theorem kSq2 : allN 1024 (sqOK E2.T BD.SQ2 BD.RT2 (EL.G 3) 48) = true := by quickRfl

theorem kRt2 : allN 48 (rootOK E2.T BD.RT2 1024) = true := by quickRfl

theorem kOrb : allN 24 oNodeOK = true := by quickRfl

theorem kOD : allN 24 oDistOK = true := by quickRfl

theorem kSG : allN 8 sgOK = true := by quickRfl

theorem kCR : allN 4608 (crOK BD.CR E4.T) = true := by quickRfl

theorem kCen : Nat.ble (cntN 4608 (fun i => Nat.beq fld(BD.CR i, 0, 1) 1)) 8 = true := by quickRfl

end CertificateChecks.KernelOm2

end
