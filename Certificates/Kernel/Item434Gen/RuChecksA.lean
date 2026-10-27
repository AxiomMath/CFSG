module

public import Certificates.Kernel.Item434Gen.RuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem kA : permOK 4060 12 (mask 12) (4060 * 12) (RV 0) (RV 1) = true := by quickRfl

theorem kB : permOK 4060 12 (mask 12) (4060 * 12) (RV 2) (RV 3) = true := by quickRfl

theorem kX : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 ruXW (RV 4) = true := by quickRfl

theorem kY : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 ruYW (RV 6) = true := by quickRfl

theorem kXI : (permOK 4060 12 (mask 12) (4060 * 12) (RV 4) (RV 5) &&
    permOK 4060 12 (mask 12) (4060 * 12) (RV 5) (RV 4)) = true := by quickRfl

theorem kYI : (permOK 4060 12 (mask 12) (4060 * 12) (RV 6) (RV 7) &&
    permOK 4060 12 (mask 12) (4060 * 12) (RV 7) (RV 6)) = true := by quickRfl

theorem kZ : (Nat.beq (cmK 4060 12 (RV 4) (RV 5) (RV 6) (RV 7)) (RV 8) &&
    heisK 4060 12 (RV 4) (RV 6) (RV 8)) = true := by quickRfl

theorem kW : (Nat.beq (pcK 4060 12 (RV 4) (RV 6)) (RV 9) &&
    Nat.beq (pcK 4060 12 (RV 4) (pwK 4060 12 (RV 6) 2)) (RV 10)) = true := by quickRfl

end CertificateChecks.KernelItem434.Ru

end
