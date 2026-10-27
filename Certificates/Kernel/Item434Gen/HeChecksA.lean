module

public import Certificates.Kernel.Item434Gen.HeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem kA : permOK 8330 14 (mask 14) (8330 * 14) (HV 0) (HV 1) = true := by quickRfl

theorem kB : permOK 8330 14 (mask 14) (8330 * 14) (HV 2) (HV 3) = true := by quickRfl

theorem kX : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 heXW (HV 4) = true := by quickRfl

theorem kY : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 heYW (HV 6) = true := by quickRfl

theorem kXI : (permOK 8330 14 (mask 14) (8330 * 14) (HV 4) (HV 5) &&
    permOK 8330 14 (mask 14) (8330 * 14) (HV 5) (HV 4)) = true := by quickRfl

theorem kYI : (permOK 8330 14 (mask 14) (8330 * 14) (HV 6) (HV 7) &&
    permOK 8330 14 (mask 14) (8330 * 14) (HV 7) (HV 6)) = true := by quickRfl

theorem kZ : (Nat.beq (cmK 8330 14 (HV 4) (HV 5) (HV 6) (HV 7)) (HV 8) &&
    heisK 8330 14 (HV 4) (HV 6) (HV 8)) = true := by quickRfl

theorem kW : (Nat.beq (pcK 8330 14 (HV 4) (HV 6)) (HV 9) &&
    Nat.beq (pcK 8330 14 (HV 4) (pwK 8330 14 (HV 6) 2)) (HV 10)) = true := by quickRfl

end CertificateChecks.KernelItem434.He

end
