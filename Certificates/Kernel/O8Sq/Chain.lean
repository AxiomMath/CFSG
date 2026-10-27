module

public import Certificates.Kernel.O8Sq.ChainData
public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Data.O8p2NoDatum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Sq

open CFSG.KC.Enum CFSG.KS CFSG.KC.PCent CertificateChecks.KernelO8 CFSG.ClassicalInvolution.O8Data

theorem ch272020g1 : (Nat.beq G1.length 6 && allN 3 (fun j =>
    Nat.beq (G1.getD j 0) (wO ((centGens.getD 1 []).getD j [])) &&
      Nat.beq (G1.getD (Nat.add j 3) 0) (pinvS 360 9 (mask 9) (G1.getD j 0))) &&
    allN 6 (fun k => Nat.beq (pcomp 360 9 (mask 9) (G1.getD k 0) (mainK 1))
      (pcomp 360 9 (mask 9) (mainK 1) (G1.getD k 0)))) = true := by quickRfl

theorem ch272020g2 : (Nat.beq G2.length 6 && allN 3 (fun j =>
    Nat.beq (G2.getD j 0) (wO ((centGens.getD 2 []).getD j [])) &&
      Nat.beq (G2.getD (Nat.add j 3) 0) (pinvS 360 9 (mask 9) (G2.getD j 0))) &&
    allN 6 (fun k => Nat.beq (pcomp 360 9 (mask 9) (G2.getD k 0) (mainK 2))
      (pcomp 360 9 (mask 9) (mainK 2) (G2.getD k 0)))) = true := by quickRfl

theorem ch272020l1 : (stabLowK 360 9 (fun k => G1.getD k 0) 6 L1 &&
    Nat.beq (L1.map fun lv => lv.2.2.2.length).prod 46080) = true := by quickRfl

theorem ch272020l2 : (stabLowK 360 9 (fun k => G2.getD k 0) 6 L2 &&
    Nat.beq (L2.map fun lv => lv.2.2.2.length).prod 3072) = true := by quickRfl

end CertificateChecks.KernelO8Sq

end
