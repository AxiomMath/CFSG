module

public import Certificates.Data.Kernel.PlusRealizeK
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.RealizeCheck
import all CFSG.OddTranspositions.PartThree.Eleven.Plus.RealizeCheck

public section

namespace CertificateChecks.KernelPlusR

open CFSG.KC.PlusRealizeK CFSG.OddTranspositions.PartThree
open CFSG.OddTranspositions.PartThree.PlusRealize

theorem ch1383005_zT : plusSquareVecs.size = 60 := by decide +kernel
theorem ch1383005_zF : plusNonsquareVecs.size = 60 := by decide +kernel
theorem ch1383005_zR : plusTable.size = 60 := by decide +kernel
theorem ch1383005_rows : allL (fun r : List Nat => Nat.beq r.length 60) (VSof plusTable) = true := by
  decide +kernel

theorem ch1383005_sT : signOK true (VSof plusSquareVecs) = true := by decide +kernel
theorem ch1383005_sF : signOK false (VSof plusNonsquareVecs) = true := by decide +kernel
theorem ch1383005_tT : tabOK (VSof plusSquareVecs) (VSof plusTable) = true := by decide +kernel
theorem ch1383005_tF : tabOK (VSof plusNonsquareVecs) (VSof plusTable) = true := by decide +kernel
theorem ch1383005_dT : distOK (VSof plusSquareVecs) = true := by decide +kernel
theorem ch1383005_dF : distOK (VSof plusNonsquareVecs) = true := by decide +kernel
theorem ch1383005_cT : covOK true (VSof plusSquareVecs) = true := by decide +kernel
theorem ch1383005_cF : covOK false (VSof plusNonsquareVecs) = true := by decide +kernel

end CertificateChecks.KernelPlusR
