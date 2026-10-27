module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCTitsInputs
public import Certificates.Kernel.TitsW.Defs

public section

namespace CertificateChecks.KernelTitsW.C5173

open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree CFSG.RankThree.PartTwo.Sec4.Item434RemTits
  CertificateChecks.KernelTitsW

theorem c5173_l1 : CFSG.KS.Raw.lettersK 13 (titsUWord ++ yWord) = true := by decide +kernel

theorem c5173_l2 : CFSG.KS.Raw.lettersK 13 (xWord ++ yWord ++ titsUWord) = true := by
  decide +kernel

theorem c5173_eq : Nat.beq (WD (titsUWord ++ yWord)) (WD (xWord ++ yWord ++ titsUWord)) = true := by
  decide +kernel

end CertificateChecks.KernelTitsW.C5173

end
