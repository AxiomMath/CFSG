module

public import Certificates.Data.Kernel.L34Cov.Sigma
public import Certificates.Kernel.L34W.Outer
public import Certificates.Kernel.L34Cov.Words
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34Cov.SigmaData
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelL34Cov.SgAB include_bytes "data/SigmaChecks.SgAB.items" 144 11132991846459586331
#kc_items CertificateChecks.KernelL34Cov.OB include_bytes "data/SigmaChecks.OB.items" 840 11287164144141015270
#kc_items CertificateChecks.KernelL34Cov.SO include_bytes "data/SigmaChecks.SO.items" 13567 8943938041465382825
#kc_items CertificateChecks.KernelL34Cov.SI include_bytes "data/SigmaChecks.SI.items" 13567 7658642376119027992

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.KC.L34Cov CertificateChecks.KernelL34W

theorem ch22219ab_k : sgAbOK GT SgAB UAC.codes UBC.codes = true := by decide +kernel

theorem ch22219cj_k : sgCjOK GT YT AlX.F = true := by decide +kernel

theorem ch22219fix_k : sgFixOK GT = true := by decide +kernel

theorem ch22219orb_k : sgOrbOK GT OB = true := by decide +kernel

theorem ch22219stab_k : sgStabOK YT = true := by decide +kernel

theorem ch22219sort_k : sgSortOK YT SO SI = true := by decide +kernel

theorem ch22219ab_neg : (!sgAbOK GT (patchT SgAB 1 (SgAB 2)) UAC.codes UBC.codes) = true := by
  decide +kernel

theorem ch22219ab_neg2 : (!sgAbOK GT SgAB (UBC.codes.take 2 ++ UAC.codes.drop 2)
    (UAC.codes.take 2 ++ UBC.codes.drop 2)) = true := by
  decide +kernel

theorem ch22219cj_neg : (!sgCjOK GT YT (patchT AlX.F 1
    (Nat.add (AlX.F 1) (Nat.shiftLeft 48 12)))) = true := by
  decide +kernel

theorem ch22219fix_neg :
    (!sgFixOK fun k => GT (nIf(Nat.beq k 0, 1, nIf(Nat.beq k 1, 0, k)))) = true := by
  decide +kernel

theorem ch22219orb_neg : (!sgOrbOK GT (patchT OB 104 (OB 0))) = true := by decide +kernel

theorem ch22219stab_neg : (!sgStabOK (patchT YT 2303 (GT 0))) = true := by decide +kernel

theorem ch22219sort_neg : (!sgSortOK YT (patchT (patchT SO 0 (SO 1)) 1 (SO 0)) SI) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
