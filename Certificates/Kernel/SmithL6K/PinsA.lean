module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.RangeGlue
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem pin_tv : pinTv tvc = true := by decide +kernel

theorem pin_tcP : pinF (fldW 12 tcP) 0 tvc = true := by decide +kernel

theorem pin_idx : pinIdx tcP idxP = true := by decide +kernel

theorem pin_mask : pinMapR maskC wData.toList wmk 0 1395 = true := by decide +kernel

theorem pin_ann_q : ∀ q < 9, pinMapR annC wData.toList anm (0 + q * 155) 155 = true := by
  kc_cover 1

theorem pin_ann : pinMapR annC wData.toList anm 0 1395 = true :=
  pinMapR_of_chunks annC wData.toList anm 0 9 155 1395 rfl pin_ann_q

theorem pin_rev : pinMapR rev20 wtd rwt 0 1395 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
