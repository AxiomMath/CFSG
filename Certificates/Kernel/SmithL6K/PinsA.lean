module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Kernel.SmithL6K.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem pin_tv : pinTv tvc = true := by decide +kernel

theorem pin_tcP : pinF (fldW 12 tcP) 0 tvc = true := by decide +kernel

theorem pin_idx : pinIdx tcP idxP = true := by decide +kernel

theorem pin_mask : pinMapR maskC wData.toList wmk 0 1395 = true := by decide +kernel

theorem pin_ann : pinMapR annC wData.toList anm 0 1395 = true := by decide +kernel

theorem pin_rev : pinMapR rev20 wtd rwt 0 1395 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
