module

public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoAll
public import CFSG.Certificates.Kernel.KDense.Data.Checks
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk0
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk1
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk2
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk3
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk4
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk5
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk6
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoCChk7

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.AXM.MT = true := by
  kd_monoTabL CFSG.KD.AXME t

theorem data_okP : dataOKP CFSG.KD.KDF.F CFSG.KD.AXM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

end CertificateChecks.KernelKDenseP.Axis

end
