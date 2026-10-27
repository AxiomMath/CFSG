
module

public import Certificates.Kernel.KDense.Basic
public import CFSG.Certificates.Kernel.KDense.Data.Ent0
public import CFSG.Certificates.Kernel.KDense.Data.Ent1
public import CFSG.Certificates.Kernel.KDense.Data.Ent2
public import CFSG.Certificates.Kernel.KDense.Data.Ent3
public import CFSG.Certificates.Kernel.KDense.Data.Ent4
public import CFSG.Certificates.Kernel.KDense.Data.Ent5
public import CFSG.Certificates.Kernel.KDense.Data.Ent6
public import CFSG.Certificates.Kernel.KDense.Data.Ent7
public import CFSG.Certificates.Kernel.KDense.Data.Ent8
public import CFSG.Certificates.Kernel.KDense.Data.Ent9
public import CFSG.Certificates.Kernel.KDense.Data.Ent10
public import CFSG.Certificates.Kernel.KDense.Data.Ent11
public import CFSG.Certificates.Kernel.KDense.Data.Ent12
public import CFSG.Certificates.Kernel.KDense.Data.Ent13
public import CFSG.Certificates.Kernel.KDense.Data.Ent14
public import CFSG.Certificates.Kernel.KDense.Data.Ent15
public import CFSG.Certificates.Kernel.KDense.Data.Ent16
public import CFSG.Certificates.Kernel.KDense.Data.Ent17

public section

namespace CertificateChecks.KernelKDense

open CFSG.KC CFSG.KC.KDense CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Griess.ModFive CFSG.YGroups.Y443Native

set_option maxRecDepth 100000

theorem arrs_length : CFSG.KD.KDT.T.arrs.length = 72 := rfl

theorem tab_ok : tabOK CFSG.KD.KDF.F CFSG.KD.KDT.T = true :=
  tabOK_of_entries _ _ (by rw [arrs_length]; kd_all CFSG.KD.KDTE 72)

theorem data_ok : dataOK CFSG.KD.KDF.F CFSG.KD.KDT.T CFSG.KD.KDF.KT CFSG.KD.KDF.TH CFSG.KD.KDF.OCT
    CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      tab_ok)))))

end CertificateChecks.KernelKDense

end
