module

public import Certificates.Kernel.KDenseP.NortonSLP.Base
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11EChk0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11EChk1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11EChk2
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Parse
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125503
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125504
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125505
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125506
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125507
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125508
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125509
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125510
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125511
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125512
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125513

public section

namespace CertificateChecks.KernelKDenseP.NortonSLP.Gen11

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.NortonSLP
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.Gen11

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.SLP.Gen11M.MT = true := by
  kd_monoTabL CFSG.KD.SLP.Gen11ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.SLP.Gen11M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem steps_eq : gen11Steps = CFSG.KD.SLP.Gen11.S := by
  unfold gen11Steps gen11Text
  exact steps_eq_of_parse CFSG.KD.SLP.Gen11.parse_ok

theorem c125503 : prodCheck gen11Gens gen11Steps 0 22 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125503.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125503 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125503.E)

theorem c125504 : prodCheck gen11Gens gen11Steps 22 33 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125504.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125504 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125504.E)

theorem c125505 : prodCheck gen11Gens gen11Steps 33 79 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125505.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125505 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125505.E)

theorem c125506 : prodCheck gen11Gens gen11Steps 79 157 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125506.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125506 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125506.E)

theorem c125507 : prodCheck gen11Gens gen11Steps 157 242 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125507.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125507 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125507.E)

theorem c125508 : prodCheck gen11Gens gen11Steps 242 292 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125508.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125508 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125508.E)

theorem c125509 : prodCheck gen11Gens gen11Steps 292 300 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125509.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125509 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125509.E)

theorem c125510 : prodCheck gen11Gens gen11Steps 300 312 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125510.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125510 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125510.E)

theorem c125511 : prodCheck gen11Gens gen11Steps 312 332 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125511.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125511 CFSG.KD.SLP.Gen11 15 CFSG.KD.SLP.c125511.E)

theorem c125512 : prodCheck gen11Gens gen11Steps 332 342 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125512.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125512 CFSG.KD.SLP.Gen11 18 CFSG.KD.SLP.c125512.E)

theorem c125513 : prodTargetsCheck gen11Gens gen11Steps 342 gen11Targets = true := by
  rw [steps_eq]
  exact prodTargetsCheck_of CFSG.KD.SLP.c125513.tgt
    (kd_slpK% data_ok CFSG.KD.SLP.c125513 CFSG.KD.SLP.Gen11 CFSG.KD.SLP.c125513.E)

end CertificateChecks.KernelKDenseP.NortonSLP.Gen11

end
