module

public import Certificates.Kernel.KDenseP.NortonSLP.Base
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7EChk0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7EChk1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7EChk2
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Parse
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125340
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125341
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125342
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125343
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125344
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125345
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125346
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125347
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125348
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125349
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125350
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125351

public section

namespace CertificateChecks.KernelKDenseP.NortonSLP.Gen7

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP CFSG.KC.NortonSLPK
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.NortonSLP
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7.Gen7

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.SLP.Gen7M.MT = true := by
  kd_monoTabL CFSG.KD.SLP.Gen7ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.SLP.Gen7M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem steps_eq : gen7Steps = CFSG.KD.SLP.Gen7.S := by
  unfold gen7Steps gen7Text
  exact steps_eq_of_parse CFSG.KD.SLP.Gen7.parse_ok

theorem c125340 : prodCheck gen7Gens gen7Steps 0 21 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125340.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125340 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125340.E)

theorem c125341 : prodCheck gen7Gens gen7Steps 21 31 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125341.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125341 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125341.E)

theorem c125342 : prodCheck gen7Gens gen7Steps 31 57 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125342.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125342 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125342.E)

theorem c125343 : prodCheck gen7Gens gen7Steps 57 105 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125343.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125343 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125343.E)

theorem c125344 : prodCheck gen7Gens gen7Steps 105 174 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125344.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125344 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125344.E)

theorem c125345 : prodCheck gen7Gens gen7Steps 174 234 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125345.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125345 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125345.E)

theorem c125346 : prodCheck gen7Gens gen7Steps 234 286 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125346.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125346 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125346.E)

theorem c125347 : prodCheck gen7Gens gen7Steps 286 302 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125347.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125347 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125347.E)

theorem c125348 : prodCheck gen7Gens gen7Steps 302 318 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125348.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125348 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125348.E)

theorem c125349 : prodCheck gen7Gens gen7Steps 318 336 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125349.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125349 CFSG.KD.SLP.Gen7 12 CFSG.KD.SLP.c125349.E)

theorem c125350 : prodCheck gen7Gens gen7Steps 336 349 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125350.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125350 CFSG.KD.SLP.Gen7 12 CFSG.KD.SLP.c125350.E)

theorem c125351 : prodTargetsCheck gen7Gens gen7Steps 349 gen7Targets = true := by
  rw [steps_eq]
  exact prodTargetsCheck_of CFSG.KD.SLP.c125351.tgt
    (kd_slpK% data_ok CFSG.KD.SLP.c125351 CFSG.KD.SLP.Gen7 CFSG.KD.SLP.c125351.E)

end CertificateChecks.KernelKDenseP.NortonSLP.Gen7

end
