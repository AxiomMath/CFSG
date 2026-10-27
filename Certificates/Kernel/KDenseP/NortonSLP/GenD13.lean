module

public import Certificates.Kernel.KDenseP.NortonSLP.Base
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13EChk0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13EChk1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13EChk2
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13EChk3
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Parse
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125530
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125531
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125532
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125533
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125534
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125535
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125536
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125537
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125538
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125539
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125540
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125541
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125542

public section

namespace CertificateChecks.KernelKDenseP.NortonSLP.GenD13

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.NortonSLP
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.GenD13

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.SLP.GenD13M.MT = true := by
  kd_monoTabL CFSG.KD.SLP.GenD13ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.SLP.GenD13M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem steps_eq : genD13Steps = CFSG.KD.SLP.GenD13.S := by
  unfold genD13Steps genD13Text
  exact steps_eq_of_parse CFSG.KD.SLP.GenD13.parse_ok

theorem c125530 : prodCheck genD13Gens genD13Steps 0 22 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125530.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125530 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125530.E)

theorem c125531 : prodCheck genD13Gens genD13Steps 22 34 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125531.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125531 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125531.E)

theorem c125532 : prodCheck genD13Gens genD13Steps 34 70 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125532.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125532 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125532.E)

theorem c125533 : prodCheck genD13Gens genD13Steps 70 144 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125533.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125533 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125533.E)

theorem c125534 : prodCheck genD13Gens genD13Steps 144 231 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125534.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125534 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125534.E)

theorem c125535 : prodCheck genD13Gens genD13Steps 231 296 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125535.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125535 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125535.E)

theorem c125536 : prodCheck genD13Gens genD13Steps 296 336 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125536.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125536 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125536.E)

theorem c125537 : prodCheck genD13Gens genD13Steps 336 343 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125537.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125537 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125537.E)

theorem c125538 : prodCheck genD13Gens genD13Steps 343 354 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125538.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125538 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125538.E)

theorem c125539 : prodCheck genD13Gens genD13Steps 354 377 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125539.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125539 CFSG.KD.SLP.GenD13 15 CFSG.KD.SLP.c125539.E)

theorem c125540 : prodCheck genD13Gens genD13Steps 377 396 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125540.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125540 CFSG.KD.SLP.GenD13 15 CFSG.KD.SLP.c125540.E)

theorem c125541 : prodCheck genD13Gens genD13Steps 396 397 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125541.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125541 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125541.E)

theorem c125542 : prodTargetsCheck genD13Gens genD13Steps 397 genD13Targets = true := by
  rw [steps_eq]
  exact prodTargetsCheck_of CFSG.KD.SLP.c125542.tgt
    (kd_slpK% data_ok CFSG.KD.SLP.c125542 CFSG.KD.SLP.GenD13 CFSG.KD.SLP.c125542.E)

end CertificateChecks.KernelKDenseP.NortonSLP.GenD13

end
