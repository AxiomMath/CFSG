module

public import Certificates.Kernel.Seitz.B45F
public import Certificates.Kernel.Seitz.B45St
public import Certificates.Kernel.Seitz.B45S0
public import Certificates.Kernel.Seitz.B45S1
public import Certificates.Kernel.Seitz.B45S2
public import Certificates.Kernel.Seitz.B45S3
public import Certificates.Kernel.Seitz.B45S4
public import Certificates.Kernel.Seitz.B45S5
public import Certificates.Kernel.Seitz.B45S6
public import Certificates.Kernel.Seitz.B45S7
public import Certificates.Kernel.Seitz.B45S8
public import Certificates.Kernel.Seitz.B45S9
public import Certificates.Kernel.Seitz.B45S10
public import Certificates.Kernel.Seitz.B45S11
public import Certificates.Kernel.Seitz.B45S12
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import Mathlib

public section

namespace CertificateChecks.KernelSeitz

open CFSG.KC.SeitzB45 Certificates.Seitz77CaseB45

#kc_forall_chunks slice_all (fun c => sliceK c = true) 91 CertificateChecks.KernelSeitz.sliceK 1
#kc_forall_chunks stats_all (fun i => statsK i = true) 15 CertificateChecks.KernelSeitz.statsK 1
#kc_forall_chunks adm_all (fun c => admK c = true) 16 CertificateChecks.KernelSeitz.admK 1

theorem sl_len : P6.SL.length = 91 := by decide +kernel

theorem ms_len : P6.MS.length = 15 := by decide +kernel

theorem fb6_true : fb6Check mtF labF laddF = true := by
  rw [mtF_fun, labF_fun, laddF_fun]
  exact fb6_of ms_len adm_all stats_all k_cover fun c hc => slice_all c (by rwa [sl_len] at hc)

theorem fbSix_true : fbSixCheck = true := by
  unfold fbSixCheck
  rw [tables_true, fb7_true, fb6_true]
  rfl

end CertificateChecks.KernelSeitz

end
