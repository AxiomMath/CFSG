module

public import Certificates.Kernel.J4Fam.Data
public import Certificates.Data.Kernel.J4Fam
public import CFSG.Certificates.Kernel.Common.Lce
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Fam

open CFSG.KC.J4Fam
open CFSG.KC (notB)

@[expose] noncomputable def cl0F (c : Nat) : Bool :=
  closeChunk CML PTP LVT1 LV1.length LVT0 TGT0 LV0.length c
@[expose] noncomputable def cl1F (c : Nat) : Bool :=
  closeChunk CML PTP LVT2 LV2.length LVT1 TGT1 LV1.length c
@[expose] noncomputable def cl2F (c : Nat) : Bool :=
  closeChunk CML PTP LVT3 LV3.length LVT2 TGT2 LV2.length c
@[expose] noncomputable def cl3F (c : Nat) : Bool :=
  closeChunk CML PTP LVT4 LV4.length LVT3 TGT3 LV3.length c
@[expose] noncomputable def cl4F (c : Nat) : Bool :=
  closeChunk CML PTP LVT5 LV5.length LVT4 TGT4 LV4.length c
@[expose] noncomputable def cl5F (c : Nat) : Bool :=
  closeChunk CML PTP LVT6 LV6.length LVT5 TGT5 LV5.length c
@[expose] noncomputable def cl6F (c : Nat) : Bool :=
  closeChunk CML PTP LVT7 LV7.length LVT6 TGT6 LV6.length c

#kc_each cl0F 0 1
#kc_each cl1F 0 2
#kc_each cl5F 0 2
#kc_each cl6F 0 1
#kc_each cl2F 0 17
#kc_each cl3F 0 29
#kc_each cl4F 0 12

#kc_forall_chunks cl_ok0 (fun c => cl0F c = true) 1 CertificateChecks.KernelJ4Fam.cl0F 1
#kc_forall_chunks cl_ok1 (fun c => cl1F c = true) 2 CertificateChecks.KernelJ4Fam.cl1F 1
#kc_forall_chunks cl_ok2 (fun c => cl2F c = true) 17 CertificateChecks.KernelJ4Fam.cl2F 1
#kc_forall_chunks cl_ok3 (fun c => cl3F c = true) 29 CertificateChecks.KernelJ4Fam.cl3F 1
#kc_forall_chunks cl_ok4 (fun c => cl4F c = true) 12 CertificateChecks.KernelJ4Fam.cl4F 1
#kc_forall_chunks cl_ok5 (fun c => cl5F c = true) 2 CertificateChecks.KernelJ4Fam.cl5F 1
#kc_forall_chunks cl_ok6 (fun c => cl6F c = true) 1 CertificateChecks.KernelJ4Fam.cl6F 1

theorem neg_close : notB (closeChunk CML PTP LVT1 LV1.length LVT0 [[[[]]]] LV0.length 0) = true := by
  quickRfl

end CertificateChecks.KernelJ4Fam
