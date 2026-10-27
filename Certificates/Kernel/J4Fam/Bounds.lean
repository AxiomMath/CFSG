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

@[expose] noncomputable def bd0F (c : Nat) : Bool := boundsChunk FBT FLLT LVT0 LV0.length c
@[expose] noncomputable def bd1F (c : Nat) : Bool := boundsChunk FBT FLLT LVT1 LV1.length c
@[expose] noncomputable def bd2F (c : Nat) : Bool := boundsChunk FBT FLLT LVT2 LV2.length c
@[expose] noncomputable def bd3F (c : Nat) : Bool := boundsChunk FBT FLLT LVT3 LV3.length c
@[expose] noncomputable def bd4F (c : Nat) : Bool := boundsChunk FBT FLLT LVT4 LV4.length c
@[expose] noncomputable def bd5F (c : Nat) : Bool := boundsChunk FBT FLLT LVT5 LV5.length c
@[expose] noncomputable def bd6F (c : Nat) : Bool := boundsChunk FBT FLLT LVT6 LV6.length c

#kc_each bd0F 0 1
#kc_each bd1F 0 1
#kc_each bd5F 0 1
#kc_each bd6F 0 1
#kc_each bd2F 0 5
#kc_each bd3F 0 8
#kc_each bd4F 0 3

#kc_forall_chunks bd_ok0 (fun c => bd0F c = true) 1 CertificateChecks.KernelJ4Fam.bd0F 1
#kc_forall_chunks bd_ok1 (fun c => bd1F c = true) 1 CertificateChecks.KernelJ4Fam.bd1F 1
#kc_forall_chunks bd_ok2 (fun c => bd2F c = true) 5 CertificateChecks.KernelJ4Fam.bd2F 1
#kc_forall_chunks bd_ok3 (fun c => bd3F c = true) 8 CertificateChecks.KernelJ4Fam.bd3F 1
#kc_forall_chunks bd_ok4 (fun c => bd4F c = true) 3 CertificateChecks.KernelJ4Fam.bd4F 1
#kc_forall_chunks bd_ok5 (fun c => bd5F c = true) 1 CertificateChecks.KernelJ4Fam.bd5F 1
#kc_forall_chunks bd_ok6 (fun c => bd6F c = true) 1 CertificateChecks.KernelJ4Fam.bd6F 1

theorem neg_bnd : notB (boundsChunk FBT FLLT [[[2 ^ 191]]] 1 0) = true := by quickRfl

end CertificateChecks.KernelJ4Fam
