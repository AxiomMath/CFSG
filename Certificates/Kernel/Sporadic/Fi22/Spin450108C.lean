module

public import Certificates.Kernel.Sporadic.Fi22.Spin450108
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CertificateChecks.KernelSpor.Spin450108

@[expose] noncomputable def chunkF (s : Nat) : Bool := chunk s

#kc_each_unfold chunkF 0 32 as CertificateChecks.KernelSpor.Spin450108.c

#kc_forall_chunks chunksK (fun s => chunk s = true) 32 CertificateChecks.KernelSpor.Spin450108.c 1

theorem chunks : ∀ s < 32, chunk s = true := chunksK

end CertificateChecks.KernelSpor.Spin450108

end
