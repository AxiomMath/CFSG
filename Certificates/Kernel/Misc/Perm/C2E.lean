module

public import Certificates.Kernel.Misc.Perm.C2K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.NativeSchreierCard

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.RankThree.Native.F2

theorem ptsQ_0 : ptsK 2 125 GQ PQ HQE.F HQR.F HQL.F 0 125 = true := by quickRfl

theorem keysQ_0 : keysK 0 125 PQ 0 125 = true := by quickRfl

theorem rootQ : Nat.beq (PQ 0) I22 = true := by quickRfl

@[expose] noncomputable def ptsC0C (j : ℕ) : Bool :=
  ptsK 2 3000 GC0 PC0 HC0E.F HC0R.F HC0L.F (Nat.mul 500 j) 500

@[expose] noncomputable def keysC0C (j : ℕ) : Bool := keysK 1 3000 PC0 (Nat.mul 500 j) 500

theorem rootC0 : Nat.beq (PC0 0) I22 = true := by quickRfl

@[expose] noncomputable def ptsC1C (j : ℕ) : Bool :=
  ptsK 3 600 GC1 PC1 HC1E.F HC1R.F HC1L.F (Nat.mul 100 j) 100

@[expose] noncomputable def keysC1C (j : ℕ) : Bool := keysK 2 600 PC1 (Nat.mul 100 j) 100

theorem rootC1 : Nat.beq (PC1 0) I22 = true := by quickRfl

theorem ptsD_0 : ptsK 2 60 GD PD HDE.F HDR.F HDL.F 0 60 = true := by quickRfl

theorem keysD_0 : keysK 3 60 PD 0 60 = true := by quickRfl

theorem rootD : Nat.beq (PD 0) I22 = true := by quickRfl

theorem dinv_ok : dinvK = true := by quickRfl

theorem words_ok : wordsK = true := by quickRfl

end CertificateChecks.KernelMisc.Co2K

#kc_each CertificateChecks.KernelMisc.Co2K.ptsC0C 0 6

#kc_each CertificateChecks.KernelMisc.Co2K.keysC0C 0 6

#kc_each CertificateChecks.KernelMisc.Co2K.ptsC1C 0 6

#kc_each CertificateChecks.KernelMisc.Co2K.keysC1C 0 6

namespace CertificateChecks.KernelMisc.Co2K

#kc_forall_chunks ptsC0_chunks (fun j => ptsC0C j = true) 6 CertificateChecks.KernelMisc.Co2K.ptsC0C 1

#kc_forall_chunks keysC0_chunks (fun j => keysC0C j = true) 6
  CertificateChecks.KernelMisc.Co2K.keysC0C 1

#kc_forall_chunks ptsC1_chunks (fun j => ptsC1C j = true) 6 CertificateChecks.KernelMisc.Co2K.ptsC1C 1

#kc_forall_chunks keysC1_chunks (fun j => keysC1C j = true) 6
  CertificateChecks.KernelMisc.Co2K.keysC1C 1

end CertificateChecks.KernelMisc.Co2K

end
