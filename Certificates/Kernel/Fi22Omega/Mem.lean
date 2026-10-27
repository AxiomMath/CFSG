module

public import Certificates.Kernel.Fi22Omega.Glue
public import Certificates.Kernel.Fi22Omega.Sift
public import Certificates.Kernel.Sporadic.Fi22.C2066

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open CFSG.KC.Fi22Omega CFSG.KC.Enum CFSG.KS CertificateChecks.KernelI242 CertificateChecks.KernelSpor
  CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Certificates CFSG.Certificates.Native

theorem y_mem_P
    {r : Nat} (hr : r < 8) : i242y r ∈ fi22P := by
  obtain ⟨hc, hs⟩ := band_true (allN_spec ySift r hr)
  have hIn := Fi22C2066.fi22InP_of (PS := Y.S) (yArr_eq hr) hc hs
  exact (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1
    (i242_rep_y hr)).1 hIn

theorem i242Y_le_P :
    i242Y ≤ fi22P := by
  rw [i242Y_eq, Subgroup.closure_le]
  rintro _ ⟨r, hr, rfl⟩
  exact y_mem_P hr

end CertificateChecks.KernelFi22Omega

end
