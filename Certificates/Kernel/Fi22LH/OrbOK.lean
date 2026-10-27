module

public import CFSG.Certificates.Kernel.Fi22LH.Defs
import Certificates.Kernel.Fi22Core.Conj

public section

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KS.Fi22L

theorem orbOK : OrbOK := by
  refine ⟨orbTab_size 0, orbTab_size 1, orbTab_size 2, orbTab_size 3, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := KernelFi22C.tree_facts hk
  exact ⟨KernelFi22C.ap_tab 0 hk, KernelFi22C.ap_tab 1 hk, KernelFi22C.ap_tab 2 hk,
    KernelFi22C.ap_tab 3 hk, h1, h2, h3, h4⟩

end CertificateChecks.KernelFi22LH
