module

public import Certificates.Kernel.Sporadic.ON.Assemble
public import Certificates.Kernel.Sporadic.ON.MV0
public import Certificates.Kernel.Sporadic.ON.MV1
public import Certificates.Kernel.Sporadic.ON.MV2
public import Certificates.Kernel.Sporadic.ON.MV3
public import Certificates.Kernel.Sporadic.ON.MV4
public import Certificates.Kernel.Sporadic.ON.MV5
public import Certificates.Kernel.Sporadic.ON.MV6
public import Certificates.Kernel.Sporadic.ON.MV7
public import Certificates.Kernel.Sporadic.ON.TR0
public import Certificates.Kernel.Sporadic.ON.TR1
public import Certificates.Kernel.Sporadic.ON.TR2
public import Certificates.Kernel.Sporadic.ON.TR3
public import Certificates.Kernel.Sporadic.ON.TR4
public import Certificates.Kernel.Sporadic.ON.TR5
public import Certificates.Kernel.Sporadic.ON.TR6
public import Certificates.Kernel.Sporadic.ON.TR7
public import Certificates.Kernel.Sporadic.ON.TR8
public import Certificates.Kernel.Sporadic.ON.TR9
public import Certificates.Kernel.Sporadic.ON.TR10
public import Certificates.Kernel.Sporadic.ON.TR11
public import Certificates.Kernel.Sporadic.ON.TR12
public import Certificates.Kernel.Sporadic.ON.TR13
public import Certificates.Kernel.Sporadic.ON.TR14
public import Certificates.Kernel.Sporadic.ON.TR15
public import Certificates.Kernel.Sporadic.ON.TrNetChk
public import Certificates.Kernel.Sporadic.ON.OrdSort

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON.mvAll CertificateChecks.KernelSpor.ON.mvS 1023

#kon_join CertificateChecks.KernelSpor.ON.trPAll CertificateChecks.KernelSpor.ON.trP 1023

#kon_join CertificateChecks.KernelSpor.ON.netAll CertificateChecks.KernelSpor.ON.netC 16

#kon_join CertificateChecks.KernelSpor.ON.wordAll CertificateChecks.KernelSpor.ON.wordK 5

#kon_join CertificateChecks.KernelSpor.ON.ordAll CertificateChecks.KernelSpor.ON.ordS 1023

#kon_join CertificateChecks.KernelSpor.ON.sortAll CertificateChecks.KernelSpor.ON.sortS 1023

namespace CertificateChecks.KernelSpor.ON

theorem trAll : ∀ s < 1023, trS s = true := trS_of_net trPAll eidS0 netAll wordAll

theorem qon_eq' : CFSG.ONSchreier.qonStrongArrs =
    Array.ofFn (n := 7) fun j => Array.ofFn (n := 245520) fun i => TT j.val i.val :=
  qon_eq mvAll ordAll sortAll trAll

theorem perm_facts' : ∀ x < 245520, ∀ j < 7, TT j x < 245520 ∧ UU j x < 245520 ∧
    UU j (TT j x) = x :=
  perm_facts trAll

end CertificateChecks.KernelSpor.ON

end
