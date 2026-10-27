
module

public import Certificates.Kernel.SporSch.Co2M.FratD

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def siftF (G : ℕ) : Bool :=
  strictB G fun G =>
    siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2LF.LR Co2LF.TRI Co2LF.BP 2 0 G

@[expose] noncomputable def pc (p q : ℕ) : ℕ :=
  strictN p fun p => strictN q fun q => pcomp 2300 12 (mask 12) p q

end CertificateChecks.KernelSporSch.Co2M

end
