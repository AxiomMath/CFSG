module

public import Certificates.Data.E27.LyS0
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelLyS0.T "Certificates/Kernel/LyS0/data/tab.bin"
  6 4 65535 396640 13471361404502399226

#kc_repo #kc_items_root CertificateChecks.KernelLyS0.GI "Certificates/Kernel/LyS0/data/gens.items"
  92416 16726903003655009276

#ks_chars CertificateChecks.KernelLyS0.OS CFSG.Sporadic.Ly.S0.opsStr

#ks_chars CertificateChecks.KernelLyS0.PS CFSG.Sporadic.Ly.S0.parStr

#ks_chars CertificateChecks.KernelLyS0.LS CFSG.Sporadic.Ly.S0.LStr

end
