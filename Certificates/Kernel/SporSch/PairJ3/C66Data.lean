module

public meta import Certificates.Kernel.Misc.Perm.Cmd
public import Certificates.Kernel.Misc.Perm.Cmd

namespace CertificateChecks.KernelSporSch.C66In

meta def fiP : String := include_str "c66/fi_par.hex"
meta def fiG : String := include_str "c66/fi_gen.hex"
meta def fiD : String := include_str "c66/fi_dep.hex"
meta def foP : String := include_str "c66/fo_par.hex"
meta def foG : String := include_str "c66/fo_gen.hex"
meta def foD : String := include_str "c66/fo_dep.hex"
meta def rI : String := include_str "c66/ri.hex"
meta def rO : String := include_str "c66/ro.hex"
meta def wI : String := include_str "c66/wi.hex"
meta def wO : String := include_str "c66/wo.hex"

end CertificateChecks.KernelSporSch.C66In

#kmisc_tree CertificateChecks.KernelSporSch.C66D.FIP CertificateChecks.KernelSporSch.C66In.fiP 4 26163
#kmisc_tree CertificateChecks.KernelSporSch.C66D.FIG CertificateChecks.KernelSporSch.C66In.fiG 1 26163
#kmisc_tree CertificateChecks.KernelSporSch.C66D.FID CertificateChecks.KernelSporSch.C66In.fiD 2 26163
#kmisc_tree CertificateChecks.KernelSporSch.C66D.FOP CertificateChecks.KernelSporSch.C66In.foP 4 20520
#kmisc_tree CertificateChecks.KernelSporSch.C66D.FOG CertificateChecks.KernelSporSch.C66In.foG 1 20520
#kmisc_tree CertificateChecks.KernelSporSch.C66D.FOD CertificateChecks.KernelSporSch.C66In.foD 2 20520
#kmisc_tree CertificateChecks.KernelSporSch.C66D.RI CertificateChecks.KernelSporSch.C66In.rI 4 27
#kmisc_tree CertificateChecks.KernelSporSch.C66D.RO CertificateChecks.KernelSporSch.C66In.rO 4 22
#kmisc_tree CertificateChecks.KernelSporSch.C66D.WI CertificateChecks.KernelSporSch.C66In.wI 8 108
#kmisc_tree CertificateChecks.KernelSporSch.C66D.WO CertificateChecks.KernelSporSch.C66In.wO 8 88
