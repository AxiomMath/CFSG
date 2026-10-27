module

public import Certificates.Kernel.E6TwD4T2.Data
public import Certificates.Data.Kernel.E6TwD4T2.Kit

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelE6TwD4T2

open CFSG.KD.E6TwD4T2

theorem ch214101_planes : planesOK = true := by decide +kernel

theorem ch214101_r3 : r3OK r3 = true := by decide +kernel

theorem ch214101_tab : tabOK r3 wts wlv = true := by decide +kernel

theorem ch214101_sig : sigOK r3 sig sigL = true := by decide +kernel

theorem ch214101_g : gOK wlv G = true := by decide +kernel

theorem ch214101_pairs : pairsK wlv sigL G 729 = true := by decide +kernel

theorem ch214103_stab : stabK r3 elems negs = true := by decide +kernel

end CertificateChecks.KernelE6TwD4T2
