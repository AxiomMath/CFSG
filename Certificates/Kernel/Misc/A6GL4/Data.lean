module

public import Certificates.Data.Kernel.Misc.A6GL4
public import Certificates.Kernel.Misc.GL4.EAData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.A6GL4 HE
  "Certificates/Kernel/Misc/A6GL4/data/he.bin" 4 4 1440 6831010415345600879
#kc_repo #kc_ktree CertificateChecks.KernelMisc.A6GL4 HP
  "Certificates/Kernel/Misc/A6GL4/data/hp.bin" 4 4 1440 7488587590701607112
#kc_repo #kc_ktree CertificateChecks.KernelMisc.A6GL4 HS
  "Certificates/Kernel/Misc/A6GL4/data/hs.bin" 4 4 1440 5854035795925314059
#kc_repo #kc_ktree CertificateChecks.KernelMisc.A6GL4 HC
  "Certificates/Kernel/Misc/A6GL4/data/hc.bin" 4 4 2880 4719884813105099199
#kc_repo #kc_ktree CertificateChecks.KernelMisc.A6GL4 W
  "Certificates/Kernel/Misc/A6GL4/data/w.bin" 8 4 161280 7780480862332082604

namespace CertificateChecks.KernelMisc.A6GL4

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.GL4 CFSG.KC.Misc.A6GL4
open CertificateChecks.KernelMisc.GL4EA (EA EAI)

@[expose] noncomputable def xA6 : Nat := nat_lit 33300

@[expose] noncomputable def yA6 : Nat := nat_lit 51833

@[expose] noncomputable def gH (j : Nat) : Nat := lAt [xA6, yA6] j

@[expose] noncomputable def RL (i : Nat) : Nat :=
  lAt [33825, 33825, 33833, 33833, 33829, 33829, 33837, 33837, 33953, 33953,
    33961, 33961, 33957, 33957, 33965, 33965, 33889, 33889, 33897, 33897,
    33893, 33893, 33901, 33901, 34017, 34017, 34025, 34025, 34021, 34021,
    34029, 34029, 34369, 33377, 34377, 33385, 34373, 33379, 34381, 33387,
    36417, 33505, 36425, 33513, 36421, 33507, 36429, 33515, 34388, 33107,
    34516, 33115, 36436, 33235, 36564, 33243] i

@[expose] noncomputable def closS (_ : Nat) : Bool :=
  allR 0 (nat_lit 360) fun k => andB (treeAt mul4F id4 gH (nat_lit 2) HE HP k)
    (andB (sortAt (nat_lit 360) HE HS k) (closedAt mul4F gH (nat_lit 2) (nat_lit 360) HE HC k))

@[expose] noncomputable def yS (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 5040) s) (nat_lit 5040) (yAt EA EAI W yA6)

@[expose] noncomputable def xS (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 5040) s) (nat_lit 5040) (xAt EA EAI W HE yA6)

@[expose] noncomputable def djS (_ : Nat) : Bool := djB HE HS RL xA6 yA6 (nat_lit 28)

end CertificateChecks.KernelMisc.A6GL4

end
