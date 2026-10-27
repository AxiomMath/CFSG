module

public import Certificates.Data.Kernel.Misc.PermA6Aut
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public meta import Certificates.Kernel.Misc.Perm.A6AutGen

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelMisc.A6Aut.E CFSG.KC.Misc.A6AutGen.eL
#kss_natlist CertificateChecks.KernelMisc.A6Aut.P CFSG.KC.Misc.A6AutGen.pL
#kss_natlist CertificateChecks.KernelMisc.A6Aut.S CFSG.KC.Misc.A6AutGen.sL
#kss_natlist CertificateChecks.KernelMisc.A6Aut.C CFSG.KC.Misc.A6AutGen.cL
#kss_natlist CertificateChecks.KernelMisc.A6Aut.L2 CFSG.KC.Misc.A6AutGen.l2L
#kss_natlist CertificateChecks.KernelMisc.A6Aut.L4 CFSG.KC.Misc.A6AutGen.l4L
#kss_natlist CertificateChecks.KernelMisc.A6Aut.R2 CFSG.KC.Misc.A6AutGen.r2L
#kss_natlist CertificateChecks.KernelMisc.A6Aut.R4 CFSG.KC.Misc.A6AutGen.r4L
#kss_natlist CertificateChecks.KernelMisc.A6Aut.W CFSG.KC.Misc.A6AutGen.wL

namespace CertificateChecks.KernelMisc.A6Aut

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CFSG.KC.Misc.A6Aut

@[expose] noncomputable def trB (_ : Nat) : Bool := allR 0 360 (treeAt mul8 one8 genC 2 E P)

@[expose] noncomputable def srB (_ : Nat) : Bool := allR 0 360 (sortAt 360 E S)

@[expose] noncomputable def clB (_ : Nat) : Bool := allR 0 360 (closedAt mul8 genC 2 360 E C)

@[expose] noncomputable def rcB (_ : Nat) : Bool :=
  andB (allR 0 360 (rec2At E L2 R2 46)) (allR 0 360 (rec4At E L4 R4 136))

@[expose] noncomputable def rwB (r : Nat) : Bool := rowAt 360 E P L2 L4 W 136 r

end CertificateChecks.KernelMisc.A6Aut

#kc_slices CertificateChecks.KernelMisc.A6Aut.TK CertificateChecks.KernelMisc.A6Aut.trB 1
#kc_slices CertificateChecks.KernelMisc.A6Aut.SK CertificateChecks.KernelMisc.A6Aut.srB 1
#kc_slices CertificateChecks.KernelMisc.A6Aut.CK CertificateChecks.KernelMisc.A6Aut.clB 1
#kc_slices CertificateChecks.KernelMisc.A6Aut.RK CertificateChecks.KernelMisc.A6Aut.rcB 1
#kc_slices CertificateChecks.KernelMisc.A6Aut.WK CertificateChecks.KernelMisc.A6Aut.rwB 46

end
