module

public import Certificates.Data.Kernel.Misc.PermG2U
public import CFSG.Quasithin.Background.G2UCodes
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public meta import Certificates.Kernel.Misc.Perm.G2UGen
public import Mathlib

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelMisc.G2U.RE CFSG.KC.Misc.G2UGen.rE
#kss_natlist CertificateChecks.KernelMisc.G2U.GR CFSG.KC.Misc.G2UGen.rG
#kss_natlist CertificateChecks.KernelMisc.G2U.RP CFSG.KC.Misc.G2UGen.rP
#kss_natlist CertificateChecks.KernelMisc.G2U.RS CFSG.KC.Misc.G2UGen.rS
#kss_natlist CertificateChecks.KernelMisc.G2U.RC CFSG.KC.Misc.G2UGen.rC
#kss_natlist CertificateChecks.KernelMisc.G2U.DE CFSG.KC.Misc.G2UGen.dE
#kss_natlist CertificateChecks.KernelMisc.G2U.GD CFSG.KC.Misc.G2UGen.dG
#kss_natlist CertificateChecks.KernelMisc.G2U.DP CFSG.KC.Misc.G2UGen.dP
#kss_natlist CertificateChecks.KernelMisc.G2U.DS CFSG.KC.Misc.G2UGen.dS
#kss_natlist CertificateChecks.KernelMisc.G2U.DC CFSG.KC.Misc.G2UGen.dC

namespace CertificateChecks.KernelMisc.G2U

open CFSG.KC.Misc.Clos CFSG.KC.Misc.G2U CFSG.Quasithin.G2U

@[expose] noncomputable def oneD : Nat := Nat.add (codes9 id3) (Nat.mul (2 ^ 36) (rows2 id2))

@[expose] noncomputable def rtB (q : Nat) : Bool :=
  allR (Nat.mul 1008 q) 1008 (treeAt m2 (rows2 id2) GR 4 RE RP)

@[expose] noncomputable def rsB (q : Nat) : Bool := allR (Nat.mul 1008 q) 1008 (sortAt 12096 RE RS)

@[expose] noncomputable def rcB (q : Nat) : Bool :=
  allR (Nat.mul 1008 q) 1008 (closedAt m2 GR 4 12096 RE RC)

@[expose] noncomputable def dtB (q : Nat) : Bool :=
  allR (Nat.mul 1008 q) 1008 (treeAt mP oneD GD 2 DE DP)

@[expose] noncomputable def dsB (q : Nat) : Bool := allR (Nat.mul 1008 q) 1008 (sortAt 6048 DE DS)

@[expose] noncomputable def dcB (q : Nat) : Bool :=
  allR (Nat.mul 1008 q) 1008 (closedAt mP GD 2 6048 DE DC)

@[expose] noncomputable def dpB (q : Nat) : Bool :=
  allR (Nat.mul 1008 q) 1008 (pairAt (rows2 id2) (codes9 id3) DE)

end CertificateChecks.KernelMisc.G2U

#kc_slices CertificateChecks.KernelMisc.G2U.RTK CertificateChecks.KernelMisc.G2U.rtB 12
#kc_slices CertificateChecks.KernelMisc.G2U.RSK CertificateChecks.KernelMisc.G2U.rsB 12
#kc_slices CertificateChecks.KernelMisc.G2U.RCK CertificateChecks.KernelMisc.G2U.rcB 12
#kc_slices CertificateChecks.KernelMisc.G2U.DTK CertificateChecks.KernelMisc.G2U.dtB 6
#kc_slices CertificateChecks.KernelMisc.G2U.DSK CertificateChecks.KernelMisc.G2U.dsB 6
#kc_slices CertificateChecks.KernelMisc.G2U.DCK CertificateChecks.KernelMisc.G2U.dcB 6
#kc_slices CertificateChecks.KernelMisc.G2U.DPK CertificateChecks.KernelMisc.G2U.dpB 6

end
