module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34DWord
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

namespace CertificateChecks.KernelLC.L34Fix

open CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen

meta def hM : Array (Array Nat) := hGens

meta def m0 : Array (Array Nat) := mGens[0]!

meta def m1 : Array (Array Nat) := mGens[1]!

meta def m2 : Array (Array Nat) := mGens[2]!

meta def m3 : Array (Array Nat) := mGens[3]!

meta def id42 : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelLC.L34Fix

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelLC.L34FH 42 6 false CertificateChecks.KernelLC.L34Fix.hM
  CertificateChecks.KernelLC.L34Fix.hM CertificateChecks.KernelLC.L34Fix.id42 27
#kpenum CertificateChecks.KernelLC.L34FM0 42 6 false CertificateChecks.KernelLC.L34Fix.m0
  CertificateChecks.KernelLC.L34Fix.m0 CertificateChecks.KernelLC.L34Fix.id42 9
#kpenum CertificateChecks.KernelLC.L34FM1 42 6 false CertificateChecks.KernelLC.L34Fix.m1
  CertificateChecks.KernelLC.L34Fix.m1 CertificateChecks.KernelLC.L34Fix.id42 9
#kpenum CertificateChecks.KernelLC.L34FM2 42 6 false CertificateChecks.KernelLC.L34Fix.m2
  CertificateChecks.KernelLC.L34Fix.m2 CertificateChecks.KernelLC.L34Fix.id42 9
#kpenum CertificateChecks.KernelLC.L34FM3 42 6 false CertificateChecks.KernelLC.L34Fix.m3
  CertificateChecks.KernelLC.L34Fix.m3 CertificateChecks.KernelLC.L34Fix.id42 9

#kc_repo #kc_natList CertificateChecks.KernelLC.L34FW WL "Certificates/Kernel/LocalComp/L34Fix/w.txt" 174 2894627814913390236

namespace CertificateChecks.KernelLC

@[expose] noncomputable def L34FM.T (k q : Nat) : Nat :=
  nIf(Nat.beq k 0, L34FM0.T q, nIf(Nat.beq k 1, L34FM1.T q,
    nIf(Nat.beq k 2, L34FM2.T q, L34FM3.T q)))

@[expose] noncomputable def L34FM.G (k j : Nat) : Nat :=
  nIf(Nat.beq k 0, L34FM0.G j, nIf(Nat.beq k 1, L34FM1.G j,
    nIf(Nat.beq k 2, L34FM2.G j, L34FM3.G j)))

@[expose] noncomputable def L34FW.RI : List Nat :=
  [32219, 12202, 13892, 32219, 13892, 12202, 13892, 108719, 13892, 130259]

@[expose] noncomputable def L34FW.SI : List Nat := [13707, 19874]

@[expose] noncomputable def L34FW.FI : List Nat := [19847, 13344, 18241, 8602, 12304, 19847]

@[expose] noncomputable def L34FW.FQ : List Nat := [1, 6, 6, 2, 4, 1]

@[expose] noncomputable def L34FW.A (k j : Nat) : Nat :=
  L34S.T (L34FW.FI.getD (Nat.add (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 1))) j) (nat_lit 0))

end CertificateChecks.KernelLC

end
