module

public import Certificates.Kernel.LocalComp.HeGlueData
public import Certificates.Kernel.LocalComp.HeModelEnum
public import Certificates.Kernel.LocalComp.HeModelEnumP23
public import Certificates.Kernel.LocalComp.HeModelEnumC
public import Certificates.Kernel.LocalComp.HexaOrb
public import Certificates.Data.Kernel.HeGlueK

public section

namespace CertificateChecks.KernelLC.HeGlue

open CertificateChecks.KernelLC

@[expose] noncomputable def hd : CFSG.KC.HeGlueK.GK where
  NP := HeMP12.N
  TP := HeMP12.T
  IP := HeGlueD.IP
  NB := HeMB0.N
  TB := HeMB0.T
  SB := HeMB0.S
  gB := HeMB0.ng
  GB := HeMB0.G
  N23 := HeMP23.N
  T23 := HeMP23.T
  I23 := HeGlueD.I23
  g23 := HeMP23.ng
  G23 := HeMP23.G
  G23I := HeGlueD.G23I
  RE := HeGlueD.RE
  REI := HeGlueD.REI
  RF := HeGlueD.RF
  RFI := HeGlueD.RFI
  CF := HeGlueD.CF
  CFI := HeGlueD.CFI
  PE := HeGlueD.PE
  PEI := HeGlueD.PEI
  PF := HeGlueD.PF
  PFI := HeGlueD.PFI
  t0 := HexaOrb.PT0
  t0I := HeGlueD.XY 0
  YTI := HeGlueD.XY 1
  gT := HexaT.ng
  GT := HexaT.G
  gM := HexaM.ng
  GM := HexaM.G
  gR := HexaR.ng
  GR := HexaR.G
  N0 := HeMP0.N
  T0 := HeMP0.T
  N1 := HeMP1.N
  T1 := HeMP1.T
  NBC := HeMBC.N
  TBC := HeMBC.T
  G12 := HeMP0.G
  G12I := HeGlueD.G12I
  G13 := HeMP1.G
  G13I := HeGlueD.G13I
  PC0 := HeGlueD.PC0
  PC0I := HeGlueD.PC0I
  PC1 := HeGlueD.PC1
  PC1I := HeGlueD.PC1I
  gBC := HeMBC.ng
  GBC := HeMBC.G
  tc := HeGlueD.TC 0
  gC := HeMC.ng
  GC := HeMC.G

end CertificateChecks.KernelLC.HeGlue

end
