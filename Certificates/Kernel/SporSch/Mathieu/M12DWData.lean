module

public import Certificates.Kernel.SporSch.Mathieu.M12MData
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import Certificates.Data.Odd87F3M12
public meta import Certificates.Kernel.SporSch.Mathieu.M12MData
public meta import Certificates.Data.Odd87F3M12
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12DW

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M12MOC

meta def evAB (wd : List Int) : Array Nat := evalW 24 #[tAM, tBM] wd

meta def evL (ws : List (List Int)) : List (List Nat) := ws.map fun wd => (evAB wd).toList

meta def og13M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsInn1_3

meta def og15M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsInn1_5

meta def og23M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsInn2_3

meta def og25M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsInn2_5

meta def ogS3M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsSig_3

meta def ogS5M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsSig_5

meta def ogS11M : List (List Nat) := evL Certificates.Odd87F3.M12.oddWordsSig_11

meta def irepsM : Array (Array Nat) :=
  #[evAB Certificates.Odd87F3.M12.repWordInn1, evAB Certificates.Odd87F3.M12.repWordInn2]

meta def oneM : Array Nat := idA 24

end CertificateChecks.KernelSporSch.M12DW

#kss_packs CertificateChecks.KernelSporSch.M12DW.OG13 5 CertificateChecks.KernelSporSch.M12DW.og13M

#kss_packs CertificateChecks.KernelSporSch.M12DW.OG15 5 CertificateChecks.KernelSporSch.M12DW.og15M

#kss_packs CertificateChecks.KernelSporSch.M12DW.OG23 5 CertificateChecks.KernelSporSch.M12DW.og23M

#kss_packs CertificateChecks.KernelSporSch.M12DW.OG25 5 CertificateChecks.KernelSporSch.M12DW.og25M

#kss_packs CertificateChecks.KernelSporSch.M12DW.OGS3 5 CertificateChecks.KernelSporSch.M12DW.ogS3M

#kss_packs CertificateChecks.KernelSporSch.M12DW.OGS5 5 CertificateChecks.KernelSporSch.M12DW.ogS5M

#kss_packs CertificateChecks.KernelSporSch.M12DW.OGS11 5
  CertificateChecks.KernelSporSch.M12DW.ogS11M

#kss_classes2 CertificateChecks.KernelSporSch.M12ICL 24 5 CertificateChecks.KernelSporSch.M12MOC.tAM
  CertificateChecks.KernelSporSch.M12MOC.tBM CertificateChecks.KernelSporSch.M12MOC.tA
  CertificateChecks.KernelSporSch.M12MOC.tB CertificateChecks.KernelSporSch.M12DW.irepsM 2 1000

namespace CertificateChecks.KernelSporSch.M12DW

@[expose] noncomputable def One : Nat := CFSG.KC.Enum.pidn 24 5

end CertificateChecks.KernelSporSch.M12DW

#kss_cntord2 CertificateChecks.KernelSporSch.M12IX CertificateChecks.KernelSporSch.M12DQ 24 5
  CertificateChecks.KernelSporSch.M12MOC.SM CertificateChecks.KernelSporSch.M12MOC.baseM
  CertificateChecks.KernelSporSch.M12DW.One CertificateChecks.KernelSporSch.M12DW.oneM 2

end
