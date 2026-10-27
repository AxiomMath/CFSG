module

public import Certificates.Data.Kernel.J2H2.Stable
public import Certificates.Kernel.J2H2.Data
public import Certificates.Kernel.J2Cover.ModelsP
public import Certificates.Kernel.J2Cover.OrbData
public import Certificates.Data.J2H2Sylow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.J2H2

open CFSG.KC.Enum CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue
open CertificateChecks.KernelJ2Cover (ALP BEP ELT)

theorem conjOK : conjK ALP BEP ELT CW CQ = true := by quickRfl

theorem rgOK : rgK C4725.aCols (matMulK C4725.bCols C4725.bCols) CW RGI = true := by quickRfl

theorem spgOK : spgK RGI SPG = true := by quickRfl

theorem rsOK : rsK RS GP PP C4725.aCols C4725.bCols yWords = true := by quickRfl

theorem phiOK0 : phiK MTP RS CQ PHI NL 0 = true := by quickRfl
theorem phiOK1 : phiK MTP RS CQ PHI NL 1 = true := by quickRfl
theorem phiOK2 : phiK MTP RS CQ PHI NL 2 = true := by quickRfl
theorem phiOK3 : phiK MTP RS CQ PHI NL 3 = true := by quickRfl
theorem phiOK4 : phiK MTP RS CQ PHI NL 4 = true := by quickRfl

theorem phvOK : strictB (rowsPack HR) (fun HP => phvK HP CQ PHI SPG NL PHV) = true := by quickRfl

theorem rankOK : rankK PHV IND RINV = true := by quickRfl

theorem relOK : strictB (rowsPack HR) (fun HP => strictB repN (fun REP =>
    allN 3 (fun k => relK HP REP LMP BR SP DEPA k))) = true := by quickRfl

theorem covOK : covK IND DEPA BR = true := by quickRfl

end CFSG.KD.J2H2

end
