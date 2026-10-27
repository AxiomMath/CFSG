module

public import Certificates.Kernel.SporSch.Co1.OrbX61
public import Certificates.Kernel.SporSch.Co1.OrbF2
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.Kernel.SporSch.Co1Tower
public import CFSG.Sporadic.Schreier.Co1AutCheckInputs
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.Co1.GenTower
public meta import CFSG.Sporadic.Schreier.Co1AutCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenDag
public import Certificates.Kernel.SporSch.Co1.GenTower

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelSporSch.Co1Aut.SD CFSG.Sporadic.Co1Schreier.Native.stabDag

#kss_co1tower CertificateChecks.KernelSporSch.Co1Aut.TW CFSG.Sporadic.Co1Schreier.Native.stabDag
  CertificateChecks.KernelSporSch.Co1Aut.SD.M CFSG.Sporadic.Co1Schreier.Data.stabTowerBase
  CFSG.Sporadic.Co1Schreier.Data.stabTowerGens CFSG.Sporadic.Co1Schreier.Data.stabTowerSizes 85 512

namespace CertificateChecks.KernelSporSch.Co1Aut

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
open CertificateChecks.KernelSporSch.Co1Stab CertificateChecks.KernelSporSch.Co1Packed
open CertificateChecks.KernelSporSch.Co1Orbs

theorem kb0 : Nat.beq (SD.M 0) PH0 = true := by quickRfl
theorem kb1 : Nat.beq (SD.M 1) PH1 = true := by quickRfl
theorem kN : Nat.beq SD.N 85 = true := by quickRfl
theorem kD : dagIK SD.M SD.MI 2 SD.N Data.stabDerivs = true := by quickRfl

theorem f0 : fixesK SD.M (Data.stabTowerGens.getD 0 []) Data.stabTowerBase 0 = true := by quickRfl
theorem f1 : fixesK SD.M (Data.stabTowerGens.getD 1 []) Data.stabTowerBase 1 = true := by quickRfl
theorem f2 : fixesK SD.M (Data.stabTowerGens.getD 2 []) Data.stabTowerBase 2 = true := by quickRfl
theorem f3 : fixesK SD.M (Data.stabTowerGens.getD 3 []) Data.stabTowerBase 3 = true := by quickRfl
theorem f4 : fixesK SD.M (Data.stabTowerGens.getD 4 []) Data.stabTowerBase 4 = true := by quickRfl

theorem kNL : nonlinK PA O3.T O3.S F2.T F2.S 16663704 6244414 11752856 15263478 Data.nonlinVecs =
    true := by quickRfl

end CertificateChecks.KernelSporSch.Co1Aut

end
