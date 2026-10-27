module

public import Certificates.Kernel.Q8Wit.J3EnumK
public import Certificates.Kernel.Q8Wit.J3Data
public import Certificates.Kernel.Q8Wit.J3Chunks
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Census.J3.Text
public import Certificates.Data.Kernel.Q8WitP
public import Certificates.Data.Kernel.PGrp
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit Certificates.TwinPerpSmSp1
open CertificateChecks.KernelSpor (J3CentP)
open CertificateChecks.KernelCensus (J3S.F)

theorem hw : szOK 6156 13 = true := by quickRfl

theorem permPG : allN 8 (fun j => permB 6156 13 (J3CentP (j + 1))) = true := by quickRfl

theorem permXG : allN 2 (fun j => permB 6156 13 (J3S.F j)) = true := by quickRfl

theorem lettersQ : (j3Wit.syl.qW.toList.all fun wd => wd.all fun l => decide (l < 8)) = true := by
  decide +kernel

theorem lettersC : (j3Wit.cW.toList.all fun wd => wd.all fun l => decide (l < 2)) = true := by
  decide +kernel

theorem wordsQ : j3Wit.syl.qW.toList.map (posWordK 6156 13 fun j => J3CentP (j + 1)) =
    (List.range J3Q.ng).map J3Q.G := by
  decide +kernel

theorem lettersW : (JC.W.all fun c => c.all fun l => decide (l < 2)) = true := by
  decide +kernel

theorem flatC : (JC.I.map (fun ik => (ik.map fun j => JC.W.getD j []).flatten) ==
    j3Wit.cW.toList) = true := by
  decide +kernel

theorem chunksC : (JC.I.map (posWordK 6156 13 JD) == (List.range nc).map C) = true := by
  decide +kernel

theorem invs : invsK 6156 13 nc C CI = true := by quickRfl

end CertificateChecks.KernelQ8W.J3

end
