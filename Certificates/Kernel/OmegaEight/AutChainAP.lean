module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1AutData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1AutData
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.Bases
public meta import Certificates.Kernel.OmegaEight.Bases
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelO8.AP 360 9 24 CFSG.EvenSmallLie.OmegaEight.autS
  CertificateChecks.KernelO8.aBaseP 10 CFSG.EvenSmallLie.OmegaEight.autWords

end
