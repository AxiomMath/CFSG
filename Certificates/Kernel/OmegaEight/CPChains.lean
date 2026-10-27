module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.CPBases
public meta import Certificates.Kernel.OmegaEight.CPBases
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

#ks_rawchain CertificateChecks.KernelO8.UP 120 9 24
  CFSG.EvenSmallLie.OmegaEight.Stage1.Model.uSPlus CertificateChecks.KernelO8.uBaseP 12
  CertificateChecks.KernelO8.noWords

#ks_rawchain CertificateChecks.KernelO8.UM 136 8 17
  CFSG.EvenSmallLie.OmegaEight.Stage1.Model.uSMinus CertificateChecks.KernelO8.uBaseM 12
  CertificateChecks.KernelO8.noWords

#ks_rawchain CertificateChecks.KernelO8.PP 120 9 24
  CFSG.EvenSmallLie.OmegaEight.Stage1.Model.pSPlus CertificateChecks.KernelO8.pBaseP 12
  CertificateChecks.KernelO8.pWordsP

#ks_rawchain CertificateChecks.KernelO8.PM 136 8 17
  CFSG.EvenSmallLie.OmegaEight.Stage1.Model.pSMinus CertificateChecks.KernelO8.pBaseM 12
  CertificateChecks.KernelO8.pWordsM

#ks_rawchain CertificateChecks.KernelO8.LMn 136 8 0 CFSG.EvenSmallLie.OmegaEightMinus.omegaS
  CertificateChecks.KernelO8.lBaseM 10 CFSG.EvenSmallLie.OmegaEightMinus.omegaWords

end
