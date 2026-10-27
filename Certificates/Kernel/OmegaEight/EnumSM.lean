module

public import CFSG.Certificates.Kernel.O8EnumSound
public meta import Certificates.Kernel.OmegaEight.EnumGen
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData
public import Certificates.Kernel.OmegaEight.EnumGen

meta def CertificateChecks.KernelO8.s1GensM : Array (ℕ × ℕ) :=
  CFSG.EvenSmallLie.OmegaEight.Stage2.stage1Gens .minus

public section

#ks_enum CertificateChecks.KernelO8.EnSM CertificateChecks.KernelO8.s1GensM

end
