module

public import CFSG.Certificates.Kernel.O8EnumSound
public meta import Certificates.Kernel.OmegaEight.EnumGen
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData
public import Certificates.Kernel.OmegaEight.EnumGen

meta def CertificateChecks.KernelO8.s1GensP : Array (ℕ × ℕ) :=
  CFSG.EvenSmallLie.OmegaEight.Stage2.stage1Gens .plus

public section

#ks_enum CertificateChecks.KernelO8.EnSP CertificateChecks.KernelO8.s1GensP

end
