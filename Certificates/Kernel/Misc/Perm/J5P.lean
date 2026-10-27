module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.RankThree.PartOne.KS.J2FiveChains
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartOne.KS.J2FiveChains
meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs

set_option maxRecDepth 400000

meta def CertificateChecks.KernelMisc.J2F.strongM : Array (Array Nat) :=
  CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ()

#ks_rawchain CertificateChecks.KernelMisc.J2F.P 315 9 0
  CertificateChecks.KernelMisc.J2F.strongM CFSG.Sporadic.Schreier.PairJ2.baseArr 7
  CFSG.RankThree.PartOne.j2FiveNoWords
