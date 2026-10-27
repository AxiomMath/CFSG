module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSC

open CFSG.Sporadic.RuSchreier

@[expose] def blkCD : List (List Int) := [[-2, -1], [-1, -1, 2, 1], [3, -4], [3, 4, 3]]

@[expose] def blkND : List (List Int) := [[-1, 2, 1], [-2, 3, 1], [3, -4, -3, 4, 3]]

meta def sQ : Array (Array Nat) := ruField80
meta def bQ : Array Nat := ruBaseArr 80 ruCQuotient80Base
meta def sK : Array (Array Nat) := ruField1920 2
meta def bK : Array Nat := ruBaseArr 1920 ruKBase
meta def sJ : Array (Array Nat) := ruField1920 3
meta def bJ : Array Nat := ruBaseArr 1920 ruJBase
meta def sR : Array (Array Nat) := ruField1920 4
meta def bR : Array Nat := ruBaseArr 1920 ruRBase
meta def sBC : Array (Array Nat) := ruCBlockStrong
meta def bBC : Array Nat := ruBaseArr 6 [0, 2, 1]
meta def sBN : Array (Array Nat) := ruNBlockStrong
meta def bBN : Array Nat := ruBaseArr 7 [1, 0, 2]

end CertificateChecks.KernelSporSch.RuSC

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuQS 80 7 2 8
  CertificateChecks.KernelSporSch.RuSC.sQ CertificateChecks.KernelSporSch.RuSC.bQ 2
  CFSG.Sporadic.RuSchreier.ruCQuotient80Derivations

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuKS 1920 11 2 16
  CertificateChecks.KernelSporSch.RuSC.sK CertificateChecks.KernelSporSch.RuSC.bK 8
  CFSG.Sporadic.RuSchreier.ruKDerivations

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuJS2 1920 11 2 16
  CertificateChecks.KernelSporSch.RuSC.sJ CertificateChecks.KernelSporSch.RuSC.bJ 6
  CFSG.Sporadic.RuSchreier.ruJDerivations

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuRS2 1920 11 2 16
  CertificateChecks.KernelSporSch.RuSC.sR CertificateChecks.KernelSporSch.RuSC.bR 5
  CFSG.Sporadic.RuSchreier.ruRDerivations

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuBC 6 3 2 8
  CertificateChecks.KernelSporSch.RuSC.sBC CertificateChecks.KernelSporSch.RuSC.bBC 2
  CertificateChecks.KernelSporSch.RuSC.blkCD

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuBN 7 4 2 8
  CertificateChecks.KernelSporSch.RuSC.sBN CertificateChecks.KernelSporSch.RuSC.bBN 2
  CertificateChecks.KernelSporSch.RuSC.blkND

end
