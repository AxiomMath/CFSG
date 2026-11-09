module

public import Certificates.Kernel.SporSch.Pair.McLCheck

public section

namespace CertificateChecks.KernelSporSch.PMcLCheck

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairMcL
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem facts_proved : (rawChainOK 275 (mclStrongArrs.extract 0 2) mclStrongArrs baseArr mclWords 4 = true ∧
      rawOrbitSizes 275 mclStrongArrs baseArr = [275, 112, 81, 45, 8])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true) :=
  facts

end CertificateChecks.KernelSporSch.PMcLCheck

end
