module

public import Certificates.Kernel.Sporadic.OddCore.S8147R
public import Certificates.Kernel.Sporadic.OddCore.S8147G

public section

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore

theorem facts8147 :
    (suzFiveQCheck suzFiveQCert suzFiveLines = true) ∧
    (∀ i < 6, suzFiveCCheck (suzFiveCArrs i) (suzFiveLineArr i) (suzFiveCCert i)
      suzFiveCentOrders[i]! = true) ∧
    suzFiveDCheck (suzFiveCArrs 0) (suzFiveCCert 0) (suzFiveDArrs 0)
      (suzFiveDCert 0) 360 (suzFiveLineArr 0) 5 = true ∧
    suzFiveDCheck (suzFiveCArrs 1) (suzFiveCCert 1) (suzFiveDArrs 1)
      (suzFiveDCert 1) 60 (suzFiveLineArr 1) 10 = true ∧
    suzFiveDCheck (suzFiveCArrs 2) (suzFiveCCert 2) (suzFiveDArrs 2)
      (suzFiveDCert 2) 60 (suzFiveLineArr 2) 10 = true ∧
    suzFiveDCheck (suzFiveCArrs 3) (suzFiveCCert 3) (suzFiveDArrs 3)
      (suzFiveDCert 3) 360 (suzFiveLineArr 3) 5 = true ∧
    suzFiveDCheck (suzFiveCArrs 4) (suzFiveCCert 4) (suzFiveDArrs 4)
      (suzFiveDCert 4) 360 (suzFiveLineArr 4) 5 = true ∧
    suzFiveDCheck (suzFiveCArrs 5) (suzFiveCCert 5) (suzFiveDArrs 5)
      (suzFiveDCert 5) 60 (suzFiveLineArr 5) 10 = true ∧
    (∀ i < 6, suzFivePairsCheck i = true) ∧
    (∀ i < 6, suzFiveOrbitCheck (suzFiveDArrs i) suzFiveOrbits[i]! suzFiveOrbits[i]!.length
      suzFiveDerivedOrders[i]! (suzFiveOrbitCert i) = true) ∧
    (∀ i < 6, suzFiveGraphCheck (suzFiveLineArr i) suzFiveInit[i]! suzFiveSteps[i]! = true) := by
  refine ⟨qCheck, fun i hi => ?_, dOK0, dOK1, dOK2, dOK3, dOK4, dOK5, fun i hi => ?_,
    fun i hi => ?_, fun i hi => graphCheck hi⟩
  · interval_cases i
    · exact ccOK0
    · exact ccOK1
    · exact ccOK2
    · exact ccOK3
    · exact ccOK4
    · exact ccOK5
  · interval_cases i
    · exact prOK0
    · exact prOK1
    · exact prOK2
    · exact prOK3
    · exact prOK4
    · exact prOK5
  · interval_cases i
    · exact orOK0
    · exact orOK1
    · exact orOK2
    · exact orOK3
    · exact orOK4
    · exact orOK5

end CertificateChecks.KernelSpor.S8147

end
