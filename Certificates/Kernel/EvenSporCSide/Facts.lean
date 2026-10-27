module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheck

public section

namespace CertificateChecks.KernelCSide

open CFSG.EvenSporadicStandard.HNRecog.CSide

set_option maxHeartbeats 0 in
theorem k6a : cSideK6a := by decide +kernel

set_option maxHeartbeats 0 in
theorem k6c : cSideK6c := by decide +kernel

set_option maxHeartbeats 0 in
theorem k4a : cSideK4a := by decide +kernel

set_option maxHeartbeats 0 in
theorem k4d : cSideK4d := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep4b : cSideRep4b := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep4c : cSideRep4c := by decide +kernel

set_option maxHeartbeats 0 in
theorem k3 : cSideK3 := by decide +kernel

set_option maxHeartbeats 0 in
theorem k1 : cSideK1 := by decide +kernel

set_option maxHeartbeats 0 in
theorem k2 : cSideK2 := by decide +kernel

end CertificateChecks.KernelCSide
