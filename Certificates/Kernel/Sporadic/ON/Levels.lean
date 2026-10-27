module

public import Certificates.Kernel.Sporadic.ON.LvAssemble
public import Certificates.Kernel.Sporadic.ON.LvPt0a
public import Certificates.Kernel.Sporadic.ON.LvPt0b
public import Certificates.Kernel.Sporadic.ON.LvPt1
public import Certificates.Kernel.Sporadic.ON.LvPos
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON.pt0All CertificateChecks.KernelSpor.ON.pt0S 1023

#kon_join CertificateChecks.KernelSpor.ON.pt1All CertificateChecks.KernelSpor.ON.pt1S 218

#kon_join CertificateChecks.KernelSpor.ON.pt2All CertificateChecks.KernelSpor.ON.pt2S 1

#kon_join CertificateChecks.KernelSpor.ON.pos0All CertificateChecks.KernelSpor.ON.pos0S 8

#kon_join CertificateChecks.KernelSpor.ON.pos1All CertificateChecks.KernelSpor.ON.pos1S 8

#kon_join CertificateChecks.KernelSpor.ON.pos2All CertificateChecks.KernelSpor.ON.pos2S 8

namespace CertificateChecks.KernelSpor.ON

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem posTAll : ∀ s < 29, 3 ≤ s → posT s = true := by
  intro s hs h3
  interval_cases s
  · exact posT3
  · exact posT4
  · exact posT5
  · exact posT6
  · exact posT7
  · exact posT8
  · exact posT9
  · exact posT10
  · exact posT11
  · exact posT12
  · exact posT13
  · exact posT14
  · exact posT15
  · exact posT16
  · exact posT17
  · exact posT18
  · exact posT19
  · exact posT20
  · exact posT21
  · exact posT22
  · exact posT23
  · exact posT24
  · exact posT25
  · exact posT26
  · exact posT27
  · exact posT28

theorem qon_SA : CFSG.ONSchreier.qonStrongArrs = SA := qon_eq'

theorem cLevels_eq' :
    cLevels 245520 CFSG.ONSchreier.Data.baseList.toArray
        (allSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
          CFSG.ONSchreier.Data.baseList.toArray) =
      Array.ofFn (n := 29) fun i => (⟨Array.ofFn (n := Mf i.val) fun k => PTSf i.val k.val,
        Array.ofFn (n := 245520) fun z => POSf i.val z.val,
        Array.ofFn (n := Mf i.val) fun k => PARf i.val k.val,
        Array.ofFn (n := Mf i.val) fun k => LABf i.val k.val⟩ : CLevel) :=
  cLevels_eq pt0All pt1All pt2All pos0All pos1All pos2All posTAll qon_SA

theorem steps_get' {i j x : Nat} (hi : i < 29) (hj : j < Nat.mul 2 (len i)) (hx : x < 245520) :
    (((allSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
      CFSG.ONSchreier.Data.baseList.toArray)[i]!)[j]!)[x]! = stepF i j x := by
  rw [qon_SA]
  exact steps_get hi hj hx

theorem steps_size' {i : Nat} (hi : i < 29) :
    ((allSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
      CFSG.ONSchreier.Data.baseList.toArray)[i]!).size = Nat.mul 2 (len i) := by
  rw [qon_SA]
  exact steps_size hi

theorem invSteps_get' {i j x : Nat} (hi : i < 29) (hj : j < Nat.mul 2 (len i)) (hx : x < 245520) :
    (((allInvSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
      CFSG.ONSchreier.Data.baseList.toArray)[i]!)[j]!)[x]! = invF i j x := by
  rw [qon_SA]
  exact invSteps_get hi hj hx

theorem invSteps_size' {i : Nat} (hi : i < 29) :
    ((allInvSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
      CFSG.ONSchreier.Data.baseList.toArray)[i]!).size = Nat.mul 2 (len i) := by
  rw [qon_SA]
  exact invSteps_size hi

end CertificateChecks.KernelSpor.ON

end
