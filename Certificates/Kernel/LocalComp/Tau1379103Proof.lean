module

public import Certificates.Kernel.LocalComp.Tau1379103K
public import Certificates.Kernel.LocalComp.B0SuzProof
public import CFSG.Certificates.Kernel.Tau1379103KSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Tau1379103

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.B0SuzK CFSG.KC.BfsPin
open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.Suz2306 CertificateChecks.KernelLC

theorem tau_eq : tauArr () = unpack 1782 11 TAU := by
  have hS : bTriple.size = 3 ∧ ∀ j < 3, bTriple[j]! = unpack 1782 11 (triS j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · change bTriple[0]! = unpack 1782 11 B0
      simpa [bTriple] using b0Arr_eq
    · change bTriple[1]! = unpack 1782 11 B1
      simpa [bTriple] using b1Arr_eq
    · change bTriple[2]! = unpack 1782 11 V
      simpa [bTriple] using vArr_eq
  exact (wordEqK_sound hS tri_perms kWord).1

theorem tauCheck_true : tauCheck () = true := by
  have k := kTau
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨hc, hb⟩, hcm⟩ := k
  rw [tauCheck_eq]
  exact tauK_sound tau_eq B0Suz.t_eq (fun i hi => B0Suz.q_eq hi) B0Suz.kBase kQ0 hc B0Suz.mat_tabs
    (bfsK_canon SuzB0M.ok) (unpack_eq_of_bindArrK hb) hcm

end CertificateChecks.KernelLC.Tau1379103

end
