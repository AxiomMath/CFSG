module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.LocalComp.K3Co3EP0
public import Certificates.Kernel.LocalComp.K3Co3EP1
public import Certificates.Kernel.LocalComp.K3Co3EP2
public import Certificates.Kernel.LocalComp.K3Co3EP3
public import Certificates.Kernel.LocalComp.K3Co3EP4
public import Certificates.Kernel.LocalComp.K3Co3CP0
public import Certificates.Kernel.LocalComp.K3Co3CP1
public import Certificates.Kernel.LocalComp.K3Co3MP0
public import Certificates.Kernel.LocalComp.K3Co3MP1
public import Certificates.Kernel.LocalComp.BlockJoin
public import Certificates.Kernel.Sporadic.Co3.C
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BS CertificateChecks.KernelLC.K3.Co3.fS 2193 72
#lc_blocks CertificateChecks.KernelLC.K3.Co3.BF CertificateChecks.KernelLC.K3.Co3.fF 84 84
#lc_blocks CertificateChecks.KernelLC.K3.Co3.BW CertificateChecks.KernelLC.K3.Co3.fW 29 5

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK Co3T.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem aE : ∀ t < 2187, fE t = true := by
  have h0 : ∀ t < 0, fE t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 480) h0 cE0
  have h2 := cover_append (a := 480) (b := 480) h1 cE1
  have h3 := cover_append (a := 960) (b := 480) h2 cE2
  have h4 := cover_append (a := 1440) (b := 480) h3 cE3
  have h5 := cover_append (a := 1920) (b := 267) h4 cE4
  exact h5

theorem aC : ∀ t < 445, fC t = true := by
  have h0 : ∀ t < 0, fC t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 420) h0 cC0
  have h2 := cover_append (a := 420) (b := 25) h1 cC1
  exact h2

theorem aM : ∀ t < 2187, fM t = true := by
  have h0 : ∀ t < 0, fM t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 2160) h0 cM0
  have h2 := cover_append (a := 2160) (b := 27) h1 cM1
  exact h2

theorem prog_eq : co3K3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg co3K3Prog = _
  rw [Co3T.eq]
  exact progK_sound kProg (cover_of_blocks (B := 72) (nb := 31) (by omega) (by decide) BS.all)

theorem gens_eq : ∀ i < K.g, co3K3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have hF : ∀ j < 2, K.GP j = CertificateChecks.KernelSpor.Co3C.S j := by decide +kernel
  have hn : K.n = 276 := rfl
  have hw : K.w = 9 := rfl
  rw [tblOf, hF i hi, hn, hw, ← CertificateChecks.KernelSpor.Co3C.binds.2.2.2.2.1 i (by omega)]
  interval_cases i <;>
    simp only [co3K3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check co3K3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    (cover_of_blocks (B := 72) (nb := 31) (by omega) (by decide) BS.all)
    (cover_of_blocks (B := 84) (nb := 1) (by omega) (by decide) BF.all)
    aE
    aC
    aM
    (cover_of_blocks (B := 5) (nb := 6) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.Co3

end
