module

public import Certificates.Kernel.LocalComp.K3M24Data
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#lc_blocks CertificateChecks.KernelLC.K3.M24.BS CertificateChecks.KernelLC.K3.M24.fS 1842 833
#lc_blocks CertificateChecks.KernelLC.K3.M24.BF CertificateChecks.KernelLC.K3.M24.fF 41 41
#lc_blocks CertificateChecks.KernelLC.K3.M24.BE CertificateChecks.KernelLC.K3.M24.fE 27 27
#lc_blocks CertificateChecks.KernelLC.K3.M24.BC CertificateChecks.KernelLC.K3.M24.fC 13 13
#lc_blocks CertificateChecks.KernelLC.K3.M24.BM CertificateChecks.KernelLC.K3.M24.fM 27 27
#lc_blocks CertificateChecks.KernelLC.K3.M24.BW CertificateChecks.KernelLC.K3.M24.fW 5 5

namespace CertificateChecks.KernelLC.K3.M24

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK M24T.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem prog_eq : m24K3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg m24K3Prog = _
  rw [M24T.eq]
  exact progK_sound kProg (cover_of_blocks (B := 833) (nb := 3) (by omega) (by decide) BS.all)

theorem gens_eq : ∀ i < K.g, m24K3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  interval_cases i <;> decide +kernel

theorem check_ok : check m24K3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    (cover_of_blocks (B := 833) (nb := 3) (by omega) (by decide) BS.all)
    (cover_of_blocks (B := 41) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 27) (nb := 1) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 13) (nb := 1) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 27) (nb := 1) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 5) (nb := 1) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.M24

end
