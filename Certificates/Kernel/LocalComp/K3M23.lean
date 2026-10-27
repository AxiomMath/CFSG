module

public import Certificates.Kernel.LocalComp.K3M23Data
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#lc_blocks CertificateChecks.KernelLC.K3.M23.BS CertificateChecks.KernelLC.K3.M23.fS 1588 869
#lc_blocks CertificateChecks.KernelLC.K3.M23.BF CertificateChecks.KernelLC.K3.M23.fF 38 38
#lc_blocks CertificateChecks.KernelLC.K3.M23.BE CertificateChecks.KernelLC.K3.M23.fE 9 9
#lc_blocks CertificateChecks.KernelLC.K3.M23.BC CertificateChecks.KernelLC.K3.M23.fC 4 4
#lc_blocks CertificateChecks.KernelLC.K3.M23.BM CertificateChecks.KernelLC.K3.M23.fM 9 9
#lc_blocks CertificateChecks.KernelLC.K3.M23.BW CertificateChecks.KernelLC.K3.M23.fW 4 4

namespace CertificateChecks.KernelLC.K3.M23

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK M23T.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem prog_eq : m23K3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg m23K3Prog = _
  rw [M23T.eq]
  exact progK_sound kProg (cover_of_blocks (B := 869) (nb := 2) (by omega) (by decide) BS.all)

theorem gens_eq : ∀ i < K.g, m23K3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  interval_cases i <;> decide +kernel

theorem check_ok : check m23K3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    (cover_of_blocks (B := 869) (nb := 2) (by omega) (by decide) BS.all)
    (cover_of_blocks (B := 38) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 9) (nb := 1) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 4) (nb := 1) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 9) (nb := 1) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 4) (nb := 1) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.M23

end
