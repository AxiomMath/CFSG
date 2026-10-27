module

public import Certificates.Kernel.LocalComp.K3Gen
public import Certificates.Kernel.LocalComp.BlockGen
public import CFSG.Certificates.Kernel.K3Sound
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3MathieuData
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3MathieuData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.M22T CFSG.EvenSmallLie.Child3.SelK3.m22K3Prog
#lc_k3 CertificateChecks.KernelLC.K3.M22 CFSG.EvenSmallLie.Child3.SelK3.m22K3

namespace CertificateChecks.KernelLC.K3.M22

open CFSG.KC.K3 CFSG.KC.Co3Bfs

@[expose] noncomputable def fS (t : Nat) : Bool := K.stepK t
@[expose] noncomputable def fF (r : Nat) : Bool := K.finK r
@[expose] noncomputable def fE (k : Nat) : Bool := K.eK k
@[expose] noncomputable def fC (p : Nat) : Bool := K.cK p
@[expose] noncomputable def fM (k : Nat) : Bool := K.memK k
@[expose] noncomputable def fW (j : Nat) : Bool := K.witK j

end CertificateChecks.KernelLC.K3.M22

#lc_blocks CertificateChecks.KernelLC.K3.M22.BS CertificateChecks.KernelLC.K3.M22.fS 1531 128
#lc_blocks CertificateChecks.KernelLC.K3.M22.BF CertificateChecks.KernelLC.K3.M22.fF 36 36
#lc_blocks CertificateChecks.KernelLC.K3.M22.BE CertificateChecks.KernelLC.K3.M22.fE 9 9
#lc_blocks CertificateChecks.KernelLC.K3.M22.BC CertificateChecks.KernelLC.K3.M22.fC 4 4
#lc_blocks CertificateChecks.KernelLC.K3.M22.BM CertificateChecks.KernelLC.K3.M22.fM 9 9
#lc_blocks CertificateChecks.KernelLC.K3.M22.BW CertificateChecks.KernelLC.K3.M22.fW 4 4

namespace CertificateChecks.KernelLC.K3.M22

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK M22T.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem prog_eq : m22K3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg m22K3Prog = _
  rw [M22T.eq]
  exact progK_sound kProg (cover_of_blocks (B := 128) (nb := 12) (by omega) (by decide) BS.all)

theorem gens_eq : ∀ i < K.g, m22K3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  interval_cases i <;> decide +kernel

theorem check_m22 : check m22K3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    (cover_of_blocks (B := 128) (nb := 12) (by omega) (by decide) BS.all)
    (cover_of_blocks (B := 36) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 9) (nb := 1) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 4) (nb := 1) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 9) (nb := 1) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 4) (nb := 1) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.M22

end
