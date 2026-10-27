module

public import Certificates.Kernel.LocalComp.K3HeData
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.LocalComp.K3HeP0
public import Certificates.Kernel.LocalComp.K3HeP1
public import Certificates.Kernel.LocalComp.K3HeP2
public import Certificates.Kernel.LocalComp.K3HeP3
public import Certificates.Kernel.LocalComp.K3HeP4
public import Certificates.Kernel.LocalComp.K3HeP5
public import Certificates.Kernel.LocalComp.K3HeP6
public import Certificates.Kernel.LocalComp.K3HeP7
public import Certificates.Kernel.LocalComp.K3HeP8
public import Certificates.Kernel.LocalComp.K3HeP9
public import Certificates.Kernel.LocalComp.K3HeP10
public import Certificates.Kernel.LocalComp.K3HeP11
public import Certificates.Kernel.LocalComp.K3HeP12
public import Certificates.Kernel.LocalComp.K3HeP13
public import Certificates.Kernel.LocalComp.K3HeP14
public import Certificates.Kernel.LocalComp.K3HeP15
public import Certificates.Kernel.LocalComp.BlockJoin
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
meta import CFSG.Sporadic.HeldB.CertPChainData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.HeHX CFSG.Sporadic.HeldB.heGenHex
#kmisc_hexflat CertificateChecks.KernelLC.K3.HeHX CFSG.Sporadic.HeldB.heGenHex 4 8330 14 2
#lc_blocks CertificateChecks.KernelLC.K3.He.BF CertificateChecks.KernelLC.K3.He.fF 42 42
#lc_blocks CertificateChecks.KernelLC.K3.He.BE CertificateChecks.KernelLC.K3.He.fE 27 1
#lc_blocks CertificateChecks.KernelLC.K3.He.BC CertificateChecks.KernelLC.K3.He.fC 13 1
#lc_blocks CertificateChecks.KernelLC.K3.He.BM CertificateChecks.KernelLC.K3.He.fM 27 1
#lc_blocks CertificateChecks.KernelLC.K3.He.BW CertificateChecks.KernelLC.K3.He.fW 5 1

namespace CertificateChecks.KernelLC.K3.He

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK HeT.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem aS : ∀ t < 1905, fS t = true := by
  have h0 : ∀ t < 0, fS t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 120) h0 cS0
  have h2 := cover_append (a := 120) (b := 120) h1 cS1
  have h3 := cover_append (a := 240) (b := 120) h2 cS2
  have h4 := cover_append (a := 360) (b := 120) h3 cS3
  have h5 := cover_append (a := 480) (b := 120) h4 cS4
  have h6 := cover_append (a := 600) (b := 120) h5 cS5
  have h7 := cover_append (a := 720) (b := 120) h6 cS6
  have h8 := cover_append (a := 840) (b := 120) h7 cS7
  have h9 := cover_append (a := 960) (b := 120) h8 cS8
  have h10 := cover_append (a := 1080) (b := 120) h9 cS9
  have h11 := cover_append (a := 1200) (b := 120) h10 cS10
  have h12 := cover_append (a := 1320) (b := 120) h11 cS11
  have h13 := cover_append (a := 1440) (b := 120) h12 cS12
  have h14 := cover_append (a := 1560) (b := 120) h13 cS13
  have h15 := cover_append (a := 1680) (b := 120) h14 cS14
  have h16 := cover_append (a := 1800) (b := 105) h15 cS15
  exact h16

theorem prog_eq : heK3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg heK3Prog = _
  rw [HeT.eq]
  exact progK_sound kProg aS

theorem gens_eq : ∀ i < K.g, heK3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have hb : ∀ j < 2, CFSG.Sporadic.HeldB.heGen j = CFSG.KS.Raw.unpack 8330 14 (HeHX.F j) :=
    fun j hj => by
      rw [CFSG.Sporadic.HeldB.heGen, HeHX.eq]
      exact CFSG.KC.Misc.HexFlat.hexTable_sound HeHX.all j hj
  have hF : ∀ j < 2, K.GP j = HeHX.F j := by decide +kernel
  have hn : K.n = 8330 := rfl
  have hw : K.w = 14 := rfl
  rw [tblOf, hF i hi, hn, hw, ← hb i hi]
  interval_cases i <;>
    simp only [heK3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check heK3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    aS
    (cover_of_blocks (B := 42) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 1) (nb := 27) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 1) (nb := 13) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 1) (nb := 27) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 1) (nb := 5) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.He

end
