module

public import Certificates.Kernel.LocalComp.K3J2Data
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.J2HX CFSG.Sporadic.Schreier.PairNative.j2StrongHex
#kmisc_hexflat CertificateChecks.KernelLC.K3.J2HX CFSG.Sporadic.Schreier.PairNative.j2StrongHex 4 315 9 2
#lc_blocks CertificateChecks.KernelLC.K3.J2.BS CertificateChecks.KernelLC.K3.J2.fS 1782 63
#lc_blocks CertificateChecks.KernelLC.K3.J2.BF CertificateChecks.KernelLC.K3.J2.fF 43 43
#lc_blocks CertificateChecks.KernelLC.K3.J2.BE CertificateChecks.KernelLC.K3.J2.fE 27 12
#lc_blocks CertificateChecks.KernelLC.K3.J2.BC CertificateChecks.KernelLC.K3.J2.fC 13 10
#lc_blocks CertificateChecks.KernelLC.K3.J2.BM CertificateChecks.KernelLC.K3.J2.fM 27 27
#lc_blocks CertificateChecks.KernelLC.K3.J2.BW CertificateChecks.KernelLC.K3.J2.fW 5 4

namespace CertificateChecks.KernelLC.K3.J2

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK J2T.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem prog_eq : j2K3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg j2K3Prog = _
  rw [J2T.eq]
  exact progK_sound kProg (cover_of_blocks (B := 63) (nb := 29) (by omega) (by decide) BS.all)

theorem gens_eq : ∀ i < K.g, j2K3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have hb : ∀ j < 2, CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[j]! =
      CFSG.KS.Raw.unpack 315 9 (J2HX.F j) := fun j hj => by
    unfold CFSG.Sporadic.Schreier.PairNative.j2StrongArrs
    rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn,
      CFSG.Sporadic.Schreier.PairNative.j2Strong, J2HX.eq]
    exact CFSG.KC.Misc.HexFlat.hexTable_sound J2HX.all j hj
  have hF : ∀ j < 2, K.GP j = J2HX.F j := by decide +kernel
  have hn : K.n = 315 := rfl
  have hw : K.w = 9 := rfl
  rw [tblOf, hF i hi, hn, hw, ← hb i hi]
  interval_cases i <;>
    simp only [j2K3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check j2K3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    (cover_of_blocks (B := 63) (nb := 29) (by omega) (by decide) BS.all)
    (cover_of_blocks (B := 43) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 12) (nb := 3) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 10) (nb := 2) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 27) (nb := 1) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 4) (nb := 2) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.J2

end
