module

public import Certificates.Kernel.LocalComp.K3McLData
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
meta import CFSG.Sporadic.Schreier.PairMcLCertInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.McLHX CFSG.Sporadic.Schreier.mclStrongHex
#kmisc_hexflat CertificateChecks.KernelLC.K3.McLHX CFSG.Sporadic.Schreier.mclStrongHex 4 275 9 2
#lc_blocks CertificateChecks.KernelLC.K3.McL.BS CertificateChecks.KernelLC.K3.McL.fS 2163 72
#lc_blocks CertificateChecks.KernelLC.K3.McL.BF CertificateChecks.KernelLC.K3.McL.fF 81 81
#lc_blocks CertificateChecks.KernelLC.K3.McL.BE CertificateChecks.KernelLC.K3.McL.fE 729 10
#lc_blocks CertificateChecks.KernelLC.K3.McL.BC CertificateChecks.KernelLC.K3.McL.fC 148 9
#lc_blocks CertificateChecks.KernelLC.K3.McL.BM CertificateChecks.KernelLC.K3.McL.fM 729 36
#lc_blocks CertificateChecks.KernelLC.K3.McL.BW CertificateChecks.KernelLC.K3.McL.fW 20 5

namespace CertificateChecks.KernelLC.K3.McL

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK McLT.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem prog_eq : mclK3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg mclK3Prog = _
  rw [McLT.eq]
  exact progK_sound kProg (cover_of_blocks (B := 72) (nb := 31) (by omega) (by decide) BS.all)

theorem gens_eq : ∀ i < K.g, mclK3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have hb : ∀ j < 2, CFSG.Sporadic.Schreier.mclStrongArrs[j]! =
      CFSG.KS.Raw.unpack 275 9 (McLHX.F j) := fun j hj => by
    unfold CFSG.Sporadic.Schreier.mclStrongArrs
    rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, McLHX.eq]
    exact CFSG.KC.Misc.HexFlat.hexTable_sound McLHX.all j hj
  have hF : ∀ j < 2, K.GP j = McLHX.F j := by decide +kernel
  have hn : K.n = 275 := rfl
  have hw : K.w = 9 := rfl
  rw [tblOf, hF i hi, hn, hw, ← hb i hi]
  interval_cases i <;>
    simp only [mclK3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check mclK3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    (cover_of_blocks (B := 72) (nb := 31) (by omega) (by decide) BS.all)
    (cover_of_blocks (B := 81) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 10) (nb := 73) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 9) (nb := 17) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 36) (nb := 21) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 5) (nb := 4) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.McL

end
