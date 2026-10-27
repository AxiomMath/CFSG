module

public import Certificates.Kernel.LocalComp.K3HSData
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.LocalComp.K3HSP0
public import Certificates.Kernel.LocalComp.K3HSP1
public import Certificates.Kernel.LocalComp.K3HSP2
public import Certificates.Kernel.LocalComp.K3HSP3
public import Certificates.Kernel.LocalComp.K3HSP4
public import Certificates.Kernel.LocalComp.BlockJoin
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
meta import CFSG.Sporadic.Schreier.PairHSCertInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.HSHX CFSG.Sporadic.Schreier.hsStrongHex
#kmisc_hexflat CertificateChecks.KernelLC.K3.HSHX CFSG.Sporadic.Schreier.hsStrongHex 4 3850 12 2
#lc_blocks CertificateChecks.KernelLC.K3.HS.BF CertificateChecks.KernelLC.K3.HS.fF 29 29
#lc_blocks CertificateChecks.KernelLC.K3.HS.BE CertificateChecks.KernelLC.K3.HS.fE 9 1
#lc_blocks CertificateChecks.KernelLC.K3.HS.BC CertificateChecks.KernelLC.K3.HS.fC 4 1
#lc_blocks CertificateChecks.KernelLC.K3.HS.BM CertificateChecks.KernelLC.K3.HS.fM 9 2
#lc_blocks CertificateChecks.KernelLC.K3.HS.BW CertificateChecks.KernelLC.K3.HS.fW 4 1

namespace CertificateChecks.KernelLC.K3.HS

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK HST.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem aS : ∀ t < 1499, fS t = true := by
  have h0 : ∀ t < 0, fS t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 300) h0 cS0
  have h2 := cover_append (a := 300) (b := 300) h1 cS1
  have h3 := cover_append (a := 600) (b := 300) h2 cS2
  have h4 := cover_append (a := 900) (b := 300) h3 cS3
  have h5 := cover_append (a := 1200) (b := 299) h4 cS4
  exact h5

theorem prog_eq : hsK3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg hsK3Prog = _
  rw [HST.eq]
  exact progK_sound kProg aS

theorem gens_eq : ∀ i < K.g, hsK3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have hb : ∀ j < 2, CFSG.Sporadic.Schreier.hsStrongArrs[j]! =
      CFSG.KS.Raw.unpack 3850 12 (HSHX.F j) := fun j hj => by
    unfold CFSG.Sporadic.Schreier.hsStrongArrs
    rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, HSHX.eq]
    exact CFSG.KC.Misc.HexFlat.hexTable_sound HSHX.all j hj
  have hF : ∀ j < 2, K.GP j = HSHX.F j := by decide +kernel
  have hn : K.n = 3850 := rfl
  have hw : K.w = 12 := rfl
  rw [tblOf, hF i hi, hn, hw, ← hb i hi]
  interval_cases i <;>
    simp only [hsK3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check hsK3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    aS
    (cover_of_blocks (B := 29) (nb := 1) (by omega) (by decide) BF.all)
    (cover_of_blocks (B := 1) (nb := 9) (by omega) (by decide) BE.all)
    (cover_of_blocks (B := 1) (nb := 4) (by omega) (by decide) BC.all)
    (cover_of_blocks (B := 2) (nb := 5) (by omega) (by decide) BM.all)
    (cover_of_blocks (B := 1) (nb := 4) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.HS

end
