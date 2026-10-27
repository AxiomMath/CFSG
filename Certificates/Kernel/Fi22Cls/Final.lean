
module

public import Certificates.Kernel.Fi22Cls.FinalBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
public import Certificates.Kernel.Fi22S0.Facts
public import Certificates.Kernel.Fi22Cls.Conj
public import Certificates.Kernel.Fi22Cls.Cent
public import Certificates.Kernel.Fi22Cls.LabKill
public import Certificates.Kernel.Fi22Cls.LabKillB
public import Certificates.Kernel.Fi22Cls.LabEq
public import Certificates.Kernel.Fi22Cls.ParseEq
public import Certificates.Kernel.Fi22.Letters
public import Certificates.Kernel.Fi22Core.OrbData
public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.E27.Fi22S0
public import CFSG.Certificates.Kernel.Fi22Cls.LabSound
public import CFSG.Certificates.Kernel.Fi22Cls.Sound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase1
import all CFSG.Certificates.Kernel.Fi22S0.Sound
public import Certificates.Certificate131101Base

public section

namespace CertificateChecks.KernelFi22Cls

open CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KD.Fi22S0 CFSG.KD.Fi22Cls CFSG.Sporadic.Fi22.S0
  CFSG.HardMathSupport.Foote.E27 CertificateChecks.KernelFi22S0

open CFSG.Sporadic.Fi22 (J orb gs)
open CFSG.Sporadic.Th (Rep allIn_eq_true)
open CFSG.Sporadic.Th.Native (Table compT)
open CFSG.Sporadic.Fi22.Native (chainLetters orbL orbitData)
open CFSG.KS.Fi22ClsParse (wlist)
open CFSG.Perm (pairG)
open CFSG.HardMathSupport.Foote.E27.Fi22S0 (gJ)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native (classifyOK classifyCore eqT
  lettersT eltT genT globRep labRep labCls labOf witOf conjW nR)

theorem labelClause :
    (List.range nR).all (fun l =>
      decide ((labCls ())[l]! < 4) &&
        (conjW ())[l]!.all (fun z => decide (z < (chainLetters orb).size)) &&
        eqT (compT 3510
            (lettersT (chainLetters orb) (conjW ())[l]!)
            (eltT (par ()) (genT orb) (labRep ())[l]!))
          (compT 3510 (eltT (par ()) (genT orb) globRep[(labCls ())[l]!]!)
            (lettersT (chainLetters orb) (conjW ())[l]!))) = true := by
  rw [List.all_eq_true]
  intro l hl
  have hl' : l < 126 := List.mem_range.1 hl
  obtain ⟨hr, hk, hse, hwd, he⟩ := conjAll l hl'
  rw [labCls_eq, labRep_eq, getOfFn hl', getOfFn hl', conjW_get hl', glob_eq _ hk]
  have hw : ∀ z ∈ wlist wo wd l, z < (chainLetters orb).size := by
    intro z hz
    unfold wlist at hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    rw [List.mem_range'_1] at ht
    rw [letters_size]
    exact hwd t ht.1 (by omega)
  have hc := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.rep_lettersT _ hw
  have hw' : ((wlist wo wd l).map (pairG gs)).prod = wordJ (pairG gs) wd (wo l) (wo (l + 1) - wo l) := by
    unfold wlist wordJ
    rw [List.map_map]
    rfl
  rw [hw'] at hc
  have hglob := glob_lt _ hk
  have e := eqT_of_rep
    (hc.compT (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.rep_eltT _ hr))
    ((CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.rep_eltT _ hglob).compT hc) he
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨hk, hw⟩, e⟩

theorem classifyOK_true : classifyOK (orbitData ()) = true := by
  have hr0 : krep 0 < 19683 := by
    have h : repC pp pj lt krep kcw 19683 81 0 = true :=
      blk_all (b := 14) (m := 9) (by norm_num) repAll 0 (by norm_num)
    unfold repC at h
    rw [sB_eq] at h
    simp only [bRec_and, Bool.and_eq_true] at h
    have h1 := h.1
    rw [Nat.blt_eq] at h1
    exact h1
  have hb := labs_of tabDataK par_eq L_eq (blk_all (by norm_num) killAll) hr0
    (blk_all (by norm_num) ch13620labAll) (fun r hr => (conjAll r hr).1) labRep_eq labOf_eq
    witOf_eq
  have hc := labelClause
  have hd : (List.range 4).all (fun k => globRep[k]! != 0 &&
      tabMul (par ()) (L ()) globRep[k]! (tabMul (par ()) (L ()) globRep[k]! globRep[k]!) == 0 &&
      decide (2187 ≤ tabComm (par ()) (L ()) nS globRep[k]!)) = true := by
    rw [List.all_eq_true]
    intro k hk
    have hk' : k < 4 := List.mem_range.1 hk
    obtain ⟨h1, h2, h3⟩ := repFacts k hk'
    rw [glob_eq k hk']
    simp [h1, h2, h3]
  have he : tabComm (par ()) (L ()) nS globRep[0]! = 2187 := by
    rw [glob_eq 0 (by norm_num)]
    exact comm0
  change classifyCore (par ()) (L ()) (genT orb) (chainLetters orb)
    (labRep ()) (labCls ()) (labOf ()) (witOf ()) (conjW ()) = true
  unfold classifyCore
  rw [hb.2.2, hc, hd, labRep_eq, labCls_eq, conjW_eq, hb.1, hb.2.1, he]
  simp [nR]

end CertificateChecks.KernelFi22Cls

end
