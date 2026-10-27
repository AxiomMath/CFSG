module

public import Certificates.Kernel.Misc.GL52.Chain
public import CFSG.Certificates.Kernel.U6Chain
public import CFSG.Literature.GL52ChainInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.GL52C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CertificateChecks.KernelMisc.GL52K

theorem perm : allN 14 (fun j => permOK 31 6 (mask 6) (31 * 6) (S j) (SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) := Array.ofFn (n := 14) fun j => unpack 31 6 (S j.val)

theorem binds : Binds 31 6 S 14 5 BP SA glBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem der_eq : glDer = glWords := by decide +kernel

theorem raw : rawChainOK 31 (SA.extract 0 2) SA glBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 14 glWords) 1 = true := by
  rw [← der_eq]
  exact rawChainK_sound (NS := 1) (CH := 31) binds head hl (by norm_num) hs

theorem rep0 : CFSG.Monster.B.Co2.Rep 31 (unpack 31 6 (S 0)) (tab (glPerm glA)) := by
  rw [tab_eq]
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep1 : CFSG.Monster.B.Co2.Rep 31 (unpack 31 6 (S 1)) (tab (glPerm glB)) := by
  rw [tab_eq]
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem arrays : ChainArrays glCert (SA.extract 0 2) SA glBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 14 glWords) := by
  refine certificate_chainArrays (gens := [tab (glPerm glA), tab (glPerm glB)]) _ _ _ _ raw
    (by simp [SA]) (by simp [SA, glWords]) (fun j hj => ?_) rfl (fun i => ?_)
  · have e : ∀ j < 2, (SA.extract 0 2)[j]! = unpack 31 6 (S j) := by
      intro j hj
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    have hj2 : j < 2 := hj
    rw [e j hj2]
    interval_cases j
    · exact rep0
    · exact rep1
  · fin_cases i <;> rfl

theorem valid : ValidSchreier glCert :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem orbitSizes : List.ofFn glCert.orbitSize = [31, 30, 28, 24, 16] := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 5).map (fun i => rcnt (LR i)) = [31, 30, 28, 24, 16] := by decide
  rw [e] at hs
  have hv := (validSchreier_of_chainOK arrays (by norm_num) raw).2
  have hl5 : (rawLevels 31 SA glBase).size = 5 := by simp [rawLevels, glBase]
  have hb : glCert.baseCount = 5 := rfl
  refine List.ext_getElem (by simp [hb]) fun i h1 h2 => ?_
  have hi : i < 5 := by simpa [hb] using h1
  rw [List.getElem_ofFn, hv ⟨i, by rw [hb]; exact hi⟩]
  change ((rawLevels 31 SA glBase)[i]!).pts.size = _
  rw [getElem!_pos _ i (by omega)]
  have := List.getElem_of_eq hs (i := i) (by simp [rawOrbitSizes, hl5, hi])
  simpa [rawOrbitSizes] using this

end CertificateChecks.KernelMisc.GL52C

end
