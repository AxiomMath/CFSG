module

public import Certificates.Kernel.Misc.KGroups.U33Chain
public import Certificates.Kernel.Misc.KGroups.M11Valid
public import CFSG.GH74.KGroups.U33Inputs
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.GH74.KGroups.U33 CertificateChecks.KernelMisc.U33K

namespace CertificateChecks.KernelMisc.U33PC

theorem perm : allN 6 (fun j => permOK 28 5 (mask 5) (28 * 5) (S j) (SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) := Array.ofFn (n := 6) fun j => unpack 28 5 (S j.val)

theorem binds : Binds 28 5 S 6 4 BP SA pBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem raw : rawChainOK 28 (SA.extract 0 2) SA pBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 [[1, -2], [-2, 3, 1, 2, 1], [4, 3, 3], [-5, -5]])
    1 = true :=
  rawChainK_sound (NS := 1) (CH := 28) binds head hl (by norm_num) hs

theorem rep0 : CFSG.Monster.B.Co2.Rep 28 (unpack 28 5 (S 0)) pa := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep1 : CFSG.Monster.B.Co2.Rep 28 (unpack 28 5 (S 1)) pb := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem arrays : ChainArrays QP (SA.extract 0 2) SA pBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6
      [[1, -2], [-2, 3, 1, 2, 1], [4, 3, 3], [-5, -5]]) := by
  refine certificate_chainArrays (gens := [pa, pb]) _ _ _ _ raw
    (by simp [SA]) (by simp [SA]) (fun j hj => ?_) rfl (fun i => ?_)
  · have e : ∀ j < 2, (SA.extract 0 2)[j]! = unpack 28 5 (S j) := by
      intro j hj
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    have hj2 : j < 2 := hj
    rw [e j hj2]
    interval_cases j
    · exact rep0
    · exact rep1
  · fin_cases i <;> rfl

theorem valid : ValidSchreier QP :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : QP.orderCertificate = 6048 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 4).map (fun i => rcnt (LR i)) = [28, 27, 2, 4] := by decide
  rw [e] at hs
  exact CertificateChecks.KernelMisc.M11C.order_of_sizes rfl (by simp [rawLevels, pBase])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelMisc.U33PC

namespace CertificateChecks.KernelMisc.U33AC

theorem perm : allN 8 (fun j => permOK 28 5 (mask 5) (28 * 5) (S j) (SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) := Array.ofFn (n := 8) fun j => unpack 28 5 (S j.val)

theorem binds : Binds 28 5 S 8 4 BP SA aBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem raw : rawChainOK 28 (SA.extract 0 3) SA aBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 8
      [[1, -2], [3, 3, 1], [-4, -4, 5, 4], [-4, 6, -1, 5, 3, 2], [7, 4, -1, 2, -6, 2]]) 1 = true :=
  rawChainK_sound (NS := 1) (CH := 28) binds head hl (by norm_num) hs

theorem rep0 : CFSG.Monster.B.Co2.Rep 28 (unpack 28 5 (S 0)) pa := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep1 : CFSG.Monster.B.Co2.Rep 28 (unpack 28 5 (S 1)) pb := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep2 : CFSG.Monster.B.Co2.Rep 28 (unpack 28 5 (S 2)) sg0 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem arrays : ChainArrays QA (SA.extract 0 3) SA aBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 8
      [[1, -2], [3, 3, 1], [-4, -4, 5, 4], [-4, 6, -1, 5, 3, 2], [7, 4, -1, 2, -6, 2]]) := by
  refine certificate_chainArrays (gens := [pa, pb, sg0]) _ _ _ _ raw
    (by simp [SA]) (by simp [SA]) (fun j hj => ?_) rfl (fun i => ?_)
  · have e : ∀ j < 3, (SA.extract 0 3)[j]! = unpack 28 5 (S j) := by
      intro j hj
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    have hj3 : j < 3 := hj
    rw [e j hj3]
    interval_cases j
    · exact rep0
    · exact rep1
    · exact rep2
  · fin_cases i <;> rfl

theorem valid : ValidSchreier QA :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : QA.orderCertificate = 12096 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 4).map (fun i => rcnt (LR i)) = [28, 27, 8, 2] := by decide
  rw [e] at hs
  exact CertificateChecks.KernelMisc.M11C.order_of_sizes rfl (by simp [rawLevels, aBase])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelMisc.U33AC

end
