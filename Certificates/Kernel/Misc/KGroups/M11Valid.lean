module

public import Certificates.Kernel.Misc.KGroups.M11Chain
public import CFSG.Certificates.Kernel.U6Chain
public import CFSG.GH74.KGroups.M11Inputs
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.M11C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.GH74.KGroups.M11 CFSG.Sporadic.Mathieu CertificateChecks.KernelMisc.M11K

theorem order_of_sizes {n : ℕ} {Q : RawSchreierDatum n} {S : Array (Array Nat)}
    {base : Array Nat} {sizes : List Nat} (hb : Q.baseCount = sizes.length)
    (hl : (rawLevels n S base).size = sizes.length)
    (hv : ∀ i : Fin Q.baseCount, Q.orbitSize i = ((rawLevels n S base)[(i : ℕ)]!).pts.size)
    (hs : rawOrbitSizes n S base = sizes) : Q.orderCertificate = sizes.prod := by
  have hsz : ∀ i (hi : i < sizes.length), ((rawLevels n S base)[i]!).pts.size = sizes[i] := by
    intro i hi
    rw [getElem!_pos _ i (by omega)]
    have := List.getElem_of_eq hs (i := i) (by simp [rawOrbitSizes, hl, hi])
    simpa [rawOrbitSizes] using this
  have hm : ∀ i : Fin Q.baseCount, Q.orbitSize i = sizes.getD i.val 0 := fun i => by
    have hi : i.val < sizes.length := hb ▸ i.2
    rw [hv, hsz _ hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  simp only [RawSchreierDatum.orderCertificate]
  rw [List.map_congr_left (fun i _ => hm i)]
  rw [show (fun i : Fin Q.baseCount => sizes.getD i.val 0) = (fun j => sizes.getD j 0) ∘ Fin.val
    from rfl, ← List.map_map, hb]
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

theorem perm : allN 8 (fun j => permOK 11 4 (mask 4) (11 * 4) (S j) (SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) := Array.ofFn (n := 8) fun j => unpack 11 4 (S j.val)

theorem binds : Binds 11 4 S 8 4 BP SA m11Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem der_eq : m11Der = words := by decide +kernel

theorem raw : rawChainOK 11 (SA.extract 0 2) SA m11Base
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 words) 1 = true := by
  rw [← der_eq]
  exact rawChainK_sound (NS := 1) (CH := 11) binds head hl (by norm_num) hs

theorem rep0 : CFSG.Monster.B.Co2.Rep 11 (unpack 11 4 (S 0)) m11gA := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep1 : CFSG.Monster.B.Co2.Rep 11 (unpack 11 4 (S 1)) m11gB := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem arrays : ChainArrays Q (SA.extract 0 2) SA m11Base
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 words) := by
  refine certificate_chainArrays (gens := [m11gA, m11gB]) _ _ _ _ raw
    (by simp [SA]) (by simp [SA, words]) (fun j hj => ?_) rfl (fun i => ?_)
  · have e : ∀ j < 2, (SA.extract 0 2)[j]! = unpack 11 4 (S j) := by
      intro j hj
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    have hj2 : j < 2 := hj
    rw [e j hj2]
    interval_cases j
    · exact rep0
    · exact rep1
  · fin_cases i <;> rfl

theorem valid : ValidSchreier Q :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : Q.orderCertificate = 7920 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 4).map (fun i => rcnt (LR i)) = [11, 10, 9, 8] := by decide
  rw [e] at hs
  exact order_of_sizes rfl (by simp [rawLevels, m11Base])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelMisc.M11C

end
