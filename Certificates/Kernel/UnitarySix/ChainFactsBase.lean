
module

public import Certificates.Kernel.UnitarySix.KQFactsBase
public import Certificates.Kernel.UnitarySix.ASTQ
public import Certificates.Kernel.UnitarySix.PQ
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem CertificateChecks.KernelU6.order_of_sizes {Q : RawSchreierDatum 693} {S : Array (Array Nat)}
    {base : Array Nat} {sizes : List Nat} (hb : Q.baseCount = sizes.length)
    (hl : (rawLevels 693 S base).size = sizes.length)
    (hv : ∀ i : Fin Q.baseCount, Q.orbitSize i = ((rawLevels 693 S base)[(i : ℕ)]!).pts.size)
    (hs : rawOrbitSizes 693 S base = sizes) : Q.orderCertificate = sizes.prod := by
  have hsz : ∀ i (hi : i < sizes.length), ((rawLevels 693 S base)[i]!).pts.size = sizes[i] := by
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

namespace CertificateChecks.KernelU6.AQ

theorem perm : allN 12 (fun j => permOK 693 10 (mask 10) (693 * 10) (S j) (SI j)) = true := by
  quickRfl

noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 12) fun j => unpack 693 10 (S j.val)

theorem binds : Binds 693 10 S 12 3 BP SA aBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem kBinds : bindsK U.LT aWN S = true := by quickRfl

theorem raw : rawChainOK 693 (SA.extract 0 9) SA aBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 12 aDer) 1 = true :=
  rawChainK_sound (NS := 11) (CH := 64) binds head hl (by norm_num) hs

end CertificateChecks.KernelU6.AQ

namespace CertificateChecks.KernelU6.SQ

theorem perm : allN 15 (fun j => permOK 693 10 (mask 10) (693 * 10) (S j) (SI j)) = true := by
  quickRfl

noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 15) fun j => unpack 693 10 (S j.val)

theorem binds : Binds 693 10 S 15 3 BP SA aBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem kBinds : bindsK U.LT (aWN ++ tWN) S = true := by quickRfl

theorem raw : rawChainOK 693 (SA.extract 0 13) SA aBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 13 15 sDer) 1 = true :=
  rawChainK_sound (NS := 11) (CH := 64) binds head hl (by norm_num) hs

end CertificateChecks.KernelU6.SQ

namespace CertificateChecks.KernelU6.TQ

theorem perm : allN 5 (fun j => permOK 693 10 (mask 10) (693 * 10) (S j) (SI j)) = true := by
  quickRfl

noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 5) fun j => unpack 693 10 (S j.val)

theorem binds : Binds 693 10 S 5 2 BP SA tBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem kBinds : bindsK U.LT tWN S = true := by quickRfl

theorem raw : rawChainOK 693 (SA.extract 0 4) SA tBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 5 tDer) 1 = true :=
  rawChainK_sound (NS := 11) (CH := 64) binds head hl (by norm_num) hs

end CertificateChecks.KernelU6.TQ

namespace CertificateChecks.KernelU6.PQ

theorem perm : allN 19 (fun j => permOK 693 10 (mask 10) (693 * 10) (S j) (SI j)) = true := by
  quickRfl

noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 19) fun j => unpack 693 10 (S j.val)

theorem binds : Binds 693 10 S 19 4 BP SA pBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem kBinds : bindsK U.LT (aWN ++ kWN) S = true := by quickRfl

theorem raw : rawChainOK 693 (SA.extract 0 12) SA pBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 12 19 pDer) 1 = true :=
  rawChainK_sound (NS := 11) (CH := 64) binds head hl (by norm_num) hs

end CertificateChecks.KernelU6.PQ

end
