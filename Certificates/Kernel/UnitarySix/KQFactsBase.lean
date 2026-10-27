
module

public import Certificates.Kernel.UnitarySix.KQ
public import Certificates.Kernel.UnitarySix.Struct3010Base
public import CFSG.Certificates.Kernel.U6Chain
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.KQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem perm : allN 7 (fun j => permOK 693 10 (mask 10) (693 * 10) (S j) (SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) := Array.ofFn (n := 7) fun j => unpack 693 10 (S j.val)

theorem binds : Binds 693 10 S 7 3 BP SA kBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem kBinds : bindsK U.LT kWN S = true := by quickRfl

theorem raw : rawChainOK 693 (SA.extract 0 3) SA kBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 7 kDer) 1 = true :=
  rawChainK_sound (NS := 11) (CH := 64) binds head hl (by norm_num) hs

theorem getD_toList_map {α : Type} [Inhabited α] (a : Array α) (f : α → Nat) {i : Nat}
    (hi : i < a.size) : (a.toList.map f).getD i 0 = f a[i]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, getElem!_pos a i hi,
    getElem?_pos a i hi]
  rfl

theorem size_of_orbitSizes {n : Nat} {S : Array (Array Nat)} {base : Array Nat} {L : List Nat}
    (hs : rawOrbitSizes n S base = L) {i : Nat} (hi : i < (rawLevels n S base).size) :
    ((rawLevels n S base)[i]!).pts.size = L.getD i 0 := by
  have h : (rawOrbitSizes n S base).getD i 0 = L.getD i 0 := by rw [hs]
  rw [rawOrbitSizes, getD_toList_map _ _ hi] at h
  exact h

end CertificateChecks.KernelU6.KQ

end
