module

public import Certificates.Data.CFSGNative.MonsterAxis.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelKDense

open CFSG.Monster.AxisCount.Native CFSG.Monster.B.Rep4371.Native

theorem pairTab_size_ok : (pairTab.size == 276) = true := by quickRfl

theorem pairTab_ok : (List.range 276).all (fun tp =>
    pairTab[tp]!.1 < pairTab[tp]!.2 && pairTab[tp]!.2 < 24 &&
      pairIdx pairTab[tp]!.1 pairTab[tp]!.2 == tp) = true := by quickRfl

theorem aIdx_ok : (List.range 24).all (fun i => (List.range 24).all fun j =>
    aIdx i j < 300 && aPos (aIdx i j) == (min i j, max i j)) = true := by quickRfl

theorem octTab_size_ok : (octTab.size == 759) = true := by quickRfl

theorem evenTab_size_ok : (evenTab.size == 64) = true := by quickRfl

theorem evenTab_ok :
    (List.range 64).all (fun q => evenTab[q]! < 128 && popcN 8 evenTab[q]! % 2 == 0) = true := by
  quickRfl

theorem octTab_spec {o : Nat} (ho : o < 759) :
    octTab[o]! < 4096 ∧ popcN 24 (wordN octTab[o]!) = 8 := by
  have hs : (octTab ()).size = 759 := by simpa using octTab_size_ok
  have hmem : octTab[o]! ∈ octTab () := by
    rw [getElem!_pos (octTab ()) o (by rw [hs]; exact ho)]
    exact Array.getElem_mem _
  unfold octTab at hmem
  rw [List.mem_toArray, List.mem_filter, List.mem_range, beq_iff_eq] at hmem
  exact hmem

theorem octTab_popcN (o : Nat) (ho : o < 759) : popcN 24 (wordN octTab[o]!) = 8 :=
  (octTab_spec ho).2

theorem tabCheck_ok : tabCheck () = true := by
  simp only [tabCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨pairTab_size_ok, pairTab_ok⟩, aIdx_ok⟩, octTab_size_ok⟩, ?_⟩, evenTab_size_ok⟩,
    evenTab_ok⟩
  refine List.all_eq_true.2 fun o ho => ?_
  have h := octTab_spec (List.mem_range.1 ho)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact h

end CertificateChecks.KernelKDense

end
