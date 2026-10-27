module

public import Certificates.Kernel.Misc.Sp4Cen.FactsT
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenFacts
public import Certificates.Kernel.Misc.Sp4Cen.FactsM

public section

namespace CertificateChecks.KernelMisc.Sp4Cen

open Matrix CFSG.KD.Sp4Cen CFSG.KC.Misc.GL4 CFSG.Quasithin.H13.MatNCert
open Certificates.GL4 (GL4 sg)
open Certificates.A5GL42 (Mat4 ofCode)
open Certificates.A5A7GL42 (Pset)
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen (sbGens4 w0c4 Sp4CenFacts)

theorem decN_s0 : decN 4 [8, 13, 6, 4] = ofCode S0 := by decide +kernel

theorem decN_s1 : decN 4 [13, 14, 7, 5] = ofCode S1 := by decide +kernel

theorem decN_w0c4 : decN 4 w0c4 = W0m := by decide +kernel

theorem valid_s0 : ValidN 4 [8, 13, 6, 4] := ⟨rfl, by decide⟩

theorem valid_s1 : ValidN 4 [13, 14, 7, 5] := ⟨rfl, by decide⟩

theorem genSub_eq : genSubN 4 sbGens4 = SB := by
  rw [genSubN, SB, sg]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Pset, sbGens4, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left]
  constructor
  · rintro (h | h)
    · left
      rw [← decN_s0, ← h, decN_colsN]
    · right
      rw [← decN_s1, ← h, decN_colsN]
  · rintro (h | h)
    · left
      rw [← h, ← decN_s0, colsN_decN valid_s0]
    · right
      rw [← h, ← decN_s1, colsN_decN valid_s1]

abbrev adjT (i : Fin 5) : Equiv.Perm (Fin 6) := Equiv.swap i.castSucc i.succ

theorem adjT_rel : (adjT 0 * adjT 1) ^ 3 = 1 ∧ (adjT 1 * adjT 2) ^ 3 = 1 ∧
    (adjT 2 * adjT 3) ^ 3 = 1 ∧ (adjT 3 * adjT 4) ^ 3 = 1 ∧ (adjT 0 * adjT 2) ^ 2 = 1 ∧
    (adjT 0 * adjT 3) ^ 2 = 1 ∧ (adjT 0 * adjT 4) ^ 2 = 1 ∧ (adjT 1 * adjT 3) ^ 2 = 1 ∧
    (adjT 1 * adjT 4) ^ 2 = 1 ∧ (adjT 2 * adjT 4) ^ 2 = 1 := by decide

theorem adjT01 : adjT 0 * adjT 1 = Equiv.swap 0 1 * Equiv.swap 1 2 := by decide

theorem range_conj (ψ : Equiv.Perm (Fin 6) →* GL4) (hψ : ψ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1) :
    ∃ c : GL4, ψ.range = SB.map (MulAut.conj c).toMonoidHom := by
  have hr : ∀ (i j : Fin 5) (n : ℕ), (adjT i * adjT j) ^ n = 1 →
      (ψ (adjT i) * ψ (adjT j)) ^ n = 1 := fun i j n h => by
    rw [← map_mul, ← map_pow, h, map_one]
  obtain ⟨e01, e12, e23, e34, f02, f03, f04, f13, f14, f24⟩ := adjT_rel
  have hsq : ∀ i, ψ (adjT i) * ψ (adjT i) = 1 := fun i => by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hne : ψ (adjT 0) * ψ (adjT 1) ≠ 1 := by
    rw [← map_mul, adjT01]
    exact hψ
  obtain ⟨c, hc⟩ := tuple_conj (fun i => ψ (adjT i)) hsq (hr _ _ _ e01) (hr _ _ _ e12)
    (hr _ _ _ e23) (hr _ _ _ e34) (hr _ _ _ f02) (hr _ _ _ f03) (hr _ _ _ f04) (hr _ _ _ f13)
    (hr _ _ _ f14) (hr _ _ _ f24) hne
  refine ⟨c, ?_⟩
  have hcl : Subgroup.closure (Set.range adjT) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)
  rw [MonoidHom.range_eq_map, ← hcl, MonoidHom.map_closure, ← Set.range_comp]
  exact hc

theorem sp4CenFacts_kernel : Sp4CenFacts := by
  refine ⟨?_, fun g => ?_, fun Z hZ => ?_, fun ψ hψ => ?_, witness⟩
  · rw [genSub_eq]
    exact sb_exact.1
  · rw [genSub_eq, sb_eq_stab, decN_w0c4]
    exact Iff.rfl
  · rw [genSub_eq] at hZ ⊢
    exact sb_max hZ
  · rw [genSub_eq]
    exact range_conj ψ hψ

end CertificateChecks.KernelMisc.Sp4Cen
