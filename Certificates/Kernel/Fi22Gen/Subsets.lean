module

public import CFSG.Certificates.Kernel.Fi22Gen.Prefix
public import Certificates.Kernel.Fi22Gen.Glue

public section

namespace CertificateChecks.KernelFi22Gen

open CFSG.KS.Fi22Gen CFSG.KD.Fi22Gen CFSG.Sporadic.Fi22
open scoped Pointwise


theorem card_Uset : Uset.card = 22 := by
  obtain ⟨-, huinc, hulast⟩ := ulK_spec (treeK_spec fg_tree_ok).1
  have hUeq : Uset = ptSet (gD UL) := Finset.ext fun y => by rw [mem_Uset, mem_ptSet]
  rw [hUeq]
  exact card_ptSet huinc hulast

theorem tuples_trans (k : Nat) (hk : k ≤ 3) :
    ∃ t : Fin k → Fin 3510, ∀ f : Fin k → Fin 3510, Function.Injective f →
      (∀ j, f j ∈ Uset) → ∃ x : J, x • Uset = Uset ∧ x • t = f := by
  have hul := (treeK_spec fg_tree_ok).1
  obtain ⟨-, huinc, hulast⟩ := ulK_spec hul
  obtain ⟨-, -, s1, s2⟩ := elts_of_checks hul fg_ord_ok fg_trace_ok gab gen_act sep5 Uset
    mem_Uset
  have hUlt : ∀ j < 22, gD UL j < 3510 := by
    intro j hj
    rcases Nat.lt_or_ge j 21 with h | h
    · exact (lt_of_inc huinc j 21 h (by omega)).trans hulast
    · rw [show j = 21 by omega]; exact hulast
  have htP : ∀ j < 22, (tP UL j).val = gD UL j := fun j hj => Nat.mod_eq_of_lt (hUlt j hj)
  have horb := orbit_prefix_ge_of_chainK hul fg_ord_ok fg_trace_ok fg_chain_ok gab gen_act
    (MulAction.stabilizer J Uset) (MulAction.mem_stabilizer_iff.2 s1)
    (MulAction.mem_stabilizer_iff.2 s2) k (by omega)
  have hprod : ∏ i ∈ Finset.range k, lvS i = Uset.card.descFactorial k := by
    rw [card_Uset]
    interval_cases k <;> simp only [Finset.prod_range_succ, Finset.prod_range_zero] <;> decide
  refine ⟨fun j : Fin k => tP UL j, fun f hf hfU => exists_smul_eq_of_orbit Uset _ ?_ ?_
    (hprod ▸ horb) f hf hfU⟩
  · intro i j e
    have e' := congrArg Fin.val e
    simp only at e'
    rw [htP _ (by omega), htP _ (by omega)] at e'
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd e' (lt_of_inc huinc i j h (by omega)).ne
    · exact absurd e' (lt_of_inc huinc j i h (by omega)).ne'
  · intro j
    rw [mem_Uset]
    exact ⟨j, by omega, (htP _ (by omega)).symm⟩

theorem subsets_trans (s s' : Finset (Fin 3510)) (hs : s ⊆ Uset) (hs' : s' ⊆ Uset)
    (hc : s.card = s'.card) (h3 : s.card ≤ 3) : ∃ x : J, x • Uset = Uset ∧ x • s = s' :=
  exists_smul_finset_of_tuples Uset tuples_trans s s' hs hs' hc h3

end CertificateChecks.KernelFi22Gen

end
