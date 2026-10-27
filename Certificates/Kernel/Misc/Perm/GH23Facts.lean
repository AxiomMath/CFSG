module

public import Certificates.Kernel.Misc.Perm.GH23K
public import CFSG.Certificates.Kernel.Misc.PermGH23Clos

public section

namespace CertificateChecks.KernelMisc.GH23

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23
  CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem members_valid : ∀ m < 41, (members.getD m ⟨[], .top⟩).gens.all validC = true := by
  decide +kernel

theorem q2_valid : q2gens.all validC = true := by decide +kernel

theorem nn_pos : ∀ m < 42, 0 < NN m := by decide +kernel

theorem nn40 : NN 40 = 20160 := by decide +kernel

theorem all_of_allR {N : ℕ} {f : ℕ → Bool} (h : allR 0 N f = true) : ∀ k < N, f k = true :=
  fun k hk => (allR_iff 0 N f).1 h k (Nat.zero_le _) (by omega)

theorem all_of_chunks {N : ℕ} {f : ℕ → Bool} (hN : N = 20160)
    (h : ∀ c < 10, allR (2016 * c) 2016 f = true) : ∀ k < N, f k = true := by
  subst hN
  exact forall_of_chunks 2016 10 f h

theorem q2_checks : trB 41 = true ∧ srB 41 = true ∧ clB 41 = true := by
  obtain ⟨h1, h2⟩ := andB_eq_true (QK.all 0 (by norm_num))
  obtain ⟨h2, h3⟩ := andB_eq_true h2
  exact ⟨h1, h2, h3⟩

theorem tree_ok (m : ℕ) (hm : m < 42) :
    ∀ k < NN m, treeAt mul8 one8 (gM m) (NG m) (eM m) (pM m) k = true := by
  rcases Nat.lt_or_ge m 40 with h | h
  · exact all_of_allR (TK.all m h)
  · rcases Nat.lt_or_ge m 41 with h' | h'
    · obtain rfl : m = 40 := by omega
      exact all_of_chunks nn40 ATK.all
    · obtain rfl : m = 41 := by omega
      exact all_of_allR q2_checks.1

theorem sort_ok (m : ℕ) (hm : m < 42) : ∀ i < NN m, sortAt (NN m) (eM m) (sM m) i = true := by
  rcases Nat.lt_or_ge m 40 with h | h
  · exact all_of_allR (SK.all m h)
  · rcases Nat.lt_or_ge m 41 with h' | h'
    · obtain rfl : m = 40 := by omega
      exact all_of_chunks nn40 ASK.all
    · obtain rfl : m = 41 := by omega
      exact all_of_allR q2_checks.2.1

theorem closed_ok (m : ℕ) (hm : m < 42) :
    ∀ k < NN m, closedAt mul8 (gM m) (NG m) (NN m) (eM m) (cM m) k = true := by
  rcases Nat.lt_or_ge m 40 with h | h
  · exact all_of_allR (CK.all m h)
  · rcases Nat.lt_or_ge m 41 with h' | h'
    · obtain rfl : m = 40 := by omega
      exact all_of_chunks nn40 ACK.all
    · obtain rfl : m = 41 := by omega
      exact all_of_allR q2_checks.2.2

theorem group_exact (m : ℕ) (hm : m < 42) {cs : List ℕ} (hcs : cs = (List.range (NG m)).map (gM m))
    (hv : cs.all validC = true) :
    Nat.card (gh23Sub cs) = NN m ∧ ExactList gh23Code (gh23Sub cs) (NN m) (eM m) :=
  gh23_clos hcs hv (nn_pos m hm) (tree_ok m hm) (sort_ok m hm) (closed_ok m hm)

theorem member_exact (m : ℕ) (hm : m < 41) :
    Nat.card (gh23Sub (members.getD m ⟨[], .top⟩).gens) = NN m ∧
      ExactList gh23Code (gh23Sub (members.getD m ⟨[], .top⟩).gens) (NN m) (eM m) :=
  group_exact m (by omega) (gens_ok m hm) (members_valid m hm)

theorem q2_exact :
    Nat.card (gh23Sub q2gens) = NN 41 ∧ ExactList gh23Code (gh23Sub q2gens) (NN 41) (eM 41) :=
  group_exact 41 (by norm_num) q2_gens_ok.symm q2_valid

end CertificateChecks.KernelMisc.GH23

end
