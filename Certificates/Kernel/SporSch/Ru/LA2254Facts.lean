
module

public import CFSG.Sporadic.Schreier.RuOrbLFacts
import Certificates.Kernel.SporSch.Ru.LA2254P

public section

namespace CertificateChecks.KernelSporSch.RuLA

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

theorem ruZL_central
    {i : ℕ} (hi : i < 3) :
    ruZL i ∈ Subgroup.centralizer (ruL : Set (Equiv.Perm (Fin 4060))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hL : ruL ≤ Subgroup.centralizer {ruZL i} := closure_list_le fun g hg => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hg
    have hlen : ruLGens.length = 3 := by rw [ruLGens_eq]; rfl
    have hj3 : j < 3 := hlen ▸ hj
    have hrep : Rep 4060 ruLGensA[j]! g := by
      have := rep_ruLGens j hj3
      rwa [List.getD_eq_getElem _ _ hj, e] at this
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((ruCommTest_iff (rep_ruZL hi) hrep).1 (comms i hi j hj3)).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hL hl)

theorem ruOrb_disjoint
    {k k' : ℕ} (hk : k < 19) (hk' : k' < 19) (h : k ≠ k') :
    Disjoint (ruOrb k) (ruOrb k') := by
  have hinv : ∀ {k : ℕ} {t : Equiv.Perm (Fin 4060)}, t ∈ ruOrb k →
      ruLInvP t = ruLInv (ruRepZA k) := by
    rintro k _ ⟨l, hl, rfl⟩
    rw [ruLInvP_conj (fun i hi => ruZL_central hi) hl, ruLInv_eq (rep_ruRepZ k)]
  rw [Set.disjoint_left]
  intro t h1 h2
  exact h (List.inj_on_of_nodup_map nodup (List.mem_range.2 hk) (List.mem_range.2 hk')
    ((hinv h1).symm.trans (hinv h2)))

end CertificateChecks.KernelSporSch.RuLA

end
