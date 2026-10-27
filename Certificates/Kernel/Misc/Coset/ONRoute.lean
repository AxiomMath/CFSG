module

public import Certificates.Kernel.Bounds.ON
public import CFSG.Certificates.Kernel.CosetBounds

public section

namespace CertificateChecks.KernelMiscCoset

open CFSG.Certificates CFSG.KBRoute.ON

theorem card_le_of_ON_rels {G : Type*} [Group G] (gen : ℕ → G)
    (hrels : ∀ r ∈ CFSG.KBRoute.ON.rels, KB.sword gen r = 1)
    (hgen : Subgroup.closure (gen '' {g | g < 7}) = ⊤) :
    Finite G ∧ Nat.card G ≤ 460815505920 := by
  obtain ⟨h1, h2, h3, htop, l1, l2⟩ := CertificateChecks.KernelBounds.ON.facts_holds
  delta T1.ok at h1
  delta T2.ok at h2
  delta T3.ok at h3
  have s1 := KB.tableOk_sound gen hrels h1
  have s2 := KB.tableOk_sound gen hrels h2
  have s3 := KB.tableOk_sound gen hrels h3
  rw [KB.linkOk_sound gen (KB.tableOk_lens h1).2 l1] at s1
  rw [KB.linkOk_sound gen (KB.tableOk_lens h2).2 l2] at s2
  rw [show T3.words = [] from rfl, KB.wordSub_nil] at s3
  have c := KB.card_le_step s1 <| KB.card_le_step s2 <| KB.card_le_step s3 KB.card_bot_le
  have hset : {g | KB.inAlpha T1.amap g} = {g | g < 7} :=
    Set.ext fun g => KB.topOk_sound (by norm_num) htop g
  have hK : KB.alphaSub gen T1.amap = ⊤ := by
    rw [KB.alphaSub, hset, hgen]
  exact (KB.finite_card_le_of_top hK c).imp id fun h => h.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelMiscCoset

end
