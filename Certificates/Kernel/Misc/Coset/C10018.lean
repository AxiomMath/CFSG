module

public import CFSG.LieType.Multipliers.U62SylowInputs
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.MemSound
public import Certificates.Kernel.Misc.Coset.XU62S81
public import Certificates.Kernel.Misc.Coset.XU62SR
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.U62Data
import CFSG.LieType.Multipliers.CoverWords
import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.CosetTableShort
public import CFSG.Fischer.T46Simple
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelMiscCoset.C10018

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62
  CFSG.Certificates

set_option maxRecDepth 100000

theorem t81 : sylowRels.map encW = CFSG.KBRoute.XU62S81.rels := by decide +kernel

theorem sylow_card_le : Finite (PG 2 sylowRels) ∧ Nat.card (PG 2 sylowRels) ≤ 81 := by
  have h := XU62S81.t1
  unfold CFSG.KBRoute.XU62S81.T1.ok at h
  exact card_le_of_tableOk sylowRels t81 h (by norm_num) CFSG.KBRoute.XU62S81.top rfl

theorem tSR : coverAB.map encW = CFSG.KBRoute.XU62SR.rels := by decide +kernel

theorem codes_eq : (sylowRels.map (substWord sylowWordsAB)).map (fun u => (encW u).map Mem.codeN) =
    [[0, 2, 0, 2, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 0, 2, 0, 2, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 0, 2, 0, 2, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3], [3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1], [0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3], [2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1]] := by decide +kernel

theorem walk0 : Mem.memOK CFSG.KBData.XU62SR_T1v.F 1791081
    [0, 2, 0, 2, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 0, 2, 0, 2, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 0, 2, 0, 2, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3]
    [0, 6, 18, 38, 76, 3293247, 3293625, 266, 464, 3355163, 1364, 2284, 3396069, 5964, 9316, 9317, 5965, 3731, 3390950, 2281, 3413013, 3722, 5950, 3391395, 14170, 20668, 28804, 3447647, 3311366, 18261, 18258, 25848, 3332303, 46504, 3525158, 3540231, 3540232, 85854, 3568479, 3577611, 103488, 103489, 3577610, 95947, 3563049, 3563044, 3555534, 85395, 72335, 58269, 45039, 34007, 3320594, 17485, 3296465, 3281307, 7605, 4805, 2983, 1803, 1063, 623, 624, 3369868, 3372588, 1800, 2980, 2981, 1801, 1061, 621, 359, 205, 113, 59, 31, 13, 3] = true := by quickRfl

theorem walk1 : Mem.memOK CFSG.KBData.XU62SR_T1v.F 1791081
    [3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1]
    [4, 3336949, 34, 3363301, 126, 3449901, 396, 3491865, 1168, 1970, 3444237, 5204, 3444305, 5073, 5074, 3431676, 3431682, 12320, 18272, 18273, 12321, 8007, 5071, 3161, 1917, 1918, 3332331, 3308841, 5068, 8004, 8005, 5069, 3159, 1915, 1133, 663, 383, 219, 123, 65, 33, 32, 64, 3364325, 220, 386, 3357357, 1144, 1930, 3367823, 5112, 8068, 8069, 5113, 3183, 3323919, 1927, 3333083, 2266, 3304919, 3262415, 5912, 9252, 9253, 5913, 3699, 2265, 1351, 793, 461, 265, 149, 3293246, 77, 39, 19, 7, 1] = true := by quickRfl

theorem walk2 : Mem.memOK CFSG.KBData.XU62SR_T1v.F 1791081
    [0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3]
    [0, 6, 18, 38, 76, 3293247, 148, 264, 460, 792, 1350, 2264, 3698, 5912, 9252, 9253, 5913, 3262414, 3304918, 2267, 3333082, 1926, 3323918, 3182, 5112, 8068, 12406, 18374, 3381732, 3418229, 20696, 2257056, 24238, 33152, 43980, 57008, 71016, 3539429, 85366, 95582, 101886, 101887, 95583, 3554648, 72313, 58245, 3394383, 33993, 24907, 3393941, 3337643, 11715, 11712, 3394444, 3399608, 3435395, 7733, 4891, 3413362, 1841, 1087, 3348934, 636, 3374313, 1094, 1856, 3062, 3063, 1857, 3376790, 641, 371, 3393612, 117, 61, 3312678, 13, 3] = true := by quickRfl

theorem walk3 : Mem.memOK CFSG.KBData.XU62SR_T1v.F 1791081
    [2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1]
    [2, 12, 30, 58, 112, 204, 358, 620, 1060, 1800, 2980, 2981, 1801, 3372589, 3369869, 625, 622, 1062, 1802, 2982, 4804, 7604, 11730, 3300637, 3297236, 7785, 7782, 11976, 17852, 25340, 34506, 45690, 58998, 73056, 86024, 96074, 102088, 102089, 96075, 3555452, 3540188, 67037, 3458228, 40573, 30311, 3446322, 15151, 15152, 21940, 2293683, 3471948, 3490634, 35528, 46932, 3485411, 74450, 3556695, 3561141, 3561142, 3564477, 3575691, 3575692, 103262, 103263, 3575693, 100559, 92953, 3550564, 78555, 64691, 50899, 38827, 3512104, 28847, 20707, 14199, 3445503, 3418223, 3418228, 3381733, 18375, 12407, 8069, 5113, 3183, 3323919, 1927, 3333083, 2266, 3304919, 3262415, 5912, 9252, 9253, 5913, 3699, 2265, 1351, 793, 461, 265, 149, 3293246, 77, 39, 19, 7, 1] = true := by quickRfl

theorem relations : ∀ u ∈ sylowRels.map (substWord sylowWordsAB),
    PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverAB.map FreeGroup.mk} (FreeGroup.mk u) = 1 := by
  have h := XU62SR.t1
  unfold CFSG.KBRoute.XU62SR.T1.ok at h
  intro u hu
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  have hex : ∃ refs, Mem.memOK CFSG.KBData.XU62SR_T1v.F 1791081
      ((encW (sylowRels.map (substWord sylowWordsAB))[k]).map Mem.codeN) refs = true := by
    have hm : (encW (sylowRels.map (substWord sylowWordsAB))[k]).map Mem.codeN ∈
        (sylowRels.map (substWord sylowWordsAB)).map (fun u => (encW u).map Mem.codeN) :=
      List.mem_map.2 ⟨_, List.getElem_mem hk, rfl⟩
    rw [codes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e | e <;> rw [e]
    · exact ⟨_, walk0⟩
    · exact ⟨_, walk1⟩
    · exact ⟨_, walk2⟩
    · exact ⟨_, walk3⟩
  obtain ⟨refs, hw⟩ := hex
  have hm := Mem.memOK_sound (pgGen coverAB) (sword_rels coverAB tSR) h (by norm_num)
    CFSG.KBRoute.XU62SR.top (u := encW (sylowRels.map (substWord sylowWordsAB))[k]) (by
      intro l hl
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      exact x.1.isLt) hw
  rw [sword_pgGen, show CFSG.KBRoute.XU62SR.T1.words = [] from rfl, KB.wordSub_nil,
    Subgroup.mem_bot] at hm
  exact hm

end CertificateChecks.KernelMiscCoset.C10018

end
