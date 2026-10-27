module

public import Certificates.Kernel.MinusEnum.TableChecks
public import Certificates.Kernel.MinusEnum.Pin
public import CFSG.Certificates.Kernel.BfsPinSeedSound
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermCheck
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelMinusEnum

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
  CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem and_ofM {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

theorem keysM : ∀ p ∈ minusBase, p < 65 := by decide

theorem rowM {k : ℕ} (hk : k < 65) : minusTable[k]! = unpack 65 7 (ME.G k) :=
  bind.2 k (by rw [nums.1]; exact hk)

theorem gCM {k : ℕ} (hk : k < 65) : canonK 65 7 (mask 7) (65 * 7) (ME.G k) = true :=
  allN_spec kG k (by rw [nums.1]; exact hk)

theorem permM {k : ℕ} (hk : k < 65) :
    permOK 65 7 (mask 7) (65 * 7) (ME.G k) (pinvS 65 7 (mask 7) (ME.G k)) = true :=
  AI.1 kPermG k hk

theorem rowLtM {i j : ℕ} (hi : i < 65) (hj : j < 65) : pg 7 (mask 7) (ME.G i) j < 65 :=
  Nat.blt_eq.mp (and_ofM (AI.1 (AI.1 kTabConj i hi) j hj)).1

theorem conjM {i j : ℕ} (hi : i < 65) (hj : j < 65) :
    ME.G (pg 7 (mask 7) (ME.G i) j) = cmpM (ME.G i) (cmpM (ME.G j) (ME.G i)) :=
  Nat.eq_of_beq_eq_true (and_ofM (AI.1 (AI.1 kTabConj i hi) j hj)).2

theorem tabSz : minusTableSizeCheck () = true := by
  unfold minusTableSizeCheck
  rw [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨by simp [bind.1, nums.1], fun i hi => ?_⟩
  rw [rowM hi]
  simp [unpack]

theorem tabValid : minusTableValidCheck () = true := by
  unfold minusTableValidCheck
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [rowM hi]
  exact validA_unpack (permM hi)

theorem tabInvol : minusTableInvolCheck () = true := by
  unfold minusTableInvolCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  rw [rowM hi, unpack_getElem! (ME.G i) j, if_pos hj,
    unpack_getElem! (ME.G i) (pg 7 (mask 7) (ME.G i) j), if_pos (rowLtM hi hj)]
  have h := AI.1 (AI.1 kTabInvol i hi) j hj
  simpa using h

theorem tabConj : minusTableConjCheck () = true := by
  unfold minusTableConjCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  have h := (and_ofM (AI.1 (AI.1 kTabConj i hi) j hj)).2
  have hlt' := rowLtM hi hj
  rw [rowM hi, rowM hj, unpack_getElem! (ME.G i) j, if_pos hj, rowM hlt',
    compA_unpack (gCM hj) (gCM hi), compA_unpack (gCM hi) (canonK_pcomp (gCM hj) (gCM hi)),
    eqA_unpack (gCM hlt') (canonK_pcomp (gCM hi) (canonK_pcomp (gCM hj) (gCM hi)))]
  exact h

theorem tabKey : minusTableKeyCheck () = true := by
  unfold minusTableKeyCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  rw [rowM hi, rowM hj, keyA_unpack keysM, keyA_unpack keysM]
  have h := AI.1 (AI.1 kTabKey i hi) j hj
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd (Nat.eq_of_beq_eq_true h) hij
    · have h' : Nat.beq (pkeyK 65 7 minusBase (ME.G i)) (pkeyK 65 7 minusBase (ME.G j)) = false := by
        simpa using h
      simp [hij, Nat.ne_of_beq_eq_false h']

theorem tabCheck : minusTableCheck () = true := by
  simp [minusTableCheck, tabSz, tabValid, tabInvol, tabConj, tabKey]

theorem seedAll {i : ℕ} (hi : i < 15600) : seedM i = true := by
  have h5 : i / 3900 < 4 := by omega
  have h1 : 3900 * (i / 3900) ≤ i := Nat.mul_div_le i 3900
  have h2 : i < 3900 * (i / 3900) + 3900 := by omega
  interval_cases hq : i / 3900
  · exact AI.1 ch1383006s_0 i (by omega)
  · have := AI.1 ch1383006s_1 (i - 3900) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  · have := AI.1 ch1383006s_2 (i - 7800) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  · have := AI.1 ch1383006s_3 (i - 11700) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

theorem enumCheck : minusEnumCheck () = true := by
  have hD := Nat.eq_of_beq_eq_true kDeriv
  have hE : enumOK 65 minusTable minusBase (enumBfs 65 minusTable minusBase 15600) = true :=
    enumOK_of_seed (S := seedS) (D := derivD) bind.1 bind.2 kSz
      (fun k hk => permM (by rw [nums.1] at hk; exact hk))
      (fun k hk => gCM (by rw [nums.1] at hk; exact hk)) canonT (Nat.eq_of_beq_eq_true kT0)
      keysM kK ME.run.1 (by rw [nums.2])
      (fun s hs => by
        rw [nums.1]
        revert s
        decide)
      (fun i hi => by
        rw [nums.2] at hi ⊢
        exact seedAll hi)
      (fun i hi j hj => by
        rw [nums.1] at hi hj ⊢
        exact ⟨rowLtM hi hj, conjM hi hj⟩)
      (fun k hk => by
        rw [hD, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
        rw [nums.1] at hk
        exact hk)
  have hs : (minusEnum ()).pts.size = 15600 := by
    rw [minusEnum_pts, Array.size_ofFn, nums.2]
  simp only [minusEnumCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hE, hs⟩

end CertificateChecks.KernelMinusEnum

end
