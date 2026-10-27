module

public import Certificates.Kernel.PlusFactors.TableChecks
public import Certificates.Kernel.PlusFactors.Facts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelPlusF

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
  CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem tabSz : plusTableSizeCheck () = true := by
  unfold plusTableSizeCheck
  rw [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨by simp [bindE.1], fun i hi => ?_⟩
  rw [bindE.2 i hi]
  simp [unpack]

theorem tabValid : plusTableValidCheck () = true := tableOK

theorem rowLt {i j : ℕ} (hi : i < 60) (hj : j < 60) : pg 6 (mask 6) (PE.G i) j < 60 :=
  Nat.blt_eq.mp (and_of (AI.1 (AI.1 kTabConj i hi) j hj)).1

theorem tabInvol : plusTableInvolCheck () = true := by
  unfold plusTableInvolCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  rw [bindE.2 i hi, unpack_getElem! (PE.G i) j, if_pos hj,
    unpack_getElem! (PE.G i) (pg 6 (mask 6) (PE.G i) j), if_pos (rowLt hi hj)]
  have h := AI.1 (AI.1 kTabInvol i hi) j hj
  simpa using h

theorem tabConj : plusTableConjCheck () = true := by
  unfold plusTableConjCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  have h := (and_of (AI.1 (AI.1 kTabConj i hi) j hj)).2
  have hlt' := rowLt hi hj
  rw [bindE.2 i hi, bindE.2 j hj, unpack_getElem! (PE.G i) j, if_pos hj, bindE.2 _ hlt',
    compA_PP (gE hj) (gE hi), compA_PP (gE hi) ((gE hj).mul (gE hi)),
    eqA_PP (gE hlt') ((gE hi).mul ((gE hj).mul (gE hi)))]
  exact h

theorem tabKey : plusTableKeyCheck () = true := by
  unfold plusTableKeyCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  rw [bindE.2 i hi, bindE.2 j hj, keyA_unpack keysOK, keyA_unpack keysOK]
  have h := AI.1 (AI.1 kTabKey i hi) j hj
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd (Nat.eq_of_beq_eq_true h) hij
    · have h' : Nat.beq (pkeyK 60 6 plusBase (PE.G i)) (pkeyK 60 6 plusBase (PE.G j)) = false := by
        simpa using h
      simp [hij, Nat.ne_of_beq_eq_false h']

theorem tabCheck : plusTableCheck () = true := by
  simp [plusTableCheck, tabSz, tabValid, tabInvol, tabConj, tabKey]

theorem enumCheck : plusEnumCheck () = true := by
  have hE : enumOK 60 plusTable plusBase (plusEnum ()) = true :=
    enumOK_of_bfsK_base (by rw [bindE.1, nums.1])
      (fun k hk => bindE.2 k (by rw [nums.1] at hk; exact hk)) permE PE.ok keysOK kKE nums.2.1.le
  have hs : (plusEnum ()).pts.size = 7200 := by rw [pinE, Array.size_ofFn, nums.2.1]
  simp [plusEnumCheck, hE, hs]

end CertificateChecks.KernelPlusF
