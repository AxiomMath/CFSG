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

theorem conjSeedM : ∀ s ∈ seedS, ∀ j < 65,
    ME.G (pg 7 (mask 7) (ME.G s) j) = cmpM (ME.G s) (cmpM (ME.G j) (ME.G s)) := by
  obtain ⟨h012, h3⟩ := and_ofM kTabConj
  obtain ⟨h01, h2⟩ := and_ofM h012
  obtain ⟨h0, h1⟩ := and_ofM h01
  intro s hs
  simp only [seedS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact fun j hj => Nat.eq_of_beq_eq_true (AI.1 h0 j hj)
  · exact fun j hj => Nat.eq_of_beq_eq_true (AI.1 h1 j hj)
  · exact fun j hj => Nat.eq_of_beq_eq_true (AI.1 h2 j hj)
  · exact fun j hj => Nat.eq_of_beq_eq_true (AI.1 h3 j hj)

theorem conjAllM : ∀ i < 65, ∀ j < 65, pg 7 (mask 7) (ME.G i) j < 65 ∧
    ME.G (pg 7 (mask 7) (ME.G i) j) = cmpM (ME.G i) (cmpM (ME.G j) (ME.G i)) := by
  have hD := Nat.eq_of_beq_eq_true kDeriv
  refine conj_of_seed (D := derivD) (fun k hk => gCM hk) (fun s hs => ?_) conjSeedM
    (fun k hk => ?_)
  · revert s
    decide
  · rw [hD, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hk

theorem rowLtM {i j : ℕ} (hi : i < 65) (hj : j < 65) : pg 7 (mask 7) (ME.G i) j < 65 :=
  (conjAllM i hi j hj).1

theorem conjM {i j : ℕ} (hi : i < 65) (hj : j < 65) :
    ME.G (pg 7 (mask 7) (ME.G i) j) = cmpM (ME.G i) (cmpM (ME.G j) (ME.G i)) :=
  (conjAllM i hi j hj).2

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
  rw [rowM hi, unpack_getElem! (ME.G i) j, ite_eq_left hj,
    unpack_getElem! (ME.G i) (pg 7 (mask 7) (ME.G i) j), ite_eq_left (rowLtM hi hj)]
  have h := AI.1 (AI.1 kTabInvol i hi) j hj
  simpa using h

theorem tabConj : minusTableConjCheck () = true := by
  unfold minusTableConjCheck
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  have hlt' := rowLtM hi hj
  rw [rowM hi, rowM hj, unpack_getElem! (ME.G i) j, ite_eq_left hj, rowM hlt',
    compA_unpack (gCM hj) (gCM hi), compA_unpack (gCM hi) (canonK_pcomp (gCM hj) (gCM hi)),
    eqA_unpack (gCM hlt') (canonK_pcomp (gCM hi) (canonK_pcomp (gCM hj) (gCM hi))), conjM hi hj]
  exact Nat.beq_refl _

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

theorem facS_spec {o s : ℕ} (h : facS o s = true) : ∀ a < 65, ∃ a' < 65, ∃ b' < 240,
    pcomp 65 7 (mask 7) (ME.G s) (facR a) = pcomp 65 7 (mask 7) (facR a') (facK b') := by
  intro a ha
  obtain ⟨h12, h3⟩ := and_ofM (AI.1 h a ha)
  obtain ⟨h1, h2⟩ := and_ofM h12
  exact ⟨_, Nat.blt_eq.mp h1, _, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem facCanK : ∀ b < 240, canonK 65 7 (mask 7) (65 * 7) (facK b) = true :=
  AI.1 (and_ofM kFacCan).1

theorem facCanR : ∀ a < 65, canonK 65 7 (mask 7) (65 * 7) (facR a) = true :=
  AI.1 (and_ofM kFacCan).2

theorem facMul : ∀ b' < 240, ∀ b < 240, ∃ b'' < 240,
    pcomp 65 7 (mask 7) (facK b') (facK b) = facK b'' := by
  obtain ⟨hAB, hC0⟩ := and_ofM kFacK
  obtain ⟨hA, hB⟩ := and_ofM hAB
  refine mulK_of_gens (nC := 3) (cK := facC) (kk := facT) facCanK (fun c hc => ?_) (fun b hb => ?_)
  · obtain ⟨h1, h2⟩ := and_ofM (AI.1 hA c hc)
    refine ⟨Nat.blt_eq.mp h1, fun b hb => ?_⟩
    obtain ⟨h3, h4⟩ := and_ofM (AI.1 h2 b hb)
    exact ⟨Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4⟩
  · have h := AI.1 hB b hb
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl ⟨0, by omega, by rw [Nat.eq_of_beq_eq_true hC0, Nat.eq_of_beq_eq_true h]⟩
    · obtain ⟨h12, h3⟩ := and_ofM h
      obtain ⟨h1, h2⟩ := and_ofM h12
      exact Or.inr ⟨_, Nat.blt_eq.mp h2, _, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3⟩

theorem facSeed : ∀ s ∈ seedS, ∀ a < 65, ∃ a' < 65, ∃ b' < 240,
    pcomp 65 7 (mask 7) (ME.G s) (facR a) = pcomp 65 7 (mask 7) (facR a') (facK b') := by
  intro s hs
  simp only [seedS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact facS_spec kFacS0
  · exact facS_spec kFacS1
  · exact facS_spec kFacS2
  · exact facS_spec kFacS3

theorem enumCheck : minusEnumCheck () = true := by
  have hD := Nat.eq_of_beq_eq_true kDeriv
  have hcG : ∀ k < ME.ng, canonK 65 7 (mask 7) (65 * 7) (ME.G k) = true :=
    fun k hk => gCM (by rw [nums.1] at hk; exact hk)
  have hcl := cl_of_factor (S := seedS) (D := derivD) (nR := 65) (nK := 240) hcG facCanR facCanK
    facMul facSeed ⟨0, by omega, 0, by omega, Nat.eq_of_beq_eq_true kFacT0⟩ kK ME.run.1
    (by rw [nums.2])
    (fun s hs => by
      rw [nums.1]
      revert s
      decide)
    (fun i hi j hj => by
      rw [nums.1] at hi hj ⊢
      exact ⟨rowLtM hi hj, conjM hi hj⟩)
    (fun k hk => by
      rw [hD, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      rw [nums.1] at hk
      exact hk)
  have hE : enumOK 65 minusTable minusBase (enumBfs 65 minusTable minusBase 15600) =
      true :=
    enumOK_of_cl bind.1 bind.2 kSz
      (fun k hk => permM (by rw [nums.1] at hk; exact hk)) hcG canonT
      (Nat.eq_of_beq_eq_true kT0) keysM kK ME.run.1 (by rw [nums.2]) hcl
  have hs : (minusEnum ()).pts.size = 15600 := by
    rw [minusEnum_pts, Array.size_ofFn, nums.2]
  simp only [minusEnumCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hE, hs⟩

end CertificateChecks.KernelMinusEnum

end
