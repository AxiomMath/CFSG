module

public import CFSG.Certificates.Kernel.U62PairSound
public import Certificates.Kernel.U62Pair.Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses
import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Kernel.UnitarySix.LettersBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU62P

open CFSG.KC.U62P CFSG.ComponentClassification.RankTwoHypIICover.U62
open CFSG.Sporadic.Schreier (evalCodes tab_eq)

theorem u62Let_eq :
    u62Let = CFSG.EvenSmallLie.UnitarySix.u62Letters := by
  unfold u62Let CFSG.EvenSmallLie.UnitarySix.u62Letters
  refine List.map_congr_left fun (k : Fin 46) _ => ?_
  exact (CFSG.EvenSmallLie.UnitarySix.letter_eq k.val k.isLt).symm

theorem sbWords_eq :
    u62SbWords = CFSG.EvenSmallLie.UnitarySix.aWords ++ CFSG.EvenSmallLie.UnitarySix.tWords := rfl

theorem rWords_eq : u62RWords = CFSG.EvenSmallLie.UnitarySix.sRepWords := rfl

theorem sbG_eq :
    u62SbG = CFSG.EvenSmallLie.UnitarySix.sGens := by
  rw [u62SbG, CFSG.EvenSmallLie.UnitarySix.sGens, CFSG.EvenSmallLie.UnitarySix.aGens,
    CFSG.EvenSmallLie.UnitarySix.tGens, ← List.map_append, ← sbWords_eq, u62Let_eq]
  refine List.map_congr_left fun w _ => ?_
  rw [CFSG.EvenSmallLie.UnitarySix.u62W, tab_eq]

theorem sb_eq :
    u62Sb = CFSG.EvenSmallLie.UnitarySix.uS := by
  rw [CFSG.EvenSmallLie.UnitarySix.uS_closure, ← sbG_eq]
  rfl

theorem card_sb :
    Nat.card u62Sb = 32768 := by
  rw [sb_eq]
  exact CFSG.EvenSmallLie.UnitarySix.card_uS

theorem mem_sReps
    {r : Equiv.Perm (Fin 693)} (hr : r ∈ CFSG.EvenSmallLie.UnitarySix.sReps) :
    ∃ j < 43, r = u62R j := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
  have hj' : j < 43 := hj
  refine ⟨j, hj', ?_⟩
  rw [u62R, sbG_eq, rWords_eq, List.getD_eq_getElem _ _ hj]

theorem classes_sb :
    ∀ u ∈ u62Sb, orderOf u = 2 → ∃ j < 43, ∃ c ∈ u62Sb, u = c * u62R j * c⁻¹ := by
  intro u hu ho
  rw [sb_eq] at hu ⊢
  obtain ⟨r, hr, c, hc, e⟩ := CFSG.EvenSmallLie.UnitarySix.sylow_facts.1 u hu ho
  obtain ⟨j, hj, rfl⟩ := mem_sReps hr
  exact ⟨j, hj, c, hc, e⟩

theorem blocks {f : Nat → Bool} {B n : Nat}
    (h : ∀ s < n, CFSG.KC.Enum.allBlk (B * s) f B = true) : ∀ i < B * n, f i = true := by
  intro i hi
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hs : i / B < n := (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact hi)
  have e := CFSG.KS.allBlk_spec (h (i / B) hs) (i % B) (Nat.mod_lt _ hB)
  have e2 : Nat.add (B * (i / B)) (i % B) = i := Nat.div_add_mod i B
  rwa [e2] at e

theorem below {f : Nat → Bool} {b n : Nat} (h : CFSG.KC.Enum.allBlk b f n = true) :
    ∀ i, b ≤ i → i < b + n → f i = true := by
  intro i h1 h2
  have e := CFSG.KS.allBlk_spec h (i - b) (by omega)
  have e2 : Nat.add b (i - b) = i := by change b + (i - b) = i; omega
  rwa [e2] at e

theorem lst_all : ∀ i < 32768, lst i = true := by
  have h : ∀ s < 16, CFSG.KC.Enum.allBlk (2048 * s) lst 2048 = true := by
    intro s hs
    interval_cases s
    exacts [kLst_0, kLst_1, kLst_2, kLst_3, kLst_4, kLst_5, kLst_6, kLst_7, kLst_8, kLst_9,
      kLst_10, kLst_11, kLst_12, kLst_13, kLst_14, kLst_15]
  exact blocks h

theorem ent_all : ∀ q < 512, ent q = true := by
  have h : ∀ s < 16, CFSG.KC.Enum.allBlk (32 * s) ent 32 = true := by
    intro s hs
    interval_cases s
    exacts [kEnt_0, kEnt_1, kEnt_2, kEnt_3, kEnt_4, kEnt_5, kEnt_6, kEnt_7, kEnt_8, kEnt_9,
      kEnt_10, kEnt_11, kEnt_12, kEnt_13, kEnt_14, kEnt_15]
  exact blocks h

theorem pool_all : ∀ p < 1771, pool p = true := by
  have h : ∀ s < 6, CFSG.KC.Enum.allBlk (256 * s) pool 256 = true := by
    intro s hs
    interval_cases s
    exacts [kPool_0, kPool_1, kPool_2, kPool_3, kPool_4, kPool_5]
  intro p hp
  rcases Nat.lt_or_ge p 1536 with h1 | h1
  · exact blocks h p h1
  · exact below kPool_6 p h1 (by omega)

theorem rec_all : ∀ g < 896, rec g = true := by
  have h : ∀ s < 2, CFSG.KC.Enum.allBlk (448 * s) rec 448 = true := by
    intro s hs
    interval_cases s
    exacts [kRec_0, kRec_1]
  exact blocks h

theorem bAnd_iff' {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := CFSG.KS.bAnd_iff a b

theorem lst_parts {i : Nat} (hi : i < 32768) :
    treeAt D.GV D.LV D.PT D.LB i = true ∧ sortAt D.LV D.SO 32768 i = true ∧
      phiAt D.LV D.UP D.XP D.NXP i = true ∧ scanAt D.LV D.PO D.EI D.NO i = true := by
  have h := lst_all i hi
  unfold lst at h
  obtain ⟨h1, h⟩ := bAnd_iff'.1 h
  obtain ⟨h2, h⟩ := bAnd_iff'.1 h
  obtain ⟨h3, h4⟩ := bAnd_iff'.1 h
  exact ⟨h1, h2, h3, h4⟩

theorem tv_D : D.TV = CertificateChecks.KernelU6.U.TV := rfl

theorem up_D : D.UP = CertificateChecks.KernelU6.U.UP := rfl

theorem facts :
    U62Facts := by
  have hNO : D.NO = 512 := Nat.eq_of_beq_eq_true kNO
  have hNG : D.NG = 896 := Nat.eq_of_beq_eq_true kNG
  have hNP : D.NP = 1771 := Nat.eq_of_beq_eq_true kNP
  have hK := kFacts_of_K (TV := D.TV) (UP := D.UP) (GV := D.GV) (RV := D.RV) (LV := D.LV)
    (PT := D.PT) (LB := D.LB) (SO := D.SO) (NI := D.NI) (XP := D.XP) (NXP := D.NXP) (PO := D.PO)
    (NO := D.NO) (NP := D.NP) (T := ET0)
    (by rw [tv_D]; exact CertificateChecks.KernelU6.tv_eq)
    (by rw [up_D]; exact CertificateChecks.KernelU6.up_eq) card_sb
    (fun k hk => below kGen k (Nat.zero_le _) (by omega))
    (fun j hj => below kRep j (Nat.zero_le _) (by omega))
    (fun i hi => (lst_parts hi).1) (fun i hi => (lst_parts hi).2.1)
    (fun i hi => (lst_parts hi).2.2.1) (fun k hk => below kNorm k (Nat.zero_le _) (by omega))
    (fun q hq => below kFix q (Nat.zero_le _) (by omega)) (fun i hi => (lst_parts hi).2.2.2) rfl rfl
    (fun p hp => pool_all p (hNP ▸ hp)) (fun g hg => rec_all g (hNG ▸ hg))
    (fun q hq => ent_all q (hNO ▸ hq))
  obtain ⟨h1, h3, h4, h6⟩ := hK
  exact ⟨h1, card_sb, h3, h4, classes_sb, h6⟩

end CertificateChecks.KernelU62P

end
