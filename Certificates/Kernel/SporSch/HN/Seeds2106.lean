module

public import Certificates.Kernel.SporSch.HN.Seeds2106K
public import CFSG.Certificates.Kernel.SporSch.HNF5Assoc
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.HNF5KronSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNSeeds

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CertificateChecks.KernelSporSch

theorem entK {K : Nat} (hK : K < 54) : Canon5 (sl K) ∧
    (HNT.OP K = 0 → Canon5 (sl (HNT.L K)) → Canon5 (sl (HNT.R K)) →
      ∀ i < 133, vm5 (sl (HNT.R K)) (sl (HNT.L K) i) = sl K i) ∧
    (HNT.OP K = 1 → ∀ i < 133, sl (HNT.L K) i = sl K i) := by
  rcases (by omega : K < 9 ∨ (9 ≤ K ∧ K < 18) ∨ (18 ≤ K ∧ K < 27) ∨ (27 ≤ K ∧ K < 36) ∨
      (36 ≤ K ∧ K < 45) ∨ 45 ≤ K) with h | h | h | h | h | h
  · exact F5Kron.krBlk_sound blk0 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk1 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk2 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk3 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk4 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk5 (by omega) (by omega)

theorem canon (k : Nat) (hk : k < 54) : Canon5 (sl k) := (entK hk).1

theorem mulE {K l r : Nat} (hK : K < 54) (ho : HNT.OP K = 0) (hl : HNT.L K = l)
    (hr : HNT.R K = r) (hl54 : l < 54) (hr54 : r < 54) : ∀ i < 133, vm5 (sl r) (sl l i) = sl K i := by
  subst hl hr
  exact (entK hK).2.1 ho (canon _ hl54) (canon _ hr54)

theorem copyE {K l : Nat} (hK : K < 54) (ho : HNT.OP K = 1) (hl : HNT.L K = l) :
    ∀ i < 133, sl l i = sl K i := by
  subst hl
  exact (entK hK).2.2 ho

theorem mul_eq {K l r : Nat} (hl54 : l < 54) (hr54 : r < 54) (hK : K < 54)
    (ho : HNT.OP K = 0) (hl : HNT.L K = l) (hr : HNT.R K = r) :
    mulM 5 133 (rows5 (sl l)) (rows5 (sl r)) = rows5 (sl K) :=
  mulM5_sound (canon l hl54) (canon r hr54) (mulE hK ho hl hr hl54 hr54)

theorem spec_of {o n : Nat} {R : Nat → Nat}
    (h : allN n (fun u => bAnd(Nat.beq (HNT.OP (o + u + 2)) 0,
      bAnd(Nat.beq (HNT.L (o + u + 2)) (o + u + 1), Nat.beq (HNT.R (o + u + 2)) (R u)))) = true)
    (u : Nat) (hu : u < n) :
    HNT.OP (o + u + 2) = 0 ∧ HNT.L (o + u + 2) = o + u + 1 ∧ HNT.R (o + u + 2) = R u := by
  have := allN_spec h u hu
  obtain ⟨a, bc⟩ := (bAnd_iff _ _).1 this
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 bc
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩

theorem pow_eq {m o e : Nat} (he : 1 ≤ e) (hm : m < 54) (hoe : o + e < 54)
    (hc : HNT.OP (o + 1) = 1 ∧ HNT.L (o + 1) = m)
    (hs : allN (e - 1) (fun u => bAnd(Nat.beq (HNT.OP (o + u + 2)) 0,
      bAnd(Nat.beq (HNT.L (o + u + 2)) (o + u + 1), Nat.beq (HNT.R (o + u + 2)) m))) = true) :
    powM 5 133 (rows5 (sl m)) e = rows5 (sl (o + e)) := by
  refine powM5_chain (M := sl m) (P := fun t => sl (o + t)) he (canon m hm)
    (fun t _ ht => canon (o + t) (by omega)) (fun i hi => (copyE (by omega) hc.1 hc.2 i hi).symm)
    (fun t h1 ht i hi => ?_)
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  obtain ⟨a, b, c⟩ := spec_of (R := fun _ => m) hs u (by omega)
  have := mulE (by omega) a b c (by omega) hm i hi
  have e1 : o + (u + 1) = o + u + 1 := by omega
  simp only [e1]
  exact this

theorem pow_add_step {M : Array (Array Nat)} (hM : mulM 5 133 (idM 133) M = M) {a b x y K : Nat}
    (hb : 1 ≤ b) (ha : powM 5 133 M a = rows5 (sl x)) (hb' : powM 5 133 M b = rows5 (sl y))
    (hK : mulM 5 133 (rows5 (sl x)) (rows5 (sl y)) = rows5 (sl K)) :
    powM 5 133 M (a + b) = rows5 (sl K) := by
  rw [powM5_add hM a b hb, ha, hb', hK]

theorem pow_one_eq {M : Array (Array Nat)} (hM : mulM 5 133 (idM 133) M = M) :
    powM 5 133 M 1 = M := by
  rw [powM, powM, hM]

theorem ltc_one : ltc 1 = 0 := rfl

theorem ltc_two : ltc 2 = 1 := rfl

theorem word_eq {w : List Nat} {o : Nat} (hn1 : 1 ≤ w.length) (hon : o + w.length < 54)
    (hmem : ∀ l ∈ w, l = 1 ∨ l = 2)
    (hc : HNT.OP (o + 1) = 1 ∧ HNT.L (o + 1) = ltc (w.headD 0))
    (hs : allN (w.length - 1) (fun u => bAnd(Nat.beq (HNT.OP (o + u + 2)) 0,
      bAnd(Nat.beq (HNT.L (o + u + 2)) (o + u + 1),
        Nat.beq (HNT.R (o + u + 2)) (ltc (w.getD (u + 1) 0))))) = true) :
    wordM (seedSel (rows5 (sl 0)) (rows5 (sl 1))) w = rows5 (sl (o + w.length)) := by
  have hl54 : ∀ l ∈ w, ltc l < 54 := fun l hl => by
    rcases hmem l hl with rfl | rfl <;> decide
  refine wordM5_chain (LT := fun l => sl (ltc l)) (Q := fun t => sl (o + t)) hn1
    (fun l hl => ?_) (fun l hl => canon (ltc l) (hl54 l hl)) (fun t _ ht => canon (o + t) (by omega))
    (fun i hi => (copyE (by omega) hc.1 hc.2 i hi).symm) (fun t h1 ht i hi => ?_)
  · rcases hmem l hl with rfl | rfl
    · rfl
    · rfl
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    obtain ⟨a, b, c⟩ := spec_of (R := fun u => ltc (w.getD (u + 1) 0)) hs u (by omega)
    have hr : ltc (w.getD (u + 1) 0) < 54 := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hl54 _ (List.getElem_mem _)
    have := mulE (by omega) a b c (by omega) hr i hi
    have e1 : o + (u + 1) = o + u + 1 := by omega
    simp only [e1]
    exact this

theorem rowsA_eq : rowsA = rows5 (sl 0) := by
  rw [rowsA, HNSeedA.eq]
  exact pay5_sound payA

theorem rowsB_eq : rowsB = rows5 (sl 1) := by
  rw [rowsB, HNSeedB.eq]
  exact pay5_sound payB

theorem bnot {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b <;> simp_all

theorem notId {k : Nat} (hk : k < 54)
    (h : anyN 133 (fun i => Bool.not (Nat.beq (sl k i) (idRow5 i))) = true) :
    notIdM 133 (rows5 (sl k)) = true := by
  obtain ⟨i, hi, hn⟩ := anyN_spec h
  refine notId5_sound (canon k hk) ⟨i, hi, fun he => ?_⟩
  have := bnot hn
  rw [he, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem isId {k : Nat} (h : allN 133 (fun i => Nat.beq (sl k i) (idRow5 i)) = true) :
    (rows5 (sl k) == idM 133) = true :=
  eqId5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem cA : allN 1 (fun u => bAnd(Nat.beq (HNT.OP (1 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (1 + u + 2)) (1 + u + 1), Nat.beq (HNT.R (1 + u + 2)) 0))) = true := by quickRfl
theorem cB : allN 2 (fun u => bAnd(Nat.beq (HNT.OP (3 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (3 + u + 2)) (3 + u + 1), Nat.beq (HNT.R (3 + u + 2)) 1))) = true := by quickRfl
theorem cG : allN 11 (fun u => bAnd(Nat.beq (HNT.OP (13 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (13 + u + 2)) (13 + u + 1),
      Nat.beq (HNT.R (13 + u + 2)) (ltc (gWord.getD (u + 1) 0))))) = true := by quickRfl
theorem cGi : allN 17 (fun u => bAnd(Nat.beq (HNT.OP (25 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (25 + u + 2)) (25 + u + 1),
      Nat.beq (HNT.R (25 + u + 2)) (ltc (gInvWord.getD (u + 1) 0))))) = true := by quickRfl

theorem facts : seedChecks rowsA rowsB = true := by
  have hA2 : powM 5 133 (rows5 (sl 0)) 2 = rows5 (sl 3) :=
    pow_eq (o := 1) (by omega) (by omega) (by omega) ⟨rfl, rfl⟩ cA
  have hB3 : powM 5 133 (rows5 (sl 1)) 3 = rows5 (sl 6) :=
    pow_eq (o := 3) (by omega) (by omega) (by omega) ⟨rfl, rfl⟩ cB
  have hAB : mulM 5 133 (rows5 (sl 0)) (rows5 (sl 1)) = rows5 (sl 7) :=
    mul_eq (by omega) (by omega) (by omega) rfl rfl rfl
  have hP := mulM5_idL (canon 7 (by omega))
  have p1 := pow_one_eq hP
  have p2 : powM 5 133 (rows5 (sl 7)) 2 = rows5 (sl 8) := pow_add_step hP (a := 1) (b := 1)
    (by omega) p1 p1 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have p4 : powM 5 133 (rows5 (sl 7)) 4 = rows5 (sl 9) := pow_add_step hP (a := 2) (b := 2)
    (by omega) p2 p2 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have p5 : powM 5 133 (rows5 (sl 7)) 5 = rows5 (sl 10) := pow_add_step hP (a := 4) (b := 1)
    (by omega) p4 p1 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have p10 : powM 5 133 (rows5 (sl 7)) 10 = rows5 (sl 11) := pow_add_step hP (a := 5) (b := 5)
    (by omega) p5 p5 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have p11 : powM 5 133 (rows5 (sl 7)) 11 = rows5 (sl 12) := pow_add_step hP (a := 10) (b := 1)
    (by omega) p10 p1 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have p22 : powM 5 133 (rows5 (sl 7)) 22 = rows5 (sl 13) := pow_add_step hP (a := 11) (b := 11)
    (by omega) p11 p11 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have hG : wordM (seedSel (rows5 (sl 0)) (rows5 (sl 1))) gWord = rows5 (sl 25) :=
    word_eq (o := 13) (by decide) (by decide) (by decide) ⟨rfl, rfl⟩ cG
  have hGi : wordM (seedSel (rows5 (sl 0)) (rows5 (sl 1))) gInvWord = rows5 (sl 43) :=
    word_eq (o := 25) (by decide) (by decide) (by decide) ⟨rfl, rfl⟩ cGi
  have hGGi : mulM 5 133 (rows5 (sl 25)) (rows5 (sl 43)) = rows5 (sl 44) :=
    mul_eq (by omega) (by omega) (by omega) rfl rfl rfl
  have hX1 : mulM 5 133 (rows5 (sl 0)) (rows5 (sl 43)) = rows5 (sl 45) :=
    mul_eq (by omega) (by omega) (by omega) rfl rfl rfl
  have hX2 : mulM 5 133 (rows5 (sl 45)) (rows5 (sl 1)) = rows5 (sl 46) :=
    mul_eq (by omega) (by omega) (by omega) rfl rfl rfl
  have hX3 : mulM 5 133 (rows5 (sl 46)) (rows5 (sl 25)) = rows5 (sl 47) :=
    mul_eq (by omega) (by omega) (by omega) rfl rfl rfl
  have hX := mulM5_idL (canon 47 (by omega))
  have q1 := pow_one_eq hX
  have q2 : powM 5 133 (rows5 (sl 47)) 2 = rows5 (sl 48) := pow_add_step hX (a := 1) (b := 1)
    (by omega) q1 q1 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have q4 : powM 5 133 (rows5 (sl 47)) 4 = rows5 (sl 49) := pow_add_step hX (a := 2) (b := 2)
    (by omega) q2 q2 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have q8 : powM 5 133 (rows5 (sl 47)) 8 = rows5 (sl 50) := pow_add_step hX (a := 4) (b := 4)
    (by omega) q4 q4 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have q16 : powM 5 133 (rows5 (sl 47)) 16 = rows5 (sl 51) := pow_add_step hX (a := 8) (b := 8)
    (by omega) q8 q8 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have q18 : powM 5 133 (rows5 (sl 47)) 18 = rows5 (sl 52) := pow_add_step hX (a := 16) (b := 2)
    (by omega) q16 q2 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  have q19 : powM 5 133 (rows5 (sl 47)) 19 = rows5 (sl 53) := pow_add_step hX (a := 18) (b := 1)
    (by omega) q18 q1 (mul_eq (by omega) (by omega) (by omega) rfl rfl rfl)
  unfold seedChecks
  dsimp only
  rw [rowsA_eq, rowsB_eq, hA2, hB3, hAB, p22, p11, p2, hG, hGi, hGGi, hX1, hX2, hX3, q19]
  rw [isId id3, isId id6, isId id13, isId id44, isId id53, notId (by omega) ne0,
    notId (by omega) ne1, notId (by omega) ne12, notId (by omega) ne8, notId (by omega) ne47]
  rfl

end CertificateChecks.KernelSporSch.HNSeeds

end
