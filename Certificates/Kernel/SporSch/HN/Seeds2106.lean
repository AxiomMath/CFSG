module

public import Certificates.Kernel.SporSch.HN.Seeds2106K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNSeeds

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CertificateChecks.KernelSporSch

theorem canon (k : Nat) (hk : k < 83) : Canon5 (sl k) := by
  intro i hi
  have hc : canonAll HNT.MT k = true := by
    rcases Nat.lt_or_ge k 21 with a | a
    · have := allBlk_spec can0 k a
      simpa [Nat.add_eq] using this
    rcases Nat.lt_or_ge k 42 with b | b
    · have := allBlk_spec can1 (k - 21) (by omega)
      simpa [Nat.add_eq, Nat.add_sub_cancel' a] using this
    rcases Nat.lt_or_ge k 63 with c | c
    · have := allBlk_spec can2 (k - 42) (by omega)
      simpa [Nat.add_eq, Nat.add_sub_cancel' b] using this
    · have := allBlk_spec can3 (k - 63) (by omega)
      simpa [Nat.add_eq, Nat.add_sub_cancel' c] using this
  exact allN_spec hc i hi

theorem ent (K : Nat) (h2 : 2 ≤ K) (hK : K < 83) :
    ∀ b < 7, entryOK HNT.MT HNT.OP HNT.L HNT.R K b = true := by
  have h := HNT.hall (K - 2) (by omega)
  have e : Nat.add (K - 2) 2 = K := by
    rw [Nat.add_eq]
    omega
  rwa [e] at h

theorem mulE {K l r : Nat} (h2 : 2 ≤ K) (hK : K < 83) (ho : HNT.OP K = 0) (hl : HNT.L K = l)
    (hr : HNT.R K = r) : ∀ i < 133, vm5 (sl r) (sl l i) = sl K i :=
  entry_mul (ent K h2 hK) ho hl hr

theorem copyE {K l : Nat} (h2 : 2 ≤ K) (hK : K < 83) (ho : HNT.OP K = 1) (hl : HNT.L K = l) :
    ∀ i < 133, sl l i = sl K i :=
  entry_copy (ent K h2 hK) ho hl

theorem mul_eq {K l r : Nat} (hl83 : l < 83) (hr83 : r < 83) (h2 : 2 ≤ K) (hK : K < 83)
    (ho : HNT.OP K = 0) (hl : HNT.L K = l) (hr : HNT.R K = r) :
    mulM 5 133 (rows5 (sl l)) (rows5 (sl r)) = rows5 (sl K) :=
  mulM5_sound (canon l hl83) (canon r hr83) (mulE h2 hK ho hl hr)

theorem spec_of {o n : Nat} {R : Nat → Nat}
    (h : allN n (fun u => bAnd(Nat.beq (HNT.OP (o + u + 2)) 0,
      bAnd(Nat.beq (HNT.L (o + u + 2)) (o + u + 1), Nat.beq (HNT.R (o + u + 2)) (R u)))) = true)
    (u : Nat) (hu : u < n) :
    HNT.OP (o + u + 2) = 0 ∧ HNT.L (o + u + 2) = o + u + 1 ∧ HNT.R (o + u + 2) = R u := by
  have := allN_spec h u hu
  obtain ⟨a, bc⟩ := (bAnd_iff _ _).1 this
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 bc
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩

theorem pow_eq {m o e : Nat} (he : 1 ≤ e) (hm : m < 83) (hoe : o + e < 83) (h2 : 2 ≤ o + 1)
    (hc : HNT.OP (o + 1) = 1 ∧ HNT.L (o + 1) = m)
    (hs : allN (e - 1) (fun u => bAnd(Nat.beq (HNT.OP (o + u + 2)) 0,
      bAnd(Nat.beq (HNT.L (o + u + 2)) (o + u + 1), Nat.beq (HNT.R (o + u + 2)) m))) = true) :
    powM 5 133 (rows5 (sl m)) e = rows5 (sl (o + e)) := by
  refine powM5_chain (M := sl m) (P := fun t => sl (o + t)) he (canon m hm)
    (fun t _ ht => canon (o + t) (by omega)) (fun i hi => (copyE h2 (by omega) hc.1 hc.2 i hi).symm)
    (fun t h1 ht i hi => ?_)
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  obtain ⟨a, b, c⟩ := spec_of (R := fun _ => m) hs u (by omega)
  have := mulE (by omega) (by omega) a b c i hi
  have e1 : o + (u + 1) = o + u + 1 := by omega
  simp only [e1]
  exact this

theorem ltc_one : ltc 1 = 0 := rfl

theorem ltc_two : ltc 2 = 1 := rfl

theorem word_eq {w : List Nat} {o : Nat} (hn1 : 1 ≤ w.length) (hon : o + w.length < 83)
    (h2 : 2 ≤ o + 1) (hmem : ∀ l ∈ w, l = 1 ∨ l = 2)
    (hc : HNT.OP (o + 1) = 1 ∧ HNT.L (o + 1) = ltc (w.headD 0))
    (hs : allN (w.length - 1) (fun u => bAnd(Nat.beq (HNT.OP (o + u + 2)) 0,
      bAnd(Nat.beq (HNT.L (o + u + 2)) (o + u + 1),
        Nat.beq (HNT.R (o + u + 2)) (ltc (w.getD (u + 1) 0))))) = true) :
    wordM (seedSel (rows5 (sl 0)) (rows5 (sl 1))) w = rows5 (sl (o + w.length)) := by
  have hl83 : ∀ l ∈ w, ltc l < 83 := fun l hl => by
    rcases hmem l hl with rfl | rfl <;> decide
  refine wordM5_chain (LT := fun l => sl (ltc l)) (Q := fun t => sl (o + t)) hn1
    (fun l hl => ?_) (fun l hl => canon (ltc l) (hl83 l hl)) (fun t _ ht => canon (o + t) (by omega))
    (fun i hi => (copyE h2 (by omega) hc.1 hc.2 i hi).symm) (fun t h1 ht i hi => ?_)
  · rcases hmem l hl with rfl | rfl
    · rfl
    · rfl
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    obtain ⟨a, b, c⟩ := spec_of (R := fun u => ltc (w.getD (u + 1) 0)) hs u (by omega)
    have := mulE (by omega) (by omega) a b c i hi
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

theorem notId {k : Nat} (hk : k < 83)
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

theorem allN_le {f : Nat → Bool} {n m : Nat} (h : allN n f = true) (hm : m ≤ n) :
    allN m f = true :=
  CFSG.KS.Raw.allN_of_forall fun i hi => allN_spec h i (by omega)

theorem cA : allN 1 (fun u => bAnd(Nat.beq (HNT.OP (1 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (1 + u + 2)) (1 + u + 1), Nat.beq (HNT.R (1 + u + 2)) 0))) = true := by quickRfl
theorem cB : allN 2 (fun u => bAnd(Nat.beq (HNT.OP (3 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (3 + u + 2)) (3 + u + 1), Nat.beq (HNT.R (3 + u + 2)) 1))) = true := by quickRfl
theorem cAB : allN 21 (fun u => bAnd(Nat.beq (HNT.OP (7 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (7 + u + 2)) (7 + u + 1), Nat.beq (HNT.R (7 + u + 2)) 7))) = true := by quickRfl
theorem cX : allN 18 (fun u => bAnd(Nat.beq (HNT.OP (63 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (63 + u + 2)) (63 + u + 1), Nat.beq (HNT.R (63 + u + 2)) 63))) = true := by
  quickRfl
theorem cG : allN 11 (fun u => bAnd(Nat.beq (HNT.OP (29 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (29 + u + 2)) (29 + u + 1),
      Nat.beq (HNT.R (29 + u + 2)) (ltc (gWord.getD (u + 1) 0))))) = true := by quickRfl
theorem cGi : allN 17 (fun u => bAnd(Nat.beq (HNT.OP (41 + u + 2)) 0,
    bAnd(Nat.beq (HNT.L (41 + u + 2)) (41 + u + 1),
      Nat.beq (HNT.R (41 + u + 2)) (ltc (gInvWord.getD (u + 1) 0))))) = true := by quickRfl

theorem facts : seedChecks rowsA rowsB = true := by
  have hA2 : powM 5 133 (rows5 (sl 0)) 2 = rows5 (sl 3) :=
    pow_eq (o := 1) (by omega) (by omega) (by omega) (by omega) ⟨rfl, rfl⟩ cA
  have hB3 : powM 5 133 (rows5 (sl 1)) 3 = rows5 (sl 6) :=
    pow_eq (o := 3) (by omega) (by omega) (by omega) (by omega) ⟨rfl, rfl⟩ cB
  have hAB : mulM 5 133 (rows5 (sl 0)) (rows5 (sl 1)) = rows5 (sl 7) :=
    mul_eq (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
  have hP : ∀ e, 1 ≤ e → e ≤ 22 → powM 5 133 (rows5 (sl 7)) e = rows5 (sl (7 + e)) :=
    fun e h1 h22 => pow_eq (o := 7) h1 (by omega) (by omega) (by omega) ⟨rfl, rfl⟩
      (allN_le cAB (by omega))
  have hG : wordM (seedSel (rows5 (sl 0)) (rows5 (sl 1))) gWord = rows5 (sl 41) :=
    word_eq (o := 29) (by decide) (by decide) (by omega) (by decide) ⟨rfl, rfl⟩ cG
  have hGi : wordM (seedSel (rows5 (sl 0)) (rows5 (sl 1))) gInvWord = rows5 (sl 59) :=
    word_eq (o := 41) (by decide) (by decide) (by omega) (by decide) ⟨rfl, rfl⟩ cGi
  have hGGi : mulM 5 133 (rows5 (sl 41)) (rows5 (sl 59)) = rows5 (sl 60) :=
    mul_eq (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
  have hX1 : mulM 5 133 (rows5 (sl 0)) (rows5 (sl 59)) = rows5 (sl 61) :=
    mul_eq (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
  have hX2 : mulM 5 133 (rows5 (sl 61)) (rows5 (sl 1)) = rows5 (sl 62) :=
    mul_eq (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
  have hX3 : mulM 5 133 (rows5 (sl 62)) (rows5 (sl 41)) = rows5 (sl 63) :=
    mul_eq (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
  have hX19 : powM 5 133 (rows5 (sl 63)) 19 = rows5 (sl 82) :=
    pow_eq (o := 63) (by omega) (by omega) (by omega) (by omega) ⟨rfl, rfl⟩ cX
  unfold seedChecks
  dsimp only
  rw [rowsA_eq, rowsB_eq, hA2, hB3, hAB, hP 22 (by omega) (by omega), hP 11 (by omega) (by omega),
    hP 2 (by omega) (by omega), hG, hGi, hGGi, hX1, hX2, hX3, hX19]
  rw [isId id3, isId id6, isId id29, isId id60, isId id82, notId (by omega) ne0,
    notId (by omega) ne1, notId (by omega) ne18, notId (by omega) ne9, notId (by omega) ne63]
  rfl

end CertificateChecks.KernelSporSch.HNSeeds

end
