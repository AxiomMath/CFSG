module

public import Certificates.Kernel.EvenSporCSide.Conj

public section

namespace CertificateChecks.KernelCSide

open CFSG.EvenSporadicStandard.HNRecog.CSide

set_option maxHeartbeats 0 in
theorem k6a : cSideK6a := by decide +kernel

set_option maxHeartbeats 0 in
theorem k6c : cSideK6c := by decide +kernel

set_option maxHeartbeats 0 in
theorem k4a : cSideK4a := by decide +kernel

set_option maxHeartbeats 0 in
theorem k4d : cSideK4d := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep4b : cSideRep4b := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep4c : cSideRep4c := by decide +kernel

set_option maxHeartbeats 0 in
theorem cls3 : ∀ a : SL2, a ^ 3 = 1 → a ≠ 1 → ∃ h : SL2, h * r3 = a * h := by decide +kernel

set_option maxHeartbeats 0 in
theorem cls2 : ∀ a : SL2, a ^ 2 = 1 → a ≠ 1 → ∃ h : SL2, h * t2 = a * h := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep2 : cSideGood2 (cSideFixC (r3, r3)) := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep3a : (cSideFixC (t2, 1)).card = 16 := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep3b : (cSideFixC (1, t2)).card = 16 := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep3c : (cSideFixC (t2, t2)).card = 16 := by decide +kernel

theorem k3 : cSideK3 := by
  intro g h2 hg
  have e1 : g.1 ^ 2 = 1 := by rw [← Prod.pow_fst, h2, Prod.fst_one]
  have e2 : g.2 ^ 2 = 1 := by rw [← Prod.pow_snd, h2, Prod.snd_one]
  have one_cls : ∀ a : SL2, a = 1 → (1 : SL2) * 1 = a * 1 := fun a ha => by rw [ha]
  by_cases a1 : g.1 = 1
  · have b1 : g.2 ≠ 1 := fun hb => hg (Prod.ext a1 hb)
    obtain ⟨k, ek⟩ := cls2 _ e2 b1
    rw [← prod_conj (one_cls _ a1) ek, card_fix_conj, ← cSideFixC_eq]
    exact rep3b
  · obtain ⟨h, eh⟩ := cls2 _ e1 a1
    by_cases b1 : g.2 = 1
    · rw [← prod_conj eh (one_cls _ b1), card_fix_conj, ← cSideFixC_eq]
      exact rep3a
    · obtain ⟨k, ek⟩ := cls2 _ e2 b1
      rw [← prod_conj eh ek, card_fix_conj, ← cSideFixC_eq]
      exact rep3c

set_option maxHeartbeats 0 in
theorem cls5 : ∀ a : SL2, a ^ 5 = 1 → a ≠ 1 → ∃ h : SL2, h * r5 = a * h ∨ h * r5b = a * h := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem rep1a : cSideZeroOn (cSideFixC (r3, 1)) := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep1b : cSideZeroOn (cSideFixC (r5, 1)) := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep1c : cSideZeroOn (cSideFixC (r5b, 1)) := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep1d : cSideZeroOn (cSideFixC (1, r3)) := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep1e : cSideZeroOn (cSideFixC (1, r5)) := by decide +kernel

set_option maxHeartbeats 0 in
theorem rep1f : cSideZeroOn (cSideFixC (1, r5b)) := by decide +kernel

theorem cls35 {a : SL2} (ha : a ^ 3 = 1 ∨ a ^ 5 = 1) (hne : a ≠ 1) :
    ∃ h r : SL2, h * r = a * h ∧ (r = r3 ∨ r = r5 ∨ r = r5b) := by
  rcases ha with ha | ha
  · obtain ⟨h, eh⟩ := cls3 a ha hne
    exact ⟨h, r3, eh, Or.inl rfl⟩
  · obtain ⟨h, eh | eh⟩ := cls5 a ha hne
    · exact ⟨h, r5, eh, Or.inr (Or.inl rfl)⟩
    · exact ⟨h, r5b, eh, Or.inr (Or.inr rfl)⟩

theorem k1 : cSideK1 := by
  intro g ho hg h1
  have one_cls : ∀ a : SL2, a = 1 → (1 : SL2) * 1 = a * 1 := fun a ha => by rw [ha]
  rcases h1 with a1 | b1
  · have hne : g.2 ≠ 1 := fun hb => hg (Prod.ext a1 hb)
    have ho2 : g.2 ^ 3 = 1 ∨ g.2 ^ 5 = 1 := by
      rcases ho with e | e
      · exact Or.inl (by rw [← Prod.pow_snd, e, Prod.snd_one])
      · exact Or.inr (by rw [← Prod.pow_snd, e, Prod.snd_one])
    obtain ⟨k, r, ek, hr⟩ := cls35 ho2 hne
    rw [← prod_conj (one_cls _ a1) ek]
    apply zero_conj
    refine (cSideZeroOn_fixC_iff _).1 ?_
    rcases hr with rfl | rfl | rfl
    · exact rep1d
    · exact rep1e
    · exact rep1f
  · have hne : g.1 ≠ 1 := fun ha => hg (Prod.ext ha b1)
    have ho1 : g.1 ^ 3 = 1 ∨ g.1 ^ 5 = 1 := by
      rcases ho with e | e
      · exact Or.inl (by rw [← Prod.pow_fst, e, Prod.fst_one])
      · exact Or.inr (by rw [← Prod.pow_fst, e, Prod.fst_one])
    obtain ⟨h, r, eh, hr⟩ := cls35 ho1 hne
    rw [← prod_conj eh (one_cls _ b1)]
    apply zero_conj
    refine (cSideZeroOn_fixC_iff _).1 ?_
    rcases hr with rfl | rfl | rfl
    · exact rep1a
    · exact rep1b
    · exact rep1c

theorem k2 : cSideK2 := by
  intro g h3 h1 h2
  have e1 : g.1 ^ 3 = 1 := by rw [← Prod.pow_fst, h3, Prod.fst_one]
  have e2 : g.2 ^ 3 = 1 := by rw [← Prod.pow_snd, h3, Prod.snd_one]
  obtain ⟨h, eh⟩ := cls3 _ e1 h1
  obtain ⟨k, ek⟩ := cls3 _ e2 h2
  rw [← prod_conj eh ek]
  have hr := (cSideGood2_fixC_iff (r3, r3)).1 rep2
  exact ⟨(card_fix_conj _ _).trans hr.1, nondeg_conj hr.2.1, plane_conj hr.2.2⟩

end CertificateChecks.KernelCSide
