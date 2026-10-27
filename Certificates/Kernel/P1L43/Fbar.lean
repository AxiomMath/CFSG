module

public import Certificates.Kernel.P1L43.Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1FbarRows
import Init.Data.Nat.Fold
import Init.Data.Range.Basic

set_option maxRecDepth 400000

public section


namespace CertificateChecks.KernelP1L43

open CFSG.ComponentClassification.HarrisLit CFSG.ComponentClassification.HarrisLit.P1
  CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.ArrEnum CFSG.KC.OrbFind
  CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Certificates Subgroup
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "𝒞" t:max => (pi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 80))))

theorem fbinds :
    bindT (tm 22222087) (LD0.G 0) = true ∧ bindT (tm 30806896) (LD0.G 1) = true ∧
    bindT (tm 28947042) (LDS2.G 0) = true ∧ bindT (tm 5634355) (LDS2.G 1) = true ∧
    bindT (tm 18085123) (KD2.G 0) = true ∧ bindT (tm 27169507) (KD2.G 1) = true ∧
    bindT (tm 17897863) (FS3.G 0) = true ∧ bindT (tm 17928943) (FS3.G 1) = true ∧
    bindT (tm 2221498) (FS4.G 0) = true ∧ bindT (tm 41267271) (FS4.G 1) = true ∧
    LD0.ng = 2 ∧ LDS2.ng = 2 ∧ KD2.ng = 2 ∧ FS3.ng = 2 ∧ FS4.ng = 2 := by
  decide +kernel

theorem bind_gen {T : Table} {ng k : ℕ} {G GI : ℕ → ℕ} (hh : headK 80 7 ng G GI = true)
    (hk : k < ng) (hb : bindT T (G k) = true) :
    tp 80 T = pp (G k) ∧ CFSG.Sporadic.Th.Rep 80 T (tp 80 T) := by
  obtain ⟨e, h⟩ := tp_of_bind hb (prep_gen hh k hk).1
  refine ⟨e, ?_⟩
  rw [e]
  exact h

theorem genOf_pair {a b : Table} {ng : ℕ} {G : ℕ → ℕ} (hng : ng = 2) (ha : tp 80 a = pp (G 0))
    (hb : tp 80 b = pp (G 1)) :
    genOf 80 [a, b] = closure ((fun k => pp (G k)) '' {k | k < ng}) := by
  rw [hng, img2, genOf]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl | rfl, rfl⟩
    · exact Or.inl ha
    · exact Or.inr hb
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨b, Or.inr rfl, hb⟩

theorem fbar_inner {r : Row} {first : Bool} (hk : r.kind = .inner) (hout : r.row.outer = false)
    (hf : first = false) : FbarRowFacts pi.range first r := by
  simp only [FbarRowFacts, hk]
  exact ⟨hout, hf⟩

theorem fbar_noFive {r : Row} {first : Bool} {t : Equiv.Perm (Fin 80)} (hk : r.kind = .noFive)
    (ht : tp 80 r.row.rep = t) (h5 : ¬ 5 ∣ Nat.card ↥(𝒞 t)) : FbarRowFacts pi.range first r := by
  simp only [FbarRowFacts, hk, ht]
  exact h5

theorem fbar_small {r : Row} {first : Bool} {gs : List Table} {ord : ℕ}
    {t : Equiv.Perm (Fin 80)} {K : Subgroup (Equiv.Perm (Fin 80))}
    (hk : r.kind = .small gs ord) (ht : tp 80 r.row.rep = t) (hK : genOf 80 gs = K)
    (hrep : ∀ g ∈ gs, CFSG.Sporadic.Th.Rep 80 g (tp 80 g)) (h5 : ¬ 5 ∣ Nat.card ↥(𝒞 t))
    (hle : K ≤ 𝒞 t) (hN : 𝒞 t ≤ normalizer (K : Set (Equiv.Perm (Fin 80)))) :
    FbarRowFacts pi.range first r := by
  simp only [FbarRowFacts, hk, ht, hK]
  exact ⟨h5, hrep, hle, hN⟩

theorem fbar_five {r : Row} {first : Bool} {gs : List Table} {ord : ℕ}
    {t : Equiv.Perm (Fin 80)} {K : Subgroup (Equiv.Perm (Fin 80))}
    (hk : r.kind = .five gs ord) (ht : tp 80 r.row.rep = t) (hK : genOf 80 gs = K)
    (hgs : ∀ g ∈ gs, tp 80 g ∈ 𝒞 t ∧ orderOf (tp 80 g) = 5) (hc : Nat.card ↥K = ord) :
    FbarRowFacts pi.range first r := by
  simp only [FbarRowFacts, hk, ht, hK]
  exact ⟨hgs, hc⟩

theorem fbar_a6 {r : Row} {first : Bool} {l₁ l₂ : Table} {w : List (Option Table)}
    {t : Equiv.Perm (Fin 80)} {L : Subgroup (Equiv.Perm (Fin 80))} {Lp : ℕ → ℕ}
    (hk : r.kind = .a6 l₁ l₂ w) (ht : tp 80 r.row.rep = t) (hL : genOf 80 [l₁, l₂] = L)
    (h₁ : CFSG.Sporadic.Th.Rep 80 l₁ (tp 80 l₁)) (h₂ : CFSG.Sporadic.Th.Rep 80 l₂ (tp 80 l₂))
    (hF : A6F t L Lp) : FbarRowFacts pi.range first r := by
  subst hL
  simp only [FbarRowFacts, hk, ht]
  exact ⟨h₁, h₂, hF.le, hF.norm, hF.pow, hF.iso⟩

theorem five_ord {P ng : ℕ} {G GI : ℕ → ℕ} (hsi : selfInv P = true)
    (hf : allN ng (fun k => bAnd(sP (G k), bAnd(cm (G k) P, ord5K 80 7 (G k)))) = true)
    (hh : headK 80 7 ng G GI = true) {k : ℕ} (hk : k < ng) :
    pp (G k) ∈ 𝒞 (pp P) ∧ orderOf (pp (G k)) = 5 := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hf k hk
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  have hG := (prep_gen hh k hk).1
  have h5 := ord5K_spec hn80 hG h.2.2
  exact ⟨mem_inf.2 ⟨mem_of_sP hG h.1,
    mem_centralizer_singleton_iff.2 (comm_of_cm hG (prep_si hsi) h.2.1)⟩,
    orderOf_eq_prime h5.1 h5.2⟩

theorem five_pair {a b : Table} {P ng : ℕ} {G GI : ℕ → ℕ} (hsi : selfInv P = true)
    (hf : allN ng (fun k => bAnd(sP (G k), bAnd(cm (G k) P, ord5K 80 7 (G k)))) = true)
    (hh : headK 80 7 ng G GI = true) (hng : ng = 2) (ha : tp 80 a = pp (G 0))
    (hb : tp 80 b = pp (G 1)) :
    ∀ g ∈ [a, b], tp 80 g ∈ 𝒞 (pp P) ∧ orderOf (tp 80 g) = 5 := by
  intro g hg
  rcases List.mem_pair.mp hg with rfl | rfl
  · rw [ha]
    exact five_ord hsi hf hh (by omega)
  · rw [hb]
    exact five_ord hsi hf hh (by omega)

theorem l43_fbarRows : ∀ i < l43Runs.length, ∀ r ∈ (l43Runs.getD i default).rows,
    FbarRowFacts pi.range (i == 0) r := by
  obtain ⟨-, -, -, -, -, -, -, a0, -, -, f0, -, -, k1080, k10530, k117a, k117b, k8424, -⟩ :=
    binds
  obtain ⟨bl1, bl2, bm1, bm2, bk1, bk2, bf1, bf2, bg1, bg2, nL, nM, nK, nF, nG⟩ := fbinds
  have l1 := bind_gen LD0.h (by omega) bl1
  have l2 := bind_gen LD0.h (by omega) bl2
  have m1 := bind_gen LDS2.h (by omega) bm1
  have m2 := bind_gen LDS2.h (by omega) bm2
  have k1 := bind_gen KD2.h (by omega) bk1
  have k2 := bind_gen KD2.h (by omega) bk2
  have g1 := bind_gen FS3.h (by omega) bf1
  have g2 := bind_gen FS3.h (by omega) bf2
  have h1 := bind_gen FS4.h (by omega) bg1
  have h2 := bind_gen FS4.h (by omega) bg2
  intro i hi r hr
  have hl : l43Runs.length = 3 := rfl
  rw [hl] at hi
  interval_cases i
  · change r ∈ runuD.rows at hr
    simp only [runuD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fbar_a6 rfl (tpR a0 (si (by simp))) (genOf_pair nL l1.1 l2.1) l1.2 l2.2 fD0
    · exact fbar_noFive rfl (tpR k1080 (si (by simp)))
        (by rw [card_of_cls c1080.2.1 (M := 5616) (by decide)]; decide)
    · have hgK := gf KD2.h (fun i hi => KD2.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => KD2.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
        KD2.k
      obtain ⟨hle, hN⟩ := norm_facts (si (by simp)) smallK KD2.h hgK.2.2 CD2.h
      rw [centD2.1] at hN
      refine fbar_small rfl (tpR f0 (si (by simp))) (genOf_pair nK k1.1 k2.1) ?_
        (by rw [centD2.2]; decide) hle hN
      intro g hg
      rcases List.mem_pair.mp hg with rfl | rfl
      · exact k1.2
      · exact k2.2
  · change r ∈ runuS.rows at hr
    simp only [runuS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact fbar_inner rfl rfl rfl
    · exact fbar_noFive rfl (tpR k10530 (si (by simp)))
        (by rw [card_of_cls c10530.2.1 (M := 576) (by decide)]; decide)
    · exact fbar_inner rfl rfl rfl
    · have hg := gf FS3.h (fun i hi => FS3.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => FS3.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
        FS3.k
      exact fbar_five rfl (tpR k117a (si (by simp))) (genOf_pair nF g1.1 g2.1)
        (five_pair (si (by simp)) fiveK.1 FS3.h nF g1.1 g2.1) hg.1
    · have hg := gf FS4.h (fun i hi => FS4.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => FS4.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
        FS4.k
      exact fbar_five rfl (tpR k117b (si (by simp))) (genOf_pair nG h1.1 h2.1)
        (five_pair (si (by simp)) fiveK.2 FS4.h nG h1.1 h2.1) hg.1
  · change r ∈ runuDS.rows at hr
    simp only [runuDS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fbar_inner rfl rfl rfl
    · exact fbar_inner rfl rfl rfl
    · exact fbar_a6 rfl (tpR k8424 (si (by simp))) (genOf_pair nM m1.1 m2.1) m1.2 m2.2 fDS2

end CertificateChecks.KernelP1L43

end
