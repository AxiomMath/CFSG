module

public import Certificates.Kernel.U43Mod.Sound
public import CFSG.Certificates.Kernel.U43Mod.GenSound
public import CFSG.Certificates.Kernel.U43Mod.BfsRecSound
public import CFSG.Certificates.Kernel.U43Mod.ArrSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Mod

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KS CFSG.KS.Raw CFSG.KS.U43Mod CFSG.Certificates
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CFSG.KGroups.U43 CFSG.Sporadic.SmallOddCore CFSG.LieType.Multipliers.U43 Subgroup

theorem rels5_letters : ∀ w ∈ rels5Codes, ∀ l ∈ w, l.1 < 5 := by decide +kernel

theorem rels4_letters : ∀ w ∈ rels4Codes, ∀ l ∈ w, l.1 < 4 := by decide +kernel

theorem cube_mem : [(1, true), (1, true), (1, true)] ∈ rels4Codes := by decide +kernel

@[expose] def commW : Word :=
  [(1, false), (2, false), (1, false), (2, true), (1, true), (2, false), (1, true), (2, true)]

theorem commW_mem : commW ∈ rels4Codes := by decide +kernel

theorem sW_letters : ∀ j, ∀ l ∈ sW.getD j [], l.1 < 4 := by
  intro j
  rcases Nat.lt_or_ge j 3 with hj | hj
  · interval_cases j <;> decide
  · rw [List.getD_eq_default _ _ (by simpa [sW] using hj)]
    simp

theorem surjB_letters : ∀ l ∈ surjB, l.1 < 5 := by decide

@[expose] noncomputable def m5 (i : ℕ) : Equiv.Perm (Fin 820) := evalG CP (gW.getD i [])

@[expose] noncomputable def m4 (i : ℕ) : Equiv.Perm (Fin 820) := if i < 4 then m5 i else 1

theorem m4_eq {i : ℕ} (hi : i < 4) : m4 i = m5 i := if_pos hi

theorem evalG_m4 {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 4) : evalG m4 w = evalG m5 w :=
  evalG_congr w fun l hl => m4_eq (hw l hl)


theorem CP_mem {i : ℕ} (hi : i < 2) : CP i ∈ P := by
  rw [P_eq_closure]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [CP_zero]
    exact subset_closure (by simp)
  · rw [CP_one]
    exact subset_closure (by simp)

theorem m5_mem (i : ℕ) : m5 i ∈ P :=
  evalG_mem _ fun l hl => CP_mem (gW_letters i l hl)

theorem evalG_m5_mem (w : List (ℕ × Bool)) : evalG m5 w ∈ P :=
  evalG_mem w fun l _ => m5_mem l.1

theorem eq_of_baseEq {x y : Equiv.Perm (Fin 820)} (hx : x ∈ P) (hy : y ∈ P) {f f' : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ))
    (hf' : ∀ q (hq : q < 820), f' q = (y ⟨q, hq⟩ : ℕ)) (h : baseEq bs f f' = true) : x = y :=
  eq_of_base hx hy fun p hp => Fin.ext (by rw [← hf, ← hf']; exact baseEq_iff.1 h p hp)

theorem baseEq_of_eq {x y : Equiv.Perm (Fin 820)} {f f' : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ))
    (hf' : ∀ q (hq : q < 820), f' q = (y ⟨q, hq⟩ : ℕ)) (h : x = y) : baseEq bs f f' = true :=
  baseEq_iff.2 fun p hp => by rw [hf p (bs_lt p hp), hf' p (bs_lt p hp), h]

theorem wv_GM (w : List (ℕ × Bool)) (q : ℕ) (hq : q < 820) :
    wv GM GMi w q = (evalG m5 w ⟨q, hq⟩ : ℕ) :=
  wv_eq w (fun l _ => letRep_GM l.1) q hq

theorem GA_eq {i : ℕ} (hi : i < 7) (q : ℕ) (hq : q < 820) : GA i q = (CP i ⟨q, hq⟩ : ℕ) :=
  (letRep_GA hi q hq).1

theorem GM_eq (i q : ℕ) (hq : q < 820) : GM i q = (m5 i ⟨q, hq⟩ : ℕ) :=
  (letRep_GM i q hq).1

theorem id_eq' (q : ℕ) (hq : q < 820) : (fun q => q) q = ((1 : Equiv.Perm (Fin 820)) ⟨q, hq⟩ : ℕ) :=
  rfl

theorem rel5 {r : List (ℕ × Bool)} (hr : r ∈ rels5Codes) : evalG m5 r = 1 := by
  refine eq_of_baseEq (evalG_m5_mem r) (P.one_mem) (wv_GM r) id_eq' ?_
  exact baseEq_iff.2 ((relsB_iff.1 kRel5) r hr)

theorem rel4 {r : List (ℕ × Bool)} (hr : r ∈ rels4Codes) : evalG m5 r = 1 := by
  refine eq_of_baseEq (evalG_m5_mem r) (P.one_mem) (wv_GM r) id_eq' ?_
  exact baseEq_iff.2 ((relsB_iff.1 kRel4) r hr)

theorem comm_m5 {i : ℕ} (hi : i < 4) : m5 i * CP 0 = CP 0 * m5 i := by
  refine eq_of_baseEq (P.mul_mem (m5_mem i) (CP_mem (by norm_num)))
    (P.mul_mem (CP_mem (by norm_num)) (m5_mem i)) (f := fun q => GM i (GA 0 q))
    (f' := fun q => GA 0 (GM i q)) (fun q hq => ?_) (fun q hq => ?_) (allN_spec kComm i hi)
  · rw [GA_eq (by norm_num) q hq, GM_eq i _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]
  · rw [GM_eq i q hq, GA_eq (by norm_num) _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]

theorem kAB_spec :baseEq bs (wv GM GMi [(0, false), (0, false)]) (GA 0) = true ∧
    baseEq bs (wv GM GMi surjB) (GA 1) = true := by
  have h := kAB
  rwa [Bool.and_eq_true] at h

theorem m5_a : evalG m5 [(0, false), (0, false)] = CP 0 :=
  eq_of_baseEq (evalG_m5_mem _) (CP_mem (by norm_num)) (wv_GM _) (GA_eq (by norm_num)) kAB_spec.1

theorem m5_b : evalG m5 surjB = CP 1 :=
  eq_of_baseEq (evalG_m5_mem _) (CP_mem (by norm_num)) (wv_GM _) (GA_eq (by norm_num)) kAB_spec.2

theorem kTabA_spec :baseEq bs (fun q => GA 0 (GA 0 q)) (fun q => q) = true ∧
    baseEq bs (GA 0) (fun q => q) = false := by
  have h := kTabA
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

theorem CP0_sq : CP 0 * CP 0 = 1 := by
  refine eq_of_baseEq (P.mul_mem (CP_mem (by norm_num)) (CP_mem (by norm_num))) P.one_mem
    (fun q hq => ?_) id_eq' kTabA_spec.1
  rw [GA_eq (by norm_num) q hq, GA_eq (by norm_num) _ (Fin.is_lt _), Fin.eta,
    Equiv.Perm.mul_apply]

theorem CP0_ne : CP 0 ≠ 1 := fun e => by
  have h : baseEq bs (GA 0) (fun q => q) = true := baseEq_iff.2 fun p hp => by
    rw [GA_eq (by norm_num) p (bs_lt p hp), e]
    rfl
  rw [kTabA_spec.2] at h
  exact Bool.false_ne_true h

theorem baseEq_true_of_eq {x y : Equiv.Perm (Fin 820)} {f f' : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ))
    (hf' : ∀ q (hq : q < 820), f' q = (y ⟨q, hq⟩ : ℕ)) (h : x = y) : baseEq bs f f' = true :=
  baseEq_iff.2 fun p hp => by rw [hf p (bs_lt p hp), hf' p (bs_lt p hp), h]

theorem kSig_spec : baseEq bs (GM 1) (fun q => q) = false ∧
    baseEq bs (wv GM GMi sig2W) (fun q => q) = false ∧
    baseEq bs (wv GM GMi sig2W) (GM 1) = false ∧
    baseEq bs (wv GM GMi sig2W) (wv GM GMi [(1, true), (1, true)]) = false := by
  have h := kSig
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ne_of_baseEq {x y : Equiv.Perm (Fin 820)} {f f' : ℕ → ℕ}
    (hf : ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ))
    (hf' : ∀ q (hq : q < 820), f' q = (y ⟨q, hq⟩ : ℕ)) (h : baseEq bs f f' = false) : x ≠ y :=
  fun e => by
    rw [baseEq_true_of_eq hf hf' e] at h
    exact Bool.noConfusion h

theorem SP_eq {j : ℕ} (hj : j < 3) : SP j = evalG m5 (sW.getD j []) := by
  refine eq_of_baseEq (SP_mem hj) (evalG_m5_mem _) (GS_eq hj) (fun q hq => ?_) (kST_spec hj).2.2
  exact (letRep_wG (W := sW) (i := j) (fun l _ => letRep_GM l.1) q hq).1

section Class


theorem classA : conjClass P (CP 0) = conjClass P (rP 2) := by
  have hm : CP 0 ∈ InvCoset 0 := ⟨CP 0, CP_mem (by norm_num), by rw [tP_zero, mul_one], CP0_sq⟩
  rcases cover_coset_zero hm with h | h
  · exfalso
    obtain ⟨g, -, hg⟩ := h
    exact CP0_ne (by rw [hg]; group)
  · exact conjClass_eq_of_mem (self_mem_conjClass P (CP 0)) h

theorem ncard_classA : (conjClass P (CP 0)).ncard = 2835 := by
  rw [classA]
  exact ncard_class (c := 1152) (by norm_num) (by decide) (by norm_num)

theorem card_CA : Nat.card ↥(P ⊓ centralizer ({CP 0} : Set (Equiv.Perm (Fin 820)))) = 1152 := by
  have h := ncard_conjClass_mul_card P (CP 0)
  rw [ncard_classA, card_P] at h
  omega

theorem invol_mem_classA {x : Equiv.Perm (Fin 820)} (hx : x ∈ P) (h2 : x * x = 1) (h1 : x ≠ 1) :
    x ∈ conjClass P (CP 0) := by
  rcases cover_coset_zero ⟨x, hx, by rw [tP_zero, mul_one], h2⟩ with h | h
  · exfalso
    obtain ⟨g, -, hg⟩ := h
    exact h1 (by rw [hg]; group)
  · rwa [classA]

@[expose] noncomputable def H4 : Subgroup (Equiv.Perm (Fin 820)) := closure (m4 '' Set.Iio 4)

theorem m4_mem_H4 {j : ℕ} (hj : j < 4) : m4 j ∈ H4 := subset_closure ⟨j, hj, rfl⟩

theorem evalG_mem_H4 {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 4) : evalG m5 w ∈ H4 := by
  rw [← evalG_m4 hw]
  exact evalG_mem w fun l hl => m4_mem_H4 (hw l hl)

theorem H4_le : H4 ≤ P ⊓ centralizer ({CP 0} : Set (Equiv.Perm (Fin 820))) := by
  rw [H4, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj : j < 4 := hj
  refine mem_inf.2 ⟨by rw [m4_eq hj]; exact m5_mem j, ?_⟩
  rw [mem_centralizer_singleton_iff, m4_eq hj]
  exact comm_m5 hj

theorem H4_le_P : H4 ≤ P := H4_le.trans inf_le_left

theorem Ssub_le : closure (SP '' Set.Iio 3) ≤ H4 := by
  rw [closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj : j < 3 := hj
  rw [SetLike.mem_coe, SP_eq hj]
  exact evalG_mem_H4 (sW_letters j)

theorem sig_facts : m5 1 ^ 3 = 1 ∧ m5 1 * evalG m5 sig2W = evalG m5 sig2W * m5 1 := by
  have h3 := rel4 cube_mem
  have hc := rel4 commW_mem
  simp only [evalG, commW, sig2W, List.map, letterVal, List.prod_cons, List.prod_nil,
    if_true, if_false, Bool.false_eq_true, ↓reduceIte, mul_one] at h3 hc ⊢
  refine ⟨by rw [pow_three]; exact h3, ?_⟩
  set s := m5 1
  set u := m5 2
  calc s * (u⁻¹ * (s * u)) = u⁻¹ * (s * u) * s *
        (s⁻¹ * (u⁻¹ * (s⁻¹ * (u * (s * (u⁻¹ * (s * u))))))) := by group
    _ = u⁻¹ * (s * u) * s := by rw [hc, mul_one]

theorem card_H4 : Nat.card H4 = 1152 := by
  obtain ⟨h3, hst⟩ := sig_facts
  have hs : m5 1 ∈ H4 := by rw [← m4_eq (by norm_num)]; exact m4_mem_H4 (by norm_num)
  have ht : evalG m5 sig2W ∈ H4 := evalG_mem_H4 (by decide)
  have ht3 : evalG m5 sig2W ^ 3 = 1 := by
    simp only [evalG, sig2W, List.map, letterVal, List.prod_cons, List.prod_nil, if_true,
      Bool.false_eq_true, ↓reduceIte, mul_one]
    have e : ((m5 2)⁻¹ * (m5 1 * m5 2)) ^ 3 = (m5 2)⁻¹ * m5 1 ^ 3 * m5 2 := by
      simp only [pow_three]
      group
    rw [e, h3]
    group
  obtain ⟨k1, k2, k3, k4⟩ := kSig_spec
  have hs1 : m5 1 ≠ 1 := ne_of_baseEq (GM_eq 1) id_eq' k1
  have ht1 : evalG m5 sig2W ≠ 1 := ne_of_baseEq (wv_GM _) id_eq' k2
  have ht2 : evalG m5 sig2W ≠ m5 1 := ne_of_baseEq (wv_GM _) (GM_eq 1) k3
  have ht4 : evalG m5 sig2W ≠ m5 1 * m5 1 := by
    have h := ne_of_baseEq (wv_GM _) (wv_GM _) k4
    simpa [evalG, letterVal] using h
  have h9 := nine_dvd_card hs ht h3 hs1 ht3 hst ht1 ht2 ht4
  have h128 : 128 ∣ Nat.card H4 := by
    rw [← card_Ssub]
    exact card_dvd_of_le Ssub_le
  have hd : 1152 ∣ Nat.card H4 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 128 9) h128 h9
  have hle : Nat.card H4 ≤ 1152 := by
    rw [← card_CA]
    exact card_le_of_le H4_le
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hd)

end Class

theorem rep_A : Rep 820 tabA (CP 0) := CP_zero ▸ rep_tabA

theorem gAB_eq {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 2) :
    evalG (fun i => if i = 0 then psi xElt else psi yElt) w = evalG CP w := by
  refine evalG_congr w fun l hl => ?_
  rcases (by have := hw l hl; omega : l.1 = 0 ∨ l.1 = 1) with h | h <;> simp [h, CP_zero, CP_one]

theorem arrAB {j : ℕ} (hj : j < 2) :
    Rep 820 (genAB tabA tabB)[j]! (CP j) ∧ Rep 820 (invArrs 820 (genAB tabA tabB))[j]! (CP j)⁻¹ := by
  have h := arrRep_genAB rep_tabA rep_tabB hj
  have e : (if j = 0 then psi xElt else psi yElt) = CP j := by
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [CP_zero, CP_one]
  rw [ArrRep, e] at h
  exact h

theorem invsOK_AB : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true :=
  invsOK_invArrs fun _ hi => ⟨_, (arrAB hi).1⟩

theorem rep_wArr' {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 2) :
    Rep 820 (wArr 820 tabA tabB w) (evalG CP w) := by
  rw [← gAB_eq hw]
  exact rep_wArr rep_tabA rep_tabB hw

theorem rep_gens {last : Array ℕ} {gl : Equiv.Perm (Fin 820)} (hl : Rep 820 last gl) {i : ℕ}
    (hi : i < 5) :
    Rep 820 (gensWith 820 tabA tabB last)[i]! (if i < 4 then m5 i else gl) := by
  interval_cases i
  · exact rep_wArr' (gW_letters 0)
  · exact rep_wArr' (gW_letters 1)
  · exact rep_wArr' (gW_letters 2)
  · exact rep_wArr' (gW_letters 3)
  · exact hl

theorem arrM {i : ℕ} (hi : i < 5) :
    ArrRep 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))
      (invArrs 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))) m5 i := by
  have h : Rep 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))[i]! (m5 i) := by
    have := rep_gens (rep_wArr' (w := wordPhi) (gW_letters 4)) hi
    have e : (if i < 4 then m5 i else evalG CP wordPhi) = m5 i := by
      split_ifs with h4
      · rfl
      · have : i = 4 := by omega
        subst this
        rfl
    rwa [e] at this
  exact ⟨h, rep_invArrs hi h⟩

theorem arrE {i : ℕ} (hi : i < 5) :
    ArrRep 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) m4 i := by
  have h : Rep 820 (hGens 820 tabA tabB)[i]! (m4 i) := rep_gens rep_idA hi
  exact ⟨h, rep_invArrs hi h⟩

theorem rep_evalE {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 4) :
    Rep 820 (evalArr 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) w)
      (evalG m5 w) := by
  rw [← evalG_m4 hw]
  exact rep_evalArr w fun l hl => arrE (by have := hw l hl; omega)

theorem sylGens_get {j : ℕ} (hj : j < 3) : (sylGens 820 tabA tabB)[j]! =
    evalArr 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) (sW.getD j []) := by
  interval_cases j <;> rfl

theorem rep_S {j : ℕ} (hj : j < 3) : Rep 820 (sylGens 820 tabA tabB)[j]! (SP j) := by
  rw [sylGens_get hj, SP_eq hj]
  exact rep_evalE (sW_letters j)

theorem key_iff {t t' : Array ℕ} {a a' : Equiv.Perm (Fin 820)} (ht : Rep 820 t a)
    (ht' : Rep 820 t' a') (ha : a ∈ P) (ha' : a' ∈ P) : keyOf t = keyOf t' ↔ a = a' := by
  constructor
  · intro e
    simp only [keyOf, Prod.mk.injEq] at e
    obtain ⟨e0, e1, e9⟩ := e
    refine eq_of_base ha ha' fun p hp => Fin.ext ?_
    simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [← ht.apply, ← ht'.apply]
      exact e0
    · rw [← ht.apply, ← ht'.apply]
      exact e1
    · rw [← ht.apply, ← ht'.apply]
      exact e9
  · rintro rfl
    simp only [keyOf, ht.apply (by norm_num : 0 < 820), ht'.apply (by norm_num : 0 < 820),
      ht.apply (by norm_num : 1 < 820), ht'.apply (by norm_num : 1 < 820),
      ht.apply (by norm_num : 9 < 820), ht'.apply (by norm_num : 9 < 820)]

section Lists


theorem orb_enum : (orbRec 820 tabA tabB).L.size = 2835 ∧
    (∀ i < (orbRec 820 tabA tabB).L.size,
      ∃ x ∈ conjClass P (CP 0), Rep 820 (orbRec 820 tabA tabB).L[i]! x) ∧
    ∀ x ∈ conjClass P (CP 0), ∃ i < (orbRec 820 tabA tabB).L.size,
      Rep 820 (orbRec 820 tabA tabB).L[i]! x := by
  have hXP : ∀ x ∈ conjClass P (CP 0), x ∈ P := by
    rintro _ ⟨c, hc, rfl⟩
    exact P.mul_mem (P.mul_mem hc (CP_mem (by norm_num))) (P.inv_mem hc)
  have h := bfsRec_enum (step := conjStep 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)))
    (k := 2) (cap := 3000) (x0 := tabA) (Rep 820) (conjClass P (CP 0))
    (fun j a => CP j * (a * (CP j)⁻¹)) (CP 0) (Set.toFinite _) rep_A (self_mem_conjClass P _)
    (fun t a ht ha j hj => by
      refine ⟨rep_compA (arrAB hj).1 (rep_compA ht (arrAB hj).2), ?_⟩
      obtain ⟨c, hc, rfl⟩ := ha
      exact ⟨CP j * c, P.mul_mem (CP_mem hj) hc, by group⟩)
    (fun t t' a a' ht ht' ha ha' => key_iff ht ht' (hXP a ha) (hXP a' ha'))
    (fun Y h0 hY => by
      rintro _ ⟨c, hc, rfl⟩
      rw [P_eq_closure, ← CP_zero, ← CP_one] at hc
      refine conj_subset_of_conj h0 (fun s hs y hy => ?_) hc
      rcases hs with rfl | rfl
      · have := hY y hy 0 (by norm_num)
        rwa [← mul_assoc] at this
      · have := hY y hy 1 (by norm_num)
        rwa [← mul_assoc] at this)
    (by rw [ncard_classA]; norm_num)
  rw [ncard_classA] at h
  exact h

theorem h4_enum :
    (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)).L.size = 1152 ∧
    (∀ i < (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)).L.size,
      ∃ x ∈ (H4 : Set (Equiv.Perm (Fin 820))),
        Rep 820 (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)).L[i]! x) ∧
    ∀ x ∈ (H4 : Set (Equiv.Perm (Fin 820))),
      ∃ i < (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)).L.size,
        Rep 820 (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)).L[i]! x := by
  have hc : (H4 : Set (Equiv.Perm (Fin 820))).ncard = 1152 := by
    rw [← Nat.card_coe_set_eq]
    exact card_H4
  have h := bfsRec_enum (step := leftStep 820 (hGens 820 tabA tabB)) (k := 4) (cap := 1200)
    (x0 := idA 820) (Rep 820) (H4 : Set (Equiv.Perm (Fin 820))) (fun j a => m4 j * a) 1
    (Set.toFinite _) rep_idA H4.one_mem
    (fun t a ht ha j hj => ⟨rep_compA (arrE (by omega)).1 ht, H4.mul_mem (m4_mem_H4 hj) ha⟩)
    (fun t t' a a' ht ht' ha ha' => key_iff ht ht' (H4_le_P ha) (H4_le_P ha'))
    (fun Y h0 hY => closure_subset_of_left h0 fun s hs y hy => by
      obtain ⟨j, hj, rfl⟩ := hs
      exact hY y hy j hj)
    (by rw [hc]; norm_num)
  rw [hc] at h
  exact h

theorem syl_enum :
    (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L.size = 128 ∧
    (∀ i < (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L.size,
      ∃ x ∈ (closure (SP '' Set.Iio 3) : Set (Equiv.Perm (Fin 820))),
        Rep 820 (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L[i]! x) ∧
    ∀ x ∈ (closure (SP '' Set.Iio 3) : Set (Equiv.Perm (Fin 820))),
      ∃ i < (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L.size,
        Rep 820 (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L[i]! x := by
  have hc : (closure (SP '' Set.Iio 3) : Set (Equiv.Perm (Fin 820))).ncard = 128 := by
    rw [← Nat.card_coe_set_eq]
    exact card_Ssub
  have h := bfsRec_enum (step := leftStep 820 (sylGens 820 tabA tabB)) (k := 3) (cap := 200)
    (x0 := idA 820) (Rep 820) (closure (SP '' Set.Iio 3) : Set (Equiv.Perm (Fin 820)))
    (fun j a => SP j * a) 1 (Set.toFinite _) rep_idA (one_mem _)
    (fun t a ht ha j hj => ⟨rep_compA (rep_S hj) ht,
      mul_mem (subset_closure ⟨j, hj, rfl⟩) ha⟩)
    (fun t t' a a' ht ht' ha ha' => key_iff ht ht' (H4_le_P (Ssub_le ha))
      (H4_le_P (Ssub_le ha')))
    (fun Y h0 hY => closure_subset_of_left h0 fun s hs y hy => by
      obtain ⟨j, hj, rfl⟩ := hs
      exact hY y hy j hj)
    (by rw [hc]; norm_num)
  rw [hc] at h
  exact h

theorem orb_ok : orbCheck 820 tabA tabB = true := by
  unfold orbCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨invsOK_AB, ?_⟩, bfsRec_keysNodup _ _ _ _⟩
  have h := bfsRec_derivOK 820 (conjStep 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)))
    2 3000 tabA
  change derivOK 820 (conjStep 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB))) 2 tabA
    (orbRec 820 tabA tabB) (orbRec 820 tabA tabB).L.size = true at h
  rwa [orb_enum.1] at h

theorem invsOK_E : invsOK 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) = true :=
  invsOK_invArrs fun _ hi => ⟨_, (arrE hi).1⟩

theorem h4_ok : h4Check 820 tabA tabB rels4Codes = true := by
  simp only [h4Check, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨invsOK_AB, invsOK_E⟩, ?_⟩, ?_⟩, ?_⟩, bfsRec_keysNodup _ _ _ _⟩
  · rw [List.all_eq_true]
    intro i hi
    have hi : i < 4 := List.mem_range.1 hi
    refine (eqA_iff (rep_compA (arrE (by omega)).1 rep_A) (rep_compA rep_A (arrE (by omega)).1)).2 ?_
    rw [m4_eq hi]
    exact comm_m5 hi
  · rw [List.all_eq_true]
    intro w hw
    refine (eqA_iff (rep_evalArr w fun l hl => arrE ?_) rep_idA).2 ?_
    · have := rels4_letters w hw l hl
      omega
    · rw [evalG_m4 (rels4_letters w hw)]
      exact rel4 hw
  · have h := bfsRec_derivOK 820 (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)
    rwa [h4_enum.1] at h

theorem syl_ok : sylCheck 820 tabA tabB = true := by
  obtain ⟨hn, hL, hX⟩ := syl_enum
  obtain ⟨-, -, hO⟩ := orb_enum
  simp only [sylCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨invsOK_AB, invsOK_E⟩, ?_⟩, ?_⟩, bfsRec_keysNodup _ _ _ _⟩, ?_⟩, ?_⟩
  · exact invsOK_invArrs fun _ hj => ⟨_, rep_S hj⟩
  · have h := bfsRec_derivOK 820 (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)
    rwa [hn] at h
  · rw [closedOK, allLt_iff]
    intro j hj
    have hj : j < 3 := hj
    rw [allLt_iff]
    intro i hi
    obtain ⟨a, ha, hra⟩ := hL i hi
    have hs : SP j ∈ closure (SP '' Set.Iio 3) := subset_closure ⟨j, hj, rfl⟩
    obtain ⟨i1, hi1, hr1⟩ := hX _ (mul_mem hs ha)
    obtain ⟨i2, hi2, hr2⟩ := hX _ (mul_mem (inv_mem hs) ha)
    rw [Bool.and_eq_true]
    exact ⟨any_of_get hi1 (eqA_of_rep hr1 (rep_compA (rep_S hj) hra)),
      any_of_get hi2 (eqA_of_rep hr2 (rep_compA (rep_invArrs (by exact hj) (rep_S hj)) hra))⟩
  · rw [allLt_iff]
    intro i hi
    rw [← hn] at hi
    obtain ⟨a, ha, hra⟩ := hL i hi
    rw [Bool.or_eq_true]
    by_cases hinv : isInvolA 820
        (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L[i]! = true
    · right
      rw [isInvolA, Bool.and_eq_true, Bool.not_eq_true'] at hinv
      have h2 : a * a = 1 := (eqA_iff (rep_compA hra hra) rep_idA).1 hinv.1
      have h1 : a ≠ 1 := fun e => by
        rw [(eqA_iff hra rep_idA).2 e] at hinv
        exact Bool.noConfusion hinv.2
      obtain ⟨i', hi', hr'⟩ := hO a (invol_mem_classA (H4_le_P (Ssub_le ha)) h2 h1)
      exact any_of_get hi' (eqA_of_rep hra hr')
    · left
      simpa using hinv

end Lists

theorem invsOK_M : invsOK 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))
    (invArrs 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))) = true :=
  invsOK_invArrs fun _ hi => ⟨_, (arrM hi).1⟩

theorem rep_evalM {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 5) :
    Rep 820 (evalArr 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))
      (invArrs 820 (gensWith 820 tabA tabB (phiArr 820 tabA tabB))) w) (evalG m5 w) :=
  rep_evalArr w fun l hl => arrM (hw l hl)

theorem model_ok : modelCheck 820 tabA tabB rels5Codes = true := by
  simp only [modelCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨invsOK_AB, invsOK_M⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro w hw
    exact (eqA_iff (rep_evalM (rels5_letters w hw)) rep_idA).2 (rel5 hw)
  · exact (eqA_iff (rep_evalM (by decide)) rep_A).2 m5_a
  · exact (eqA_iff (rep_evalM surjB_letters) (CP_one ▸ rep_tabB)).2 m5_b

end CertificateChecks.KernelU43Mod

end
