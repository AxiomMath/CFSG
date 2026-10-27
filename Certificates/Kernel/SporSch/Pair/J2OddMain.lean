module

public import Certificates.Kernel.SporSch.Pair.J2OddClFacts
public import Certificates.Kernel.SporSch.Pair.J2OddWit
public import CFSG.Certificates.Kernel.SporSch.J2OddWitSound
public import CFSG.Certificates.Kernel.SporSch.J2OddGroup
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass

public section

namespace CertificateChecks.KernelSporSch.PJ2C260410G

open CFSG CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.J2OW CFSG.KS.SporSch.J2OG CFSG.KS.SylowCount
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.J2Cls
open CertificateChecks.KernelSporSch.J2OW260410 Subgroup CFSG.Certificates CFSG.Certificates.Native

@[expose] noncomputable def wg (i : ℕ) : Equiv.Perm (Fin 315) :=
  (wordElts (j2Gen 0) (j2Gen 1) 2 3 (getW ws i)).prod

theorem wg_mem (i : ℕ) : wg i ∈ j2P :=
  wordElts_prod_mem (j2Gen_mem_P 0 (by norm_num)) (j2Gen_mem_P 1 (by norm_num)) _

@[expose] noncomputable def E (i : ℕ) : ↥j2P := ⟨wg i, wg_mem i⟩

theorem hsz : szOK 315 9 = true := rfl

theorem pS (j : ℕ) (hj : j < 7) :
    PRep 315 9 (PJ2.S j) (j2Gen j) :=
  prep_of_rep (by rw [← PJ2.arr_eq j hj]; exact rep_j2StrongPerm hj)

theorem hT : TabRep 315 9 nT ps wg :=
  tabK_sound hsz (pS 0 (by norm_num)) (pS 1 (by norm_num)) j2owTab

theorem powE {i k j : ℕ} (h : (i, k, j) ∈ powL) : E j = E i ^ k :=
  Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (powsK_sound hsz hT j2owPow _ h).2.2)

theorem conjE {d x y : ℕ} (h : (d, x, y) ∈ conjL) :
    IsConj (E x) (E y) := by
  have e : E d * E x = E y * E d :=
    Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (conjsK_sound hsz hT j2owConj _ h).2.2.2)
  refine isConj_iff.2 ⟨E d, ?_⟩
  rw [e]
  group

theorem commE {x y : ℕ} (h : (x, y) ∈ commL) :
    E x * E y = E y * E x :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (commsK_sound hsz hT j2owComm _ h).2.2)

theorem ordE {i o : ℕ} (h : (i, o) ∈ ordL) : orderOf (E i) = o := by
  rw [← Subgroup.orderOf_coe]
  exact (ordsK_sound hsz hT j2owOrd _ h).2

theorem E9 : E 9 = 1 := Subtype.ext (by
  have e : getW ws 9 = [] := by decide
  change (wordElts (j2Gen 0) (j2Gen 1) 2 3 (getW ws 9)).prod = 1
  rw [e]
  rfl)

theorem sub_of_closed {L : List ℕ}
    (h : closedK 315 9 (mask 9) nT ps L L = true) (hne : L ≠ []) :
    ∃ H : Subgroup ↥j2P, Nat.card H = L.length ∧ ∀ s ∈ H, ∃ i ∈ L, s = E i := by
  obtain ⟨hlt, hnd, hcl⟩ := closedK_sound hsz hT h
  let el : Fin L.length → ↥j2P := fun t => E (L.get t)
  have hinj : Function.Injective el := by
    intro s t hst
    have e : wg (L.get s) = wg (L.get t) := congrArg Subtype.val hst
    have hL : L.Nodup := hnd.of_map _
    have e2 : L.get s = L.get t :=
      List.inj_on_of_nodup_map hnd (List.get_mem _ _) (List.get_mem _ _) e
    exact hL.get_inj_iff.1 e2
  have hmemL : ∀ i ∈ L, ∃ t, el t = E i := fun i hi => by
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hi
    exact ⟨⟨t, ht⟩, rfl⟩
  have hclosed : ∀ x ∈ Set.range el, ∀ y ∈ Set.range el, x * y ∈ Set.range el := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    have hs : L.get s ∈ L := List.get_mem L s
    have ht : L.get t ∈ L := List.get_mem L t
    obtain ⟨k, hk, e⟩ := memK_spec (hcl _ hs _ ht)
    obtain ⟨r, hr⟩ := hmemL k hk
    refine ⟨r, ?_⟩
    rw [hr]
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    have p1 := prep_pcomp (by norm_num) (hT _ (hlt _ hs)).1 (hT _ (hlt _ ht)).1
    rw [e] at p1
    exact CFSG.KS.SporSch.MOC.prep_unique (hT _ (hlt _ hk)).1 p1
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil L hne
  obtain ⟨t0, -⟩ := hmemL j hj
  obtain ⟨H, hH⟩ := exists_subgroup_of_closed _
    (⟨el t0, t0, rfl⟩ : (Set.range el).Nonempty) hclosed
  refine ⟨H, ?_, fun s hs => ?_⟩
  · have e1 : Nat.card H = Nat.card (Set.range el) := Nat.card_congr (Equiv.subtypeEquivRight hH)
    rw [e1, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · obtain ⟨t, rfl⟩ := (hH s).1 hs
    exact ⟨L.get t, List.get_mem L t, rfl⟩

theorem cl_bound
    {w : List (Array ℕ)} {c : ℕ} (hcl : ClFact w c) {x : ↥j2P} (hrep : RepW 315 w x) :
    c * Nat.card (centralizer ({x} : Set ↥j2P)) ≤ 604800 := by
  classical
  have : Fintype ↥j2P := Fintype.ofFinite _
  obtain ⟨hok, hsz', hnd⟩ := hcl
  have hxo : (x : Equiv.Perm (Fin 315)) ∈ j2Chain.originalSubgroup := j2P_eq_original ▸ x.2
  have spec := closureOK_spec j2ChainArrays (chainCheckFacts PairJ2.chain_check.1)
    j2Chain_valid.1 j2_baseFaithful j2_bs_lt j2_gens hrep hxo hok
  set cl := closureOf w
  have hmem : ∀ nf ∈ cl.1.toList, nfOK (rawLevels 315 j2StrongArrs PairJ2.baseArr) nf = true ∧
      ∃ d ∈ j2Chain.originalSubgroup, nfElt 315 j2StrongArrs PairJ2.baseArr nf = d * x * d⁻¹ := by
    intro nf hnf
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hnf
    rw [Array.length_toList] at hk
    have := spec k hk
    rw [getElem!_pos cl.1 k hk] at this
    simpa [Array.getElem_toList] using this
  set L := cl.1.toList.map (nfElt 315 j2StrongArrs PairJ2.baseArr)
  have hkey : cl.1.toList.map clKey = L.map (keyElt 315 PairJ2.bs) := by
    rw [List.map_map]
    refine List.map_congr_left fun nf hnf => ?_
    exact imgKey_baseImgs j2_bs_lt (repW_nfWord j2ChainArrays
      (chainCheckFacts PairJ2.chain_check.1) (hmem nf hnf).1)
  have hLnd : L.Nodup := by
    rw [hkey] at hnd
    exact hnd.of_map _
  have hLlen : L.length = c := by simp [L, hsz']
  let F := (Finset.univ.filter (IsConj x)).map (Function.Embedding.subtype _)
  have hsub : L.toFinset ⊆ F := by
    intro y hy
    rw [List.mem_toFinset] at hy
    obtain ⟨nf, hnf, rfl⟩ := List.mem_map.1 hy
    obtain ⟨-, d, hd, e⟩ := hmem nf hnf
    have hdP : d ∈ j2P := j2P_eq_original ▸ hd
    rw [Finset.mem_map]
    refine ⟨⟨d, hdP⟩ * x * ⟨d, hdP⟩⁻¹, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, isConj_conj _ _⟩
    · rw [Function.Embedding.subtype_apply, e]
      rfl
  have h1 : c ≤ (Finset.univ.filter (IsConj x)).card := by
    rw [← hLlen, ← List.toFinset_card_of_nodup hLnd]
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_map])
  have h2 := card_conj_mul_card_comm x
  have h3 : Nat.card (centralizer ({x} : Set ↥j2P)) =
      (Finset.univ.filter fun g : ↥j2P => g * x = x * g).card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_centralizer_singleton_iff),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h4 : Fintype.card ↥j2P = 604800 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_j2P
  rw [h3, ← h4, ← h2]
  convert Nat.mul_le_mul_right _ h1

theorem prod_wordElts_pat (gA gB : Equiv.Perm (Fin 315)) (p : List Bool) :
    (wordElts gA gB 2 3 (p.map fun t => if t then 1 else 0)).prod =
      (p.map fun t => if t then gB else gA).prod := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, ← ih]
    cases t <;> simp [wordElts]

theorem wrep15A : RepW 315 w15A (wg 0) := by
  have e : getW ws 0 = p15A.map fun t => if t then 1 else 0 := by decide
  change RepW 315 w15A (wordElts (j2Gen 0) (j2Gen 1) 2 3 (getW ws 0)).prod
  rw [e, prod_wordElts_pat]
  exact repW_patW repW_j2wA repW_j2wB p15A

theorem wrep5C : RepW 315 w5C (wg 2) := by
  have e : getW ws 2 = p5C.map fun t => if t then 1 else 0 := by decide
  change RepW 315 w5C (wordElts (j2Gen 0) (j2Gen 1) 2 3 (getW ws 2)).prod
  rw [e, prod_wordElts_pat]
  exact repW_patW repW_j2wA repW_j2wB p5C

theorem wrepB : RepW 315 PairJ2.wB (wg 3) := by
  have e : getW ws 3 = [1] := by decide
  change RepW 315 PairJ2.wB (wordElts (j2Gen 0) (j2Gen 1) 2 3 (getW ws 3)).prod
  rw [e]
  simpa [wordElts] using repW_j2wB

theorem repPow :
    ∀ k : ℕ, RepW 315 (List.replicate k w15A).flatten (wg 0 ^ k)
  | 0 => by simpa using repW_nil
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, pow_succ]
    exact wrep15A.append (repPow k)

theorem cent_le {w : List (Array ℕ)}
    {c i : ℕ} (hcl : ClFact w c) (hrep : RepW 315 w (wg i)) (hc : 0 < c) :
    Nat.card (centralizer ({E i} : Set ↥j2P)) ≤ 604800 / c :=
  (Nat.le_div_iff_mul_le hc).2 (by rw [mul_comm]; exact cl_bound hcl hrep)

theorem wg_pow {i k j : ℕ} (h : (i, k, j) ∈ powL) :
    wg j = wg i ^ k := congrArg Subtype.val (powE h)

theorem sub_props {L : List ℕ}
    (h : closedK 315 9 (mask 9) nT ps L L = true) (hne : L ≠ []) {n x : ℕ}
    (hn : L.length = n) (hc : ∀ i ∈ L, (i, x) ∈ commL) :
    ∃ H : Subgroup ↥j2P, Nat.card H = n ∧ H ≤ centralizer {E x} ∧
      ∀ s ∈ H, ∃ i ∈ L, s = E i := by
  obtain ⟨H, hH, hs⟩ := sub_of_closed h hne
  refine ⟨H, hn ▸ hH, fun s hsH => ?_, hs⟩
  obtain ⟨i, hi, rfl⟩ := hs s hsH
  exact mem_cent (commE (hc i hi))

theorem conj_of {L : List ℕ} {X : List ℕ}
    (h : ∀ i ∈ L, i = 9 ∨ ∃ r ∈ conjL, r.2.2 = i ∧ r.2.1 ∈ X) {i : ℕ} (hi : i ∈ L) :
    E i = 1 ∨ ∃ x ∈ X, IsConj (E x) (E i) := by
  rcases h i hi with rfl | ⟨⟨d, x, y⟩, hr, rfl, hx⟩
  · exact Or.inl E9
  · exact Or.inr ⟨x, hx, conjE hr⟩

theorem j2Data :
    J2Data ↥j2P (E 5) (E 3) (E 6) (E 2) (E 4) (E 0) (E 1) := by
  obtain ⟨c3A, c3B, c5A, c5C⟩ := clFacts
  have h5 : wg 5 = wg 0 ^ 5 := wg_pow (by decide)
  have h6 : wg 6 = wg 0 ^ 3 := wg_pow (by decide)
  have h7 : E 7 = E 6 ^ 2 := powE (by decide)
  have h8 : E 8 = E 2 ^ 2 := powE (by decide)
  refine
    { card := card_j2P
      ha := powE (by decide)
      hu := powE (by decide)
      oy := ordE (by decide)
      ob := ordE (by decide)
      ov := ordE (by decide)
      ox := ordE (by decide)
      cA := cent_le c3A (by rw [h5]; exact repPow 5) (by norm_num)
      cB := cent_le c3B wrepB (by norm_num)
      cU := cent_le c5A (by rw [h6]; exact repPow 3) (by norm_num)
      cV := cent_le c5C wrep5C (by norm_num)
      s3 := ?_
      s5 := ?_
      s5v := ?_
      k4 := ?_
      e4 := ⟨E 143, ordE (by decide), commE (by decide)⟩
      e5 := ⟨E 144, ordE (by decide), commE (by decide)⟩
      t2 := ⟨E 145, ordE (by decide), commE (by decide)⟩
      c7 := ?_
      c15 := ?_ }
  · obtain ⟨H, hc, hle, hs⟩ := sub_props (n := 27) (x := 5) j2owS3 (by decide) (by decide) (by decide)
    refine ⟨H, hc, hle, fun s hsH => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hs s hsH
    rcases conj_of (X := [5, 3]) (by decide) hi with h | ⟨x, hx, hc⟩
    · exact Or.inl h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · obtain ⟨H, hc, hle, hs⟩ := sub_props (n := 25) (x := 6) j2owS5 (by decide) (by decide) (by decide)
    refine ⟨H, hc, hle, fun s hsH => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hs s hsH
    rcases conj_of (X := [6, 7, 2, 8]) (by decide) hi with h | ⟨x, hx, hc⟩
    · exact Or.inl h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl (h7 ▸ hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (h8 ▸ hc))))
  · obtain ⟨H, hc, hle, -⟩ := sub_props (n := 25) (x := 2) j2owS5V (by decide) (by decide) (by decide)
    exact ⟨H, hc, hle⟩
  · obtain ⟨H, hc, hle, -⟩ := sub_props (n := 4) (x := 3) j2owK4 (by decide) (by decide) (by decide)
    exact ⟨H, hc, hle⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [pow_one]
      exact IsConj.refl _
    · rw [← powE (i := 4) (k := 2) (j := 119) (by decide)]
      exact conjE (d := 120) (by decide)
    · rw [← powE (i := 4) (k := 3) (j := 121) (by decide)]
      exact conjE (d := 122) (by decide)
    · rw [← powE (i := 4) (k := 4) (j := 123) (by decide)]
      exact conjE (d := 124) (by decide)
    · rw [← powE (i := 4) (k := 5) (j := 125) (by decide)]
      exact conjE (d := 126) (by decide)
    · rw [← powE (i := 4) (k := 6) (j := 127) (by decide)]
      exact conjE (d := 128) (by decide)
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · left
      rw [pow_one]
      exact IsConj.refl _
    · right
      rw [← powE (i := 0) (k := 2) (j := 129) (by decide)]
      exact conjE (d := 130) (by decide)
    · right
      rw [← powE (i := 0) (k := 7) (j := 133) (by decide)]
      exact conjE (d := 134) (by decide)
    · left
      rw [← powE (i := 0) (k := 11) (j := 137) (by decide)]
      exact conjE (d := 138) (by decide)

theorem j2OddFacts :
    (∀ g : ↥j2P, IsPRegular 2 g → orderOf g ∈ [1, 3, 5, 7, 15]) ∧
      Fintype.card (PRegularClass 2 ↥j2P) ≤ 10 := by
  have D := j2Data
  refine ⟨fun g hg => (odd_cover D g hg).1, ?_⟩
  classical
  let R : Fin 10 → ↥j2P := ![1, E 5, E 3, E 6, E 6 ^ 2, E 2, E 2 ^ 2, E 4, E 0, E 1]
  have hrep : ∀ C : PRegularClass 2 ↥j2P, ∃ i : Fin 10, IsConj (R i) (PRegularClass.repr C) := by
    intro C
    rcases (odd_cover D _ (PRegularClass.repr_isPRegular C)).2 with
      h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩
    · exact ⟨8, h⟩
    · exact ⟨9, h⟩
  choose f hf using hrep
  have hinj : Function.Injective f := by
    intro C C' hCC'
    have hc : IsConj (PRegularClass.repr C) (PRegularClass.repr C') :=
      (hf C).symm.trans (hCC' ▸ hf C')
    apply PRegularClass.ext
    have h1 : ConjClasses.mk (PRegularClass.repr C) = C.1 := Quotient.out_eq C.1
    have h2 : ConjClasses.mk (PRegularClass.repr C') = C'.1 := Quotient.out_eq C'.1
    rw [← h1, ← h2]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hc
  have h := Fintype.card_le_of_injective f hinj
  rwa [Fintype.card_fin] at h

end CertificateChecks.KernelSporSch.PJ2C260410G

end
