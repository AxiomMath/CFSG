module

public import Certificates.Kernel.G2Three.SylChecks
public import Certificates.Kernel.G2Three.Final
public import CFSG.Certificates.Kernel.G2Three.SylSound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Local
public import Certificates.Data.G23RecogNativeFactsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.KC.Ord CFSG.KC.Loop CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec4.Item434RemG23

theorem wordE (w : List ℕ) : canon14 (wordCode w) = true ∧ pk (wordCode w) = wordK GA w :=
  wordCode_pk consts_ok bone gA_ok w

theorem commE {a b : List ℕ} {A B : ℕ} (ha : canon14 a = true ∧ pk a = A)
    (hb : canon14 b = true ∧ pk b = B) : commutes a b = commK2 A B := by
  unfold commutes commK2
  rw [beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _), pk_mul14 consts_ok ha.1 hb.1,
    pk_mul14 consts_ok hb.1 ha.1, ha.2, hb.2]
  rfl

theorem cubeE {c : List ℕ} {C : ℕ} (h : canon14 c = true ∧ pk c = C) :
    (cube14 c == one14) = cubeK2 C := by
  unfold cube14 sq14 cubeK2
  rw [beq_pk (canon14_mul14 _ _) canon14_one14, pk_mul14 consts_ok h.1 (canon14_mul14 _ _),
    pk_mul14 consts_ok h.1 h.1, h.2, bone]
  rfl

theorem oneE {c : List ℕ} {C : ℕ} (h : canon14 c = true ∧ pk c = C) :
    (c == one14) = Nat.beq C ONE := by
  rw [beq_pk h.1 canon14_one14, h.2, bone]

theorem getD_of_all {α : Type} {l : List α} {p : α → Bool} (h : l.all p = true) (d : α) {s : ℕ}
    (hs : s < l.length) : p (l.getD s d) = true := by
  rw [List.getD_eq_getElem _ _ hs]
  exact List.all_eq_true.1 h _ (List.getElem_mem hs)

theorem getD_mem' {α : Type} {l : List α} (d : α) {s : ℕ} (hs : s < l.length) :
    l.getD s d ∈ l := by
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs

theorem sylGens_len : sylGens.length = 3 := rfl

theorem sylGens_ok : ∀ s < sylGens.length,
    canon14 (sylGens.getD s one14) = true ∧ pk (sylGens.getD s one14) = SylG s
  | 0, _ => by
    have e : sylGens.getD 0 one14 = x0c := by simp only [sylGens, List.getD_cons_zero]
    rw [e]
    exact bindE bx0 (by quickRfl)
  | 1, _ => by
    have e : sylGens.getD 1 one14 = x1c := by
      simp only [sylGens, List.getD_cons_succ, List.getD_cons_zero]
    rw [e]
    exact bindE bx1 (by quickRfl)
  | 2, _ => by
    have e : sylGens.getD 2 one14 = wordCode sylWord := by
      simp only [sylGens, List.getD_cons_succ, List.getD_cons_zero]
    rw [e]
    exact bindE (wordE sylWord) (by quickRfl)
  | s + 3, h => absurd h (by rw [sylGens_len]; omega)

attribute [local irreducible] x0c x1c y0c y1c

theorem sylX0 : SylX 0 = pk one14 := by
  rw [bone]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem sylPar_eq : sylPar = parL (pA (SylPP 0)) (pB (SylPP 0)) 728 := of_decide_eq_true sylPar_ok

theorem sylPar_len : sylPar.length = 728 := by
  rw [sylPar_eq]
  simp [parL]

theorem sylPar_get {i : ℕ} (hi : i < 728) :
    sylPar.getD i (0, 0) = (pA (SylPP 0) i, pB (SylPP 0) i) := by
  rw [sylPar_eq, List.getD_eq_getElem _ _ (by simp [parL]; omega)]
  simp [parL]

theorem sylBuild : ∀ i < 728, pA (SylPP 0) i ≤ i ∧ pB (SylPP 0) i < 3 ∧
    SylX (i + 1) = MUL (SylX (pA (SylPP 0) i)) (SylG (pB (SylPP 0) i)) :=
  build_at sylBuild_ok (by decide)

theorem tabY : sylElems.size = 729 ∧
    ∀ t < 729, canon14 (sylElems.getD t []) = true ∧ pk (sylElems.getD t []) = SylX t := by
  have hgm : ∀ g ∈ sylGens, canon14 g = true := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    have := (sylGens_ok s hs).1
    rwa [List.getD_eq_getElem _ _ hs] at this
  obtain ⟨hsz, hrec⟩ := build_pk consts_ok hgm (fun s hs => (sylGens_ok s hs).2) sylX0
    (par := sylPar) (fun i hi => by
      rw [sylPar_len] at hi
      rw [sylPar_get hi]
      exact sylBuild i hi)
  rw [sylPar_len] at hsz hrec
  have hsz' : sylElems.size = 729 := hsz
  refine ⟨hsz', fun t ht => ?_⟩
  rw [getD_irrel (by rw [hsz']; exact ht) [] one14]
  exact hrec t ht

attribute [local irreducible] sylElems

theorem sylE {t : ℕ} (ht : t < 729) : canon14 (sylAt t) = true ∧ pk (sylAt t) = SylX t :=
  tabY.2 t ht

theorem sylInj : ∀ t < 729, ∀ t' < 729, SylX t = SylX t' → t = t' :=
  sort_inj sylSort_ok (by decide)

theorem sylAt_eq {t t' : ℕ} (ht : t < 729) (ht' : t' < 729) (h : sylAt t = sylAt t') : t = t' :=
  sylInj t ht t' ht' (by rw [← (sylE ht).2, ← (sylE ht').2, h])

theorem posE {i s : ℕ} (hi : i < 729) (hs : s < 3) :
    fR (SylRTP 0) (3 * i + s) < 729 ∧
      sylAt (fR (SylRTP 0) (3 * i + s)) = mul14 (sylAt i) (sylGens.getD s one14) := by
  obtain ⟨hn, hdiv, hmod⟩ := flat_facts (k := 3) (by decide) hi hs
  obtain ⟨hlt, hx⟩ := close_at sylClose_ok (by decide) _ hn
  rw [hdiv, hmod] at hx
  rw [Nat.mul_comm 3 i]
  refine ⟨hlt, pk_inj (sylE hlt).1 (canon14_mul14 _ _) ?_⟩
  rw [(sylE hlt).2, hx, pk_mul14 consts_ok (sylE hi).1 (sylGens_ok s hs).1, (sylE hi).2,
    (sylGens_ok s hs).2]
  rfl

theorem okSyl : sylCheck = true := by
  obtain ⟨hsz, hrec⟩ := tabY
  unfold sylCheck
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, hsz]
  refine ⟨⟨⟨⟨rfl, closedCheck_of (fun v hv g hg => ?_)⟩,
    distinctCheck_of (fun t ht t' ht' he => ?_)⟩,
    allCheck_of (fun t ht => (hrec t (by rw [← hsz]; exact ht)).1)⟩, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    rw [hsz] at hv
    have h := posE hv hs
    refine ⟨fR (SylRTP 0) (3 * v + s), by rw [hsz]; exact h.1, ?_⟩
    rw [← List.getD_eq_getElem _ one14 hs, ← sylAt_def, ← sylAt_def]
    exact h.2
  · rw [hsz] at ht ht'
    exact sylInj t ht t' ht' (by rw [← (hrec t ht).2, ← (hrec t' ht').2, he])
  · exact okC.2

theorem sylZ_parts : (∀ i ∈ sylZ, i < 729 ∧ ∀ s < 3, commK2 (SylX i) (SylG s) = true) ∧
    sylZIdx < 729 ∧ (∀ s < 3, commK2 (SylX sylZIdx) (SylG s) = true) ∧
    cubeK2 (SylX sylZIdx) = true ∧ Nat.beq (SylX sylZIdx) ONE = false := by
  have h := sylZ_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hZ, hzi⟩, hzc⟩, hzcube⟩, hzne⟩ := h
  refine ⟨fun i hi => ?_, Nat.blt_eq.mp hzi, allBelow_g2 hzc (by decide), hzcube, hzne⟩
  have := allL_true hZ i hi
  rw [Bool.and_eq_true] at this
  exact ⟨Nat.blt_eq.mp this.1, allBelow_g2 this.2 (by decide)⟩

theorem gensAll {t : ℕ} (ht : t < 729) (h : ∀ s < 3, commK2 (SylX t) (SylG s) = true) :
    sylGens.all (commutes (sylAt t)) = true :=
  all_of_getD one14 fun s hs => by
    rw [commE (sylE ht) (sylGens_ok s hs)]
    exact h s hs

theorem okZ : zOK = true := by
  obtain ⟨hZ, hzi, hzc, hzcube, hzne⟩ := sylZ_parts
  unfold zOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨List.all_eq_true.2 (fun i hi => ?_), hzi⟩, gensAll hzi hzc⟩, ?_⟩, ?_⟩
  · rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(hZ i hi).1, gensAll (hZ i hi).1 (hZ i hi).2⟩
  · rw [cubeE (sylE hzi)]
    exact hzcube
  · rw [oneE (sylE hzi)]
    exact hzne

theorem dShape : allBelow 7 1 (fun j => allBelow 4 1 fun a =>
    Nat.blt ((sylDs.getD j []).getD a 0) 729) = true := by quickRfl

theorem dE {j a : ℕ} (hj : j < 7) (ha : a < 4) :
    canon14 (dEl (sylDs.getD j []) a) = true ∧
      pk (dEl (sylDs.getD j []) a) = SylX ((sylDs.getD j []).getD a 0) :=
  sylE (Nat.blt_eq.mp (allBelow_g2 (allBelow_g2 dShape (by decide) j hj) (by decide) a ha))

theorem dBlock {j : ℕ} (hj : j < 7) :
    dBlockK SylX SylDX SylDSRT SylDSRI SylZW (sylDs.getD j []) sylZIdx j = true :=
  allBelow_g2 sylD_ok (by decide) j hj

theorem dProd_pk {D : List ℕ} {E : ℕ → ℕ}
    (hE : ∀ a < 4, canon14 (dEl D a) = true ∧ pk (dEl D a) = E a) (u : ℕ) :
    canon14 (dProd D u) = true ∧ pk (dProd D u) = dPK E u := by
  unfold dProd dPK
  exact mulE consts_ok (mulE consts_ok (mulE consts_ok
    (pow14_pk consts_ok bone (hE 0 (by decide)) _) (pow14_pk consts_ok bone (hE 1 (by decide)) _))
    (pow14_pk consts_ok bone (hE 2 (by decide)) _)) (pow14_pk consts_ok bone (hE 3 (by decide)) _)

theorem dArr_size (D : List ℕ) : (dArr D).size = 81 := by simp [dArr]

theorem dFacts {j : ℕ} (hj : j < 7) :
    (∀ a < 4, ∀ b < 4, commK2 (SylX ((sylDs.getD j []).getD a 0))
      (SylX ((sylDs.getD j []).getD b 0)) = true) ∧
    (∀ a < 4, cubeK2 (SylX ((sylDs.getD j []).getD a 0)) = true) ∧
    (∀ u < 81, SylDX (81 * j + u) = dPK (fun a => SylX ((sylDs.getD j []).getD a 0)) u) ∧
    (∀ u < 81, ∀ u' < 81, SylDX (81 * j + u) = SylDX (81 * j + u') → u = u') ∧
    SylZW j < 81 ∧ SylDX (81 * j + SylZW j) = SylX sylZIdx := by
  have hb := dBlock hj
  unfold dBlockK at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨hcomm, hcube⟩, hprod⟩, hsort⟩, hzw⟩, hzx⟩ := hb
  refine ⟨fun a ha b hb => allBelow_g2 (allBelow_g2 hcomm (by decide) a ha) (by decide) b hb,
    allBelow_g2 hcube (by decide), fun u hu => Nat.eq_of_beq_eq_true (allBelow_g2 hprod
    (by decide) u hu), fun u hu u' hu' he => sort_inj hsort (by decide) u hu u' hu' he,
    Nat.blt_eq.mp hzw, Nat.eq_of_beq_eq_true hzx⟩

theorem dProdE {j u : ℕ} (hj : j < 7) (hu : u < 81) :
    canon14 (dProd (sylDs.getD j []) u) = true ∧
      pk (dProd (sylDs.getD j []) u) = SylDX (81 * j + u) := by
  rw [(dFacts hj).2.2.1 u hu]
  exact dProd_pk (fun a ha => dE hj ha) u

theorem sylDs_len : sylDs.length = 7 := rfl

theorem dShape2 : (sylDs.all fun D => D.length == 4 && D.all (· < 729)) = true := by quickRfl

theorem okD : sylDs.all dOK = true := by
  refine all_of_getD [] fun j hj => ?_
  rw [sylDs_len] at hj
  obtain ⟨hcomm, hcube, -, hsort, hzw, hzx⟩ := dFacts hj
  have hsh := getD_of_all dShape2 [] (by rw [sylDs_len]; exact hj)
  unfold dOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨hsh, all_range_of (fun a ha => all_range_of (fun b hb => ?_))⟩,
    all_range_of (fun a ha => ?_)⟩, distinctCheck_of (fun t ht t' ht' he => ?_)⟩, ?_⟩
  · rw [commE (dE hj ha) (dE hj hb)]
    exact hcomm a ha b hb
  · rw [cubeE (dE hj ha)]
    exact hcube a ha
  · rw [dArr_size] at ht ht'
    rw [dArr_getD _ ht, dArr_getD _ ht'] at he
    exact hsort t ht t' ht' (by rw [← (dProdE hj ht).2, ← (dProdE hj ht').2, he])
  · refine found_indexMap.2 ⟨SylZW j, by rw [dArr_size]; exact hzw, ?_⟩
    rw [dArr_getD _ hzw]
    have hzi := sylZ_parts.2.1
    exact pk_inj (dProdE hj hzw).1 (sylE hzi).1 (by rw [(dProdE hj hzw).2, hzx, (sylE hzi).2])

theorem okCover2 : coverK2 = true := by
  unfold coverK2
  refine all_range_of fun t ht => ?_
  have e := sylE ht
  have hw := allBelow_g2 sylW_ok (by decide) t ht
  simp only [Bool.or_eq_true] at hw ⊢
  rw [oneE e, cubeE e]
  rcases hw with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · right
    rw [Bool.and_eq_true] at h
    have hlt := Nat.blt_eq.mp h.1
    have heq := Nat.eq_of_beq_eq_true h.2
    have hj : SylW t / 81 < 7 := by omega
    have hu : SylW t % 81 < 81 := Nat.mod_lt _ (by decide)
    have hwe : 81 * (SylW t / 81) + SylW t % 81 = SylW t := Nat.div_add_mod _ _
    rw [List.any_eq_true]
    refine ⟨(dArr (sylDs.getD (SylW t / 81) []), indexMap (dArr (sylDs.getD (SylW t / 81) []))),
      List.mem_map.2 ⟨_, getD_mem' [] (by rw [sylDs_len]; exact hj), rfl⟩, ?_⟩
    refine found_indexMap.2 ⟨SylW t % 81, by rw [dArr_size]; exact hu, ?_⟩
    rw [dArr_getD _ hu]
    exact pk_inj (dProdE hj hu).1 e.1 (by rw [(dProdE hj hu).2, hwe, heq, e.2])

theorem okK2 : k2Check = true := by
  unfold k2Check
  rw [okZ, okD, okCover2]
  rfl

theorem okWords : wordsOK = true := by quickRfl

theorem okRt : rtOK (indexMap sylElems) = true := by
  unfold rtOK
  refine all_range_of (fun i hi => all_range_of (fun s hs => found_indexMap.2
    ⟨fR (SylRTP 0) (3 * i + s), by rw [tabY.1]; exact (posE hi hs).1, ?_⟩))
  rw [← sylAt_def]
  exact (posE hi hs).2

theorem rtMain_eq : rtMain = rtTab (indexMap sylElems) := rfl

theorem rtStep_main {i s : ℕ} (hi : i < 729) (hs : s < 3) :
    rtStep rtMain i s = fR (SylRTP 0) (3 * i + s) := by
  obtain ⟨h1, h2⟩ := rtStep_spec okSyl okRt hi hs
  rw [rtMain_eq]
  exact sylAt_eq h1 (posE hi hs).1 (by rw [h2, (posE hi hs).2])

theorem buildStep {k : ℕ} (hk : k < 728) :
    sylAt (k + 1) = mul14 (sylAt (pA (SylPP 0) k)) (sylGens.getD (pB (SylPP 0) k) one14) := by
  obtain ⟨hle, hlt, hx⟩ := sylBuild k hk
  have hg := sylGens_ok _ hlt
  have hp := sylE (by omega : pA (SylPP 0) k < 729)
  refine pk_inj (sylE (by omega)).1 (canon14_mul14 _ _) ?_
  rw [(sylE (by omega)).2, hx, pk_mul14 consts_ok hp.1 hg.1, hp.2, hg.2]
  rfl

theorem paths_spec : pathsArr.getD 0 [] = [] ∧ ∀ k < 728,
    pathsArr.getD (k + 1) [] = pathsArr.getD (pA (SylPP 0) k) [] ++ [pB (SylPP 0) k] := by
  obtain ⟨-, h2, h3⟩ := foldl_push_spec [] (fun x ps => x ++ [ps.2]) sylPar #[[]]
    (fun i hi => by
      rw [sylPar_len] at hi
      rw [sylPar_get hi]
      have := (sylBuild i hi).1
      simp only [List.size_toArray, List.length_singleton]
      omega)
  unfold pathsArr
  refine ⟨h2 0 (by decide), fun k hk => ?_⟩
  have := h3 k (by rw [sylPar_len]; exact hk)
  rw [sylPar_get hk, List.size_toArray, List.length_singleton] at this
  rw [Nat.add_comm]
  exact this

attribute [local irreducible] pathsArr rtMain

theorem one_mul14 {x : List ℕ} (hx : canon14 x = true) : mul14 one14 x = x :=
  dec14_injective (canon14_mul14 _ _) hx (by rw [dec14_mul14, dec14_one14, one_mul])

theorem walk_spec : ∀ k < 729, (∀ s ∈ pathsArr.getD k [], s < 3) ∧ ∀ a < 729,
    (pathsArr.getD k []).foldl (rtStep rtMain) a < 729 ∧
      sylAt ((pathsArr.getD k []).foldl (rtStep rtMain) a) = mul14 (sylAt a) (sylAt k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · rw [paths_spec.1]
      refine ⟨fun s hs => absurd hs List.not_mem_nil, fun a ha => ⟨ha, ?_⟩⟩
      rw [List.foldl_nil, sylAt_zero, mul14_one (sylE ha).1]
    · obtain ⟨hle, hlt, -⟩ := sylBuild k (by omega)
      obtain ⟨ihs, iha⟩ := ih (pA (SylPP 0) k) (by omega) (by omega)
      rw [(paths_spec.2 k (by omega))]
      refine ⟨fun s hs => ?_, fun a ha => ?_⟩
      · rcases List.mem_append.1 hs with hs | hs
        · exact ihs s hs
        · rw [List.mem_singleton.1 hs]
          exact hlt
      · obtain ⟨h1, h2⟩ := iha a ha
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, rtStep_main h1 hlt]
        refine ⟨(posE h1 hlt).1, ?_⟩
        rw [(posE h1 hlt).2, h2, mul14_assoc, ← buildStep (by omega)]

theorem okPath : pathOK rtMain = true := by
  unfold pathOK
  refine all_range_of fun k hk => ?_
  obtain ⟨hs, hw⟩ := walk_spec k hk
  obtain ⟨h1, h2⟩ := hw 0 (by decide)
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨fun s hs' => decide_eq_true (hs s hs'), sylAt_eq h1 hk ?_⟩
  rw [h2, sylAt_zero, one_mul14 (sylE hk).1]

theorem mulIdxE {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    mulIdx rtMain a b < 729 ∧ sylAt (mulIdx rtMain a b) = mul14 (sylAt a) (sylAt b) :=
  mulIdx_main okSyl okRt okPath ha hb

theorem tArr_getD' {t : ℕ} (ht : t < 729) : tArr.getD t false = isTIdx t := by
  simp [tArr, Array.getD_eq_getD_getElem?, ht]

theorem conjWords_len : conjWords.length = 25 := rfl

theorem sylZ_len : sylZ.length = 8 := rfl

theorem inT_sound {D : ℕ} (h : inTK SylTKY SylTD (SylMK 0) D = true) :
    ∃ c ∈ tCodes, canon14 c = true ∧ pk c = D := by
  unfold inTK at h
  generalize SylTKY (Nat.mod D (SylMK 0)) = j at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hj, hD⟩ := h
  have hj' := Nat.blt_eq.mp hj
  have hT := Nat.eq_of_beq_eq_true (allBelow_g2 sylT_ok (by decide) _ hj')
  have e1 : Nat.div j 8 = j / 8 := rfl
  have e2 : Nat.mod j 8 = j % 8 := rfl
  rw [e1, e2] at hT
  have hw : j / 8 < conjWords.length := by rw [conjWords_len]; omega
  have hz : j % 8 < sylZ.length := by rw [sylZ_len]; omega
  have hzm := getD_mem' 0 hz
  have hz729 := (sylZ_parts.1 _ hzm).1
  have hp := take_drop_pair (wordE (invWord (conjWords.getD (j / 8) [])))
    (wordE (invWord (invWord (conjWords.getD (j / 8) []))))
  refine ⟨conjStep (wordPair (invWord (conjWords.getD (j / 8) []))) (sylAt (sylZ.getD (j % 8) 0)),
    ?_, canon14_mul14 _ _, ?_⟩
  · unfold tCodes zCodes
    exact List.mem_flatMap.2 ⟨_, getD_mem' [] hw, List.mem_map.2 ⟨_, List.mem_map.2 ⟨_, hzm, rfl⟩,
      rfl⟩⟩
  · unfold conjStep wordPair
    rw [pk_mul14 consts_ok (canon14_mul14 _ _) hp.2.1, pk_mul14 consts_ok hp.1.1 (sylE hz729).1,
      hp.1.2, hp.2.2, (sylE hz729).2, Nat.eq_of_beq_eq_true hD, hT]
    rfl

theorem tArr_of {m : ℕ} (hm : m < 729) (h : inTK SylTKY SylTD (SylMK 0) (SylX m) = true) :
    tArr.getD m false = true := by
  rw [tArr_getD' hm]
  obtain ⟨c, hc, hcc, hpk⟩ := inT_sound h
  unfold isTIdx
  rw [List.contains_iff_mem]
  rw [pk_inj hcc (sylE hm).1 (by rw [hpk, (sylE hm).2])] at hc
  exact hc

theorem tb_sound {m : ℕ} (hm : m < 729) (h : bitK (SylTB 0) m = true) :
    tArr.getD m false = true := by
  have := allBelow_g2 sylTB_ok (by decide) m hm
  rw [h, Bool.not_true, Bool.false_or] at this
  exact tArr_of hm this

theorem isN_isNK {t : ℕ} (ht : t < 729) (h : isN t = true) :
    isNK SylX (inTK SylTKY SylTD (SylMK 0)) t = true := by
  unfold isN at h
  rw [oneE (sylE ht), cubeE (sylE ht)] at h
  unfold isNK
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  refine ⟨h.1, ?_⟩
  cases hq : inTK SylTKY SylTD (SylMK 0) (SylX t)
  · rfl
  · rw [tArr_of ht hq] at h
    exact absurd h.2 (by decide)

theorem sylR_eq : SylR = SylR0 ++ SylR1 ++ SylR2 ++ SylR3 ++ SylR4 ++ SylR5 ++ SylR6 ++ SylR7 :=
  of_decide_eq_true sylRC_ok

theorem sylN_eq : (List.range 729).filter (isNK SylX (inTK SylTKY SylTD (SylMK 0))) =
    SylR.map fun R => fR R 0 :=
  of_decide_eq_true sylN_ok

theorem rows_ok {R : ℕ} (hR : R ∈ SylR) : rowK (SylPP 0) (SylRTP 0) R = true := by
  rw [sylR_eq] at hR
  simp only [List.mem_append] at hR
  rcases hR with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact allL_true sylRow0_ok R h
  · exact allL_true sylRow1_ok R h
  · exact allL_true sylRow2_ok R h
  · exact allL_true sylRow3_ok R h
  · exact allL_true sylRow4_ok R h
  · exact allL_true sylRow5_ok R h
  · exact allL_true sylRow6_ok R h
  · exact allL_true sylRow7_ok R h

theorem pairs_ok {R : ℕ} (hR : R ∈ SylR) :
    allL (fun RB => (fun b => Nat.beq b (fR R 0) || Nat.beq b (fR R (fR R 0)) ||
      (fun ab => !(Nat.beq ab (fR RB (fR R 0))) || bitK (SylTB 0) ab ||
        bitK (SylTB 0) (fR R (fR RB b))) (fR R b)) (fR RB 0)) SylR = true := by
  rw [sylR_eq] at hR
  simp only [List.mem_append] at hR
  rcases hR with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact allL_true sylP0_ok R h
  · exact allL_true sylP1_ok R h
  · exact allL_true sylP2_ok R h
  · exact allL_true sylP3_ok R h
  · exact allL_true sylP4_ok R h
  · exact allL_true sylP5_ok R h
  · exact allL_true sylP6_ok R h
  · exact allL_true sylP7_ok R h

theorem row_pos {R : ℕ} (hR : R ∈ SylR) : fR R 0 < 729 := by
  have : fR R 0 ∈ SylR.map fun R => fR R 0 := List.mem_map.2 ⟨R, hR, rfl⟩
  rw [← sylN_eq] at this
  exact List.mem_range.1 (List.mem_filter.1 this).1

theorem row_spec {R : ℕ} (hR : R ∈ SylR) : ∀ k < 729, fR R k = mulIdx rtMain (fR R 0) k := by
  have hrow := row_at (rows_ok hR)
  have ha := row_pos hR
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · unfold mulIdx
      rw [paths_spec.1]
      rfl
    · obtain ⟨hle, hlt, -⟩ := sylBuild k (by omega)
      have hm := (mulIdxE ha (by omega : pA (SylPP 0) k < 729)).1
      rw [hrow k (by omega), ih _ (by omega) (by omega), ← rtStep_main hm hlt]
      unfold mulIdx
      rw [paths_spec.2 k (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem row_of {t : ℕ} (ht : t < 729) (h : isN t = true) : ∃ R ∈ SylR, fR R 0 = t := by
  have : t ∈ (List.range 729).filter (isNK SylX (inTK SylTKY SylTD (SylMK 0))) :=
    List.mem_filter.2 ⟨List.mem_range.2 ht, isN_isNK ht h⟩
  rw [sylN_eq] at this
  obtain ⟨R, hR, he⟩ := List.mem_map.1 this
  exact ⟨R, hR, he⟩

theorem mulIdx_assoc {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    mulIdx rtMain (mulIdx rtMain a b) b = mulIdx rtMain a (mulIdx rtMain b b) := by
  obtain ⟨h1, h2⟩ := mulIdxE ha hb
  obtain ⟨h3, h4⟩ := mulIdxE hb hb
  obtain ⟨h5, h6⟩ := mulIdxE h1 hb
  obtain ⟨h7, h8⟩ := mulIdxE ha h3
  exact sylAt_eq h5 h7 (by rw [h6, h8, h2, h4, mul14_assoc])

theorem okLoop : coverLoop = true := by
  unfold coverLoop
  refine all_range_of (fun ia hia => ?_)
  rw [nArr_getD hia]
  cases hNa : isN ia
  · rfl
  obtain ⟨RA, hRA, rfl⟩ := row_of hia hNa
  have hP := allL_true (pairs_ok hRA)
  rw [Bool.not_true, Bool.false_or]
  dsimp only
  refine all_range_of (fun ib hib => ?_)
  rw [nArr_getD hib]
  cases hNb : isN ib
  · rfl
  obtain ⟨RB, hRB, rfl⟩ := row_of hib hNb
  have hp := hP RB hRB
  dsimp only at hp
  have ha := row_pos hRA
  have hb := row_pos hRB
  rw [row_spec hRB (fR RB 0) hb] at hp
  rw [row_spec hRA (mulIdx rtMain (fR RB 0) (fR RB 0)) (mulIdxE hb hb).1,
    row_spec hRA (fR RA 0) ha, row_spec hRA (fR RB 0) hb, row_spec hRB (fR RA 0) ha] at hp
  rw [Bool.not_true, Bool.false_or, mulIdx_assoc ha hb]
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hp ⊢
  rcases hp with (h | h) | ((h | h) | h)
  · rw [Nat.eq_of_beq_eq_true h]
    exact Or.inl (Or.inl (Or.inl (Or.inl (beq_self_eq_true _))))
  · rw [Nat.eq_of_beq_eq_true h]
    exact Or.inl (Or.inl (Or.inl (Or.inr (beq_self_eq_true _))))
  · refine Or.inl (Or.inl (Or.inr ?_))
    cases hq : (mulIdx rtMain (fR RA 0) (fR RB 0) == mulIdx rtMain (fR RB 0) (fR RA 0))
    · rfl
    · rw [beq_iff_eq.1 hq, Nat.beq_refl] at h
      exact absurd h (by decide)
  · exact Or.inl (Or.inr (tb_sound (mulIdxE ha hb).1 h))
  · exact Or.inr (tb_sound (mulIdxE ha (mulIdxE hb hb).1).1 h)

theorem okCover : coverCheck = true := by
  unfold coverCheck
  rw [okWords, okRt, okPath, okLoop]
  rfl

theorem liftShape : (liftW.length == 3 && liftW.all (· < 729) && liftG.length == 2 &&
    liftM.length == 2) = true := by quickRfl

theorem liftMatOK : ((List.range 2).all fun j => (List.range 3).all fun k => (List.range 3).all
    fun i => decide (liftMat j k i < 3)) = true := by quickRfl

theorem liftW_lt {a : ℕ} (ha : a < 3) : liftW.getD a 0 < 729 := by
  rcases a with _ | _ | _ | a
  · decide
  · decide
  · decide
  · omega

theorem liftE {a : ℕ} (ha : a < 3) :
    canon14 (liftEl a) = true ∧ pk (liftEl a) = SylX (liftW.getD a 0) :=
  sylE (liftW_lt ha)

theorem liftProd_pk (u : ℕ) :
    canon14 (liftProd u) = true ∧ pk (liftProd u) = lPK (fun a => SylX (liftW.getD a 0)) u := by
  unfold liftProd lPK
  exact mulE consts_ok (mulE consts_ok (pow14_pk consts_ok bone (liftE (by decide)) _)
    (pow14_pk consts_ok bone (liftE (by decide)) _)) (pow14_pk consts_ok bone (liftE (by decide)) _)

theorem okLift : liftCheck = true := by
  have h := sylLift_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcomm, hcube⟩, hdist⟩, hconj⟩ := h
  have hsh := liftShape
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hsh
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hsh
  unfold liftCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, all_range_of fun a ha => all_range_of fun b hb => ?_⟩,
    all_range_of fun a ha => ?_⟩, distinctCheck_of fun t ht t' ht' he => ?_⟩, ?_⟩,
    all_range_of fun j hj => all_range_of fun i hi => ?_⟩
  · rw [commE (liftE ha) (liftE hb)]
    exact allBelow_g2 (allBelow_g2 hcomm (by decide) a ha) (by decide) b hb
  · rw [cubeE (liftE ha)]
    exact allBelow_g2 hcube (by decide) a ha
  · simp only [List.size_toArray, List.length_map, List.length_range] at ht ht'
    have hd := allBelow_g2 (allBelow_g2 hdist (by decide) t ht) (by decide) t' ht'
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hd
    rcases hd with hd | hd
    · exact Nat.eq_of_beq_eq_true hd
    · exfalso
      have e1 : ((List.range 27).map liftProd).toArray.getD t [] = liftProd t := by
        simp [Array.getD_eq_getD_getElem?, ht]
      have e2 : ((List.range 27).map liftProd).toArray.getD t' [] = liftProd t' := by
        simp [Array.getD_eq_getD_getElem?, ht']
      rw [e1, e2] at he
      rw [← (liftProd_pk t).2, ← (liftProd_pk t').2, he, Nat.beq_refl] at hd
      exact absurd hd (by decide)
  · exact liftMatOK
  · have hc := allBelow_g2 (allBelow_g2 hconj (by decide) j hj) (by decide) i hi
    have hp := take_drop_pair (wordE (liftG.getD j [])) (wordE (invWord (liftG.getD j [])))
    have eL : canon14 (conjStep (wordPair (liftG.getD j [])) (liftEl i)) = true ∧
        pk (conjStep (wordPair (liftG.getD j [])) (liftEl i)) =
          MUL (MUL (wordK GA (liftG.getD j [])) (SylX (liftW.getD i 0)))
            (wordK GA (invWord (liftG.getD j []))) :=
      mulE consts_ok (mulE consts_ok hp.1 (liftE hi)) hp.2
    have eR : canon14 (liftRhs j i) = true ∧ pk (liftRhs j i) =
        MUL (pwK (SylX (liftW.getD 0 0)) (liftMat j 0 i)) (MUL (pwK (SylX (liftW.getD 1 0))
          (liftMat j 1 i)) (MUL (pwK (SylX (liftW.getD 2 0)) (liftMat j 2 i)) ONE)) := by
      unfold liftRhs
      exact mulE consts_ok (pow14_pk consts_ok bone (liftE (by decide)) _)
        (mulE consts_ok (pow14_pk consts_ok bone (liftE (by decide)) _)
          (mulE consts_ok (pow14_pk consts_ok bone (liftE (by decide)) _)
            ⟨canon14_one14, bone⟩))
    rw [beq_pk eL.1 eR.1, eL.2, eR.2]
    exact hc

open CFSG.GH74.QTGen4.Recog.G23 in
theorem eCanon : ((List.finRange 6).all fun i => canon14 (eCode i) && canon14 (eInvCode i)) =
    true := by quickRfl

open CFSG.GH74.QTGen4.Recog.G23 in
theorem eWords : ((List.finRange 6).all fun i => Nat.beq (wordK GA (eWord i)) (pk (eCode i))) =
    true := by quickRfl

open CFSG.GH74.QTGen4.Recog.G23 in
theorem xyWords :
    (Nat.beq (x1Word.foldl (fun c a => MUL c (pk (CFSG.GH74.QTGen4.Recog.G23.letterCode a))) ONE)
        (pk x0c) &&
      Nat.beq (y1Word.foldl (fun c a => MUL c (pk (CFSG.GH74.QTGen4.Recog.G23.letterCode a))) ONE)
        (pk y0c)) = true := by
  quickRfl

open CFSG.GH74.QTGen4.Recog.G23 in
theorem eCanon_at (i : Fin 6) : canon14 (eCode i) = true ∧ canon14 (eInvCode i) = true := by
  have := List.all_eq_true.1 eCanon i (List.mem_finRange i)
  rwa [Bool.and_eq_true] at this

open CFSG.GH74.QTGen4.Recog.G23 in
theorem letter_pk (l : Fin 6 × Bool) :
    canon14 (CFSG.GH74.QTGen4.Recog.G23.letterCode l) = true ∧
      pk (CFSG.GH74.QTGen4.Recog.G23.letterCode l) =
        pk (CFSG.GH74.QTGen4.Recog.G23.letterCode l) := by
  refine ⟨?_, rfl⟩
  unfold CFSG.GH74.QTGen4.Recog.G23.letterCode
  split
  · exact (eCanon_at l.1).1
  · exact (eCanon_at l.1).2

open CFSG.GH74.QTGen4.Recog.G23 in
theorem ok320002 : (∀ i, wordCode (eWord i) = eCode i) ∧ (evalCode x1Word = x0c) ∧
    (evalCode y1Word = y0c) := by
  have hxy := xyWords
  rw [Bool.and_eq_true] at hxy
  have ev := fun r => foldl_pk consts_ok CFSG.GH74.QTGen4.Recog.G23.letterCode
    (fun l => pk (CFSG.GH74.QTGen4.Recog.G23.letterCode l)) letter_pk r one14 ONE
    ⟨canon14_one14, bone⟩
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have := List.all_eq_true.1 eWords i (List.mem_finRange i)
    exact pk_inj (wordE _).1 (eCanon_at i).1 (by rw [(wordE _).2]; exact Nat.eq_of_beq_eq_true this)
  · have h1 := Nat.eq_of_beq_eq_true hxy.1
    have h2 := (ev x1Word).2
    rw [h1] at h2
    unfold CFSG.GH74.QTGen4.Recog.G23.evalCode
    exact pk_inj (ev x1Word).1 bx0.1 h2
  · have h1 := Nat.eq_of_beq_eq_true hxy.2
    have h2 := (ev y1Word).2
    rw [h1] at h2
    unfold CFSG.GH74.QTGen4.Recog.G23.evalCode
    exact pk_inj (ev y1Word).1 by0.1 h2

end CFSG.KD.G2Three

end
