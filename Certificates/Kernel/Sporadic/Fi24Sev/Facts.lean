module

public import Certificates.Kernel.Sporadic.Fi24Sev.Cent
public import Certificates.Kernel.Sporadic.Fi24Sev.Points
public import Certificates.Kernel.Sporadic.Fi24Sev.CovA
public import Certificates.Kernel.Sporadic.Fi24Sev.CovB
public import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KD.Fi24Sev.Cent

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24Sev CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group

attribute [local instance] CFSG.Sporadic.Fi24.rAction

local notation "DK" => clsK CFSG.KD.Fi24ThreeO.OL NT

theorem cbG {j : ℕ} (hj : j < 6) : CFSG.Sporadic.Fi24.Native.chainBase[j]! = cb.getD j 0 := by
  rw [chainBase_eq]
  interval_cases j <;> rfl

theorem cb_lt' {j : ℕ} (hj : j < 6) : cb.getD j 0 < 306936 := by
  interval_cases j <;> decide

theorem mem_lv {i l : ℕ} (hi : i ≤ 4) (hl : 4 * i ≤ l ∧ l < 26) :
    l ∈ (CFSG.KD.Fi24OrbL.lv i).toArray := by
  rw [List.mem_toArray]
  interval_cases i
  · simp only [CFSG.KD.Fi24OrbL.lv, List.mem_range]; omega
  all_goals
    simp only [CFSG.KD.Fi24OrbL.lv, List.mem_map, List.mem_range]
    first
      | exact ⟨l - 4, by omega, by omega⟩
      | exact ⟨l - 8, by omega, by omega⟩
      | exact ⟨l - 12, by omega, by omega⟩
      | exact ⟨l - 16, by omega, by omega⟩

theorem letter_mem_lvl {i l : ℕ} (hi : i ≤ 6) (hl : l ∈ (CFSG.KD.Fi24OrbL.lv i).toArray) :
    pairG gs l ∈ lvl i := by
  change pairG gs l ∈ levelGroup CFSG.Sporadic.Fi24.letters CFSG.Sporadic.Fi24.Native.chainBase
    (pairG gs) i
  unfold levelGroup
  rw [show CFSG.Sporadic.Fi24.letters = CFSG.Sporadic.Fi24.Native.chainLetters CFSG.Sporadic.Fi24.orb
    from rfl, CertificateChecks.KernelFi24OrbL.levelLetters_eq i hi]
  exact lG_mem hl

theorem wordElt_mem_lvl {i : ℕ} (hi : i ≤ 4) {t : List ℕ} (ht : ∀ l ∈ t, 4 * i ≤ l ∧ l < 26) :
    wordElt t ∈ lvl i := by
  unfold wordElt
  refine (lvl i).list_prod_mem fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact letter_mem_lvl (by omega) (mem_lv hi (ht l hl))

local notation "L24" => pairG gs 24

theorem L24_mem : L24 ∈ lvl 5 :=
  letter_mem_lvl (by norm_num) (by rw [List.mem_toArray]; simp [CFSG.KD.Fi24OrbL.lv])

theorem card_lvl5 : Nat.card (lvl 5) = 3 := by
  rw [CFSG.Sporadic.Fi24.chain_facts'.2.2 5 (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num),
    CFSG.Sporadic.Fi24.chainBase_size]
  rw [show Finset.Ico 5 6 = {5} by decide, Finset.prod_singleton,
    CFSG.Sporadic.Fi24.tree_size_of (l := 5) rfl]

theorem L24_val (hB : Bridge) (x : ℕ) (hx : x < 306936) : idx 306936 L24 x = LN NW 24 x := by
  rw [idx_of_lt _ hx]
  exact hB.letter 24 (by norm_num) ⟨x, hx⟩

theorem mv4_facts (hB : Bridge) : idx 306936 L24 4 ≠ 4 ∧ idx 306936 (L24 ^ 2) 4 ≠ 4 := by
  have h := CFSG.KD.Fi24Sev.Ck.mv4_t
  unfold CFSG.KD.Fi24Sev.mv4 at h
  obtain ⟨h1, h2⟩ := andB_true' h
  simp only [letN_eq] at h1 h2
  have e1 : LN NW 24 4 ≠ 4 := fun e => by rw [e, Nat.beq_refl] at h1; exact absurd h1 (by decide)
  have e2 : LN NW 24 (LN NW 24 4) ≠ 4 := fun e => by
    rw [e, Nat.beq_refl] at h2; exact absurd h2 (by decide)
  have hl : LN NW 24 4 < 306936 := by rw [← L24_val hB 4 (by norm_num)]; exact idx_lt _ (by norm_num)
  refine ⟨by rw [L24_val hB 4 (by norm_num)]; exact e1, ?_⟩
  rw [pow_two, idx_mul, L24_val hB 4 (by norm_num), L24_val hB _ hl]
  exact e2

theorem lvl5_cases (hB : Bridge) {g : J} (hg : g ∈ lvl 5) : g = 1 ∨ g = L24 ∨ g = L24 ^ 2 := by
  classical
  have hl1 : L24 ≠ 1 := fun e => (mv4_facts hB).1 (by rw [e, idx_one])
  set h : lvl 5 := ⟨L24, L24_mem⟩ with hh
  have hfin : Finite (lvl 5) := Nat.finite_of_card_ne_zero (by rw [card_lvl5]; norm_num)
  have ho : orderOf h = 3 := by
    have hd : orderOf h ∣ 3 := by
      have := orderOf_dvd_natCard h
      rwa [card_lvl5] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with e | e
    · exact absurd (Subtype.ext_iff.1 (orderOf_eq_one_iff.1 e)) hl1
    · exact e
  have htop : Subgroup.zpowers h = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, card_lvl5]
  have hmem : (⟨g, hg⟩ : lvl 5) ∈ Subgroup.zpowers h := by rw [htop]; trivial
  rw [mem_zpowers_iff_mem_range_orderOf, ho, Finset.mem_image] at hmem
  obtain ⟨n, hn, e⟩ := hmem
  rw [Finset.mem_range] at hn
  have ev := congrArg Subtype.val e
  simp only [SubmonoidClass.coe_pow, hh] at ev
  interval_cases n
  · exact Or.inl (by rw [← ev, pow_zero])
  · exact Or.inr (Or.inl (by rw [← ev, pow_one]))
  · exact Or.inr (Or.inr ev.symm)

theorem eq_one_of_fixA (hB : Bridge) {g : J} (h5 : ∀ j < 5, idx 306936 g (cb.getD j 0) = cb.getD j 0)
    (h4 : idx 306936 g 4 = 4) : g = 1 := by
  have hg : g ∈ lvl 5 := mem_lvl_of_fix (by norm_num) fun t ht => by
    rw [cbG (by omega)]
    exact h5 t ht
  rcases lvl5_cases hB hg with e | e | e
  · exact e
  · exact absurd (by rw [← e]; exact h4) (mv4_facts hB).1
  · exact absurd (by rw [← e]; exact h4) (mv4_facts hB).2

theorem eq_one_of_fixB {g : J} (h6 : ∀ j < 6, idx 306936 g (cb.getD j 0) = cb.getD j 0) : g = 1 := by
  refine eq_of_base fun t ht => ?_
  apply Fin.ext
  rw [one_smul]
  have e : idx 306936 g CFSG.Sporadic.Fi24.Native.chainBase[t]! =
      CFSG.Sporadic.Fi24.Native.chainBase[t]! := by
    rw [cbG ht]
    exact h6 t ht
  rw [idx_of_lt g (cb_lt t ht)] at e
  exact e

theorem strip_spec (hB : Bridge) : ∀ (ts : List (List ℕ)) (i : ℕ) (C c' : List ℕ) (u : J),
    i + ts.length = 5 → u ∈ lvl i → C.length = 6 →
    (∀ j < 6, idx 306936 u (cb.getD j 0) = C.getD j 0) → stripL NW NT ts i C = some c' →
    ∃ u' ∈ lvl 5, idx 306936 u' (cb.getD 5 0) = c'.getD 5 0
  | [], i, C, c', u, hi, hu, _, hC, hs => by
    simp only [stripL, Option.some.injEq] at hs
    subst hs
    simp only [List.length_nil, add_zero] at hi
    subst hi
    exact ⟨u, hu, hC 5 (by norm_num)⟩
  | t :: ts, i, C, c', u, hi, hu, hlen, hC, hs => by
    simp only [stripL] at hs
    split_ifs at hs with hcond
    obtain ⟨ht, htc⟩ := hcond
    simp only [List.length_cons] at hi
    have hi4 : i ≤ 4 := by omega
    have htl : ∀ l ∈ t, l < 26 := fun l hl => (ht l hl).2
    set T := wordElt t with hT
    have hTm : T ∈ lvl i := wordElt_mem_lvl hi4 ht
    have hCl : ∀ j < 6, C.getD j 0 < 306936 := fun j hj => by
      rw [← hC j hj]
      exact idx_lt _ (cb_lt' hj)
    have hfix : idx 306936 (T⁻¹ * u) (cb.getD i 0) = cb.getD i 0 := by
      rw [idx_mul, hC i (by omega), ← htc, cP_idx hB htl (cb_lt' (by omega)), idx_inv_idx]
    have hu' : T⁻¹ * u ∈ lvl (i + 1) := by
      have hm : T⁻¹ * u ∈ lvl i := (lvl i).mul_mem ((lvl i).inv_mem hTm) hu
      refine (CFSG.Sporadic.Fi24.chain_facts'.2.1 i
        (by rw [CFSG.Sporadic.Fi24.chainBase_size]; omega) _ hm).1 ?_
      rw [cbG (by omega)]
      exact hfix
    refine strip_spec hB ts (i + 1) _ c' (T⁻¹ * u) (by omega) hu' (by simpa using hlen) ?_ hs
    intro j hj
    rw [getD_map_of_lt _ (by omega), idx_mul, hC j hj,
      cP_idx hB (CFSG.KD.Fi24ThreeO.invC_lt htl) (hCl j hj), wordElt_invC hB htl]

open CFSG.KD.Fi24Sev (wrA wsA omA cvA cwA szA repsA rfA bpA bposA bwA bsA wrB wsB omB cvB cwB szB
  repsB rfB bpB bposB bwB bsB twB)

@[expose] def SideOK (w : List ℕ) (ws : List (List ℕ)) (om : ℕ) (reps : List ℕ)
    (rf : List (List (ℕ × ℕ) × ℕ × ℕ × ℕ)) (bp : List (ℕ × ℕ)) (bpos bw : List ℕ) : Prop :=
  (∀ l ∈ w, l < 26) ∧ (∀ u ∈ ws, ∀ l ∈ u, l < 26) ∧ om < 306936 ∧ (∀ q ∈ reps, q < 306936) ∧
    rf.length ≤ reps.length ∧
    (∀ i < rf.length, rf[i]!.2.2.2 ≤ 7 ∧ ProgOK rf[i]!.2.2.2 rf[i]!.1 ∧
      rf[i]!.2.1 < rf[i]!.2.2.2 + rf[i]!.1.length ∧ rf[i]!.2.2.1 < rf[i]!.2.2.2 + rf[i]!.1.length) ∧
    ProgOK 7 bp ∧ bpos.length = 6 ∧ (∀ k ∈ bpos, k < 7 + bp.length) ∧ (∀ l ∈ bw, l < 26)

theorem sideA : SideOK wrA wsA omA repsA rfA bpA bposA bwA := by
  unfold SideOK
  decide +kernel

theorem sideB : SideOK wrB wsB omB repsB rfB bpB bposB bwB := by
  unfold SideOK
  decide +kernel

theorem bsA_eq : bsA = [0, 305530, 5604, 221549, 266275, 4] := by decide +kernel

theorem bsB_eq : bsB = cb := by decide +kernel

theorem repsA_len : repsA.length = rfA.length := by decide +kernel

theorem repsB_len : repsB.length = rfB.length + 1 ∧ repsB.getD rfB.length 0 = (twB.headD (0, [])).1 ∧
    twB.length = 1 := by decide +kernel

theorem comm_of_rel (hB : Bridge) {w : List ℕ} {ws : List (List ℕ)} (hw : ∀ l ∈ w, l < 26)
    (hws : ∀ u ∈ ws, ∀ l ∈ u, l < 26) (h : relOK NW NT w ws = true) :
    ∀ u ∈ ws, wordElt u * wordElt w = wordElt w * wordElt u := by
  intro u hu
  have hc := (relOK_spec h).2 u hu
  have huw : ∀ l ∈ u ++ w, l < 26 := fun l hl => by
    rcases List.mem_append.1 hl with h' | h'
    · exact hws u hu l h'
    · exact hw l h'
  have hwu : ∀ l ∈ w ++ u, l < 26 := fun l hl => by
    rcases List.mem_append.1 hl with h' | h'
    · exact hw l h'
    · exact hws u hu l h'
  rw [← wordElt_append, ← wordElt_append]
  refine eq_of_base fun t ht => Fin.ext ?_
  rw [word_val hB _ huw, word_val hB _ hwu]
  have hmem : CFSG.Sporadic.Fi24.Native.chainBase[t]! ∈ cb := by
    rw [cbG ht, List.getD_eq_getElem _ _ (by simpa [cb] using ht)]
    exact List.getElem_mem _
  exact hc _ hmem

theorem rep_of_ref (hB : Bridge) {w : List ℕ} {ws : List (List ℕ)} {om : ℕ} {reps : List ℕ}
    {rf : List (List (ℕ × ℕ) × ℕ × ℕ × ℕ)} {bp : List (ℕ × ℕ)} {bpos bw : List ℕ}
    (hS : SideOK w ws om reps rf bp bpos bw) (h : refsOK NW NT CFSG.KD.Fi24Sev.OL w om reps rf = true)
    {i : ℕ} (hi : i < rf.length) (g : J) (hc : g * wordElt w = wordElt w * g) :
    idx 306936 g om ≠ reps.getD i 0 := by
  obtain ⟨hw, -, hom, hreps, hlen, hrf, -⟩ := hS
  obtain ⟨hn, hP, ha, hb⟩ := hrf i hi
  have hq : reps.getD i 0 < 306936 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hreps _ (List.getElem_mem _)
  obtain ⟨e1, e2⟩ := refsOK_spec CFSG.KD.Fi24ThreeO.vn (by omega) h i hi (by omega) hn
  exact not_conj_of_ref hB hw hom hP ha hb e1 e2 g hc

theorem base_fix (hB : Bridge) {w : List ℕ} {ws : List (List ℕ)} {om : ℕ} {reps : List ℕ}
    {rf : List (List (ℕ × ℕ) × ℕ × ℕ × ℕ)} {bp : List (ℕ × ℕ)} {bpos bw bs : List ℕ}
    (hS : SideOK w ws om reps rf bp bpos bw)
    (h : baseOK NW NT CFSG.KD.Fi24Sev.OL w om bp bpos bw bs = true)
    (hbs : ∀ j < 6, bs.getD j 0 < 306936) (g : J) (hc : g * wordElt w = wordElt w * g) (hg : idx 306936 g om = om) :
    ∀ j < 6, idx 306936 ((wordElt bw)⁻¹ * g * wordElt bw) (bs.getD j 0) = bs.getD j 0 := by
  obtain ⟨hw, -, hom, -, -, -, hP, hpl, hpos, hbw⟩ := hS
  obtain ⟨hlen, hb⟩ := baseOK_spec CFSG.KD.Fi24ThreeO.vn (by omega) h
  obtain ⟨e, hlt⟩ := cfgT_map hB hw hc hom hP
  rw [hg] at e
  have hZl : (cfgL DK (tupN (cP NW NT w) om 7) bp).length = 7 + bp.length := by
    rw [cfgL_length, tupN_length]
  intro j hj
  have hk : bpos.getD j 0 < 7 + bp.length := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hpos _ (List.getElem_mem _)
  have hbj := hb j (by omega)
  change cP NW NT bw (bs.getD j 0) = (cfgL DK (tupN (cP NW NT w) om 7) bp).getD (bpos.getD j 0) 0 at hbj
  have hfix : idx 306936 g ((cfgL DK (tupN (cP NW NT w) om 7) bp).getD (bpos.getD j 0) 0) =
      (cfgL DK (tupN (cP NW NT w) om 7) bp).getD (bpos.getD j 0) 0 := by
    conv_rhs => rw [e]
    rw [getD_map_of_lt _ (by omega)]
  have hpt : (cfgL DK (tupN (cP NW NT w) om 7) bp).getD (bpos.getD j 0) 0 < 306936 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hlt _ (List.getElem_mem _)
  rw [← hbj, cP_idx hB hbw (hbs j hj)] at hfix
  rw [idx_mul, idx_mul, hfix, idx_inv_idx]

theorem mem_reps {reps : List ℕ} {q : ℕ} (hq : q ∈ reps) : ∃ i < reps.length, reps.getD i 0 = q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩

theorem conj_one {u g : J} (h : u⁻¹ * g * u = 1) : g = 1 := by
  calc g = u * (u⁻¹ * g * u) * u⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem card_cent_A (hB : Bridge) :
    Nat.card (Subgroup.centralizer ({wordElt wrA} : Set J)) = 17640 := by
  have hS := sideA
  obtain ⟨hw, hws, hom, -, -, -, -, -, -, hbw⟩ := hS
  obtain ⟨F, hF1, hF2, hF3⟩ := covOK_spec CFSG.KD.Fi24ThreeO.vn CFSG.KD.Fi24Sev.Ck.covA_t
  have hsz : szA = 17640 := by decide +kernel
  rw [hsz] at hF2
  refine card_cent hB hw hws hom hF1 hF2 hF3
    (comm_of_rel hB hw hws CFSG.KD.Fi24Sev.Ck.relA_t) (fun q hq g hc => ?_) (fun g hc hg => ?_)
  · obtain ⟨i, hi, rfl⟩ := mem_reps hq
    exact rep_of_ref hB sideA CFSG.KD.Fi24Sev.Ck.refA_t (by rw [← repsA_len]; exact hi) g hc
  · have hfix := base_fix hB sideA CFSG.KD.Fi24Sev.Ck.baseA_t
      (fun j hj => by rw [bsA_eq]; interval_cases j <;> decide) g hc hg
    refine conj_one (u := wordElt bwA) (eq_one_of_fixA hB (fun j hj => ?_) ?_)
    · have := hfix j (by omega)
      rw [bsA_eq] at this
      interval_cases j <;> exact this
    · have := hfix 5 (by norm_num)
      rw [bsA_eq] at this
      exact this

theorem twin_not (hB : Bridge) (g : J) (hc : g * wordElt wrB = wordElt wrB * g) :
    idx 306936 g omB ≠ repsB.getD rfB.length 0 := by
  intro hgq
  obtain ⟨hw, -, hom, -, -, -, hP, hpl, hpos, hbw⟩ := sideB
  obtain ⟨hl1, hl2, hl3⟩ := repsB_len
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl3
  have ht := allL_spec CFSG.KD.Fi24Sev.Ck.twin_t x (by rw [hx]; exact List.mem_singleton_self x)
  have hxq : x.1 = repsB.getD rfB.length 0 := by rw [hl2, hx]; rfl
  have hq : x.1 < 524288 := by
    have := idx_lt g hom
    rw [hxq, ← hgq]
    omega
  obtain ⟨hts, hposl, c, hstrip, n1, n2, n3⟩ := twinOK_spec CFSG.KD.Fi24ThreeO.vn hq ht
  obtain ⟨-, hb⟩ := baseOK_spec CFSG.KD.Fi24ThreeO.vn (by omega) CFSG.KD.Fi24Sev.Ck.baseB_t
  obtain ⟨e, hlt⟩ := cfgT_map hB hw hc hom hP
  rw [hgq, ← hxq] at e
  have hZl : (cfgL DK (tupN (cP NW NT wrB) omB 7) bpB).length = 7 + bpB.length := by
    rw [cfgL_length, tupN_length]
  set C := bposB.map fun k => (cfgL DK (tupL (cP NW NT wrB) x.1) bpB).getD k 0 with hC
  have hCv : ∀ j < 6, idx 306936 (g * wordElt bwB) (cb.getD j 0) = C.getD j 0 := by
    intro j hj
    have hk : bposB.getD j 0 < 7 + bpB.length := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hpos _ (List.getElem_mem _)
    have hbj := hb j (by omega)
    rw [bsB_eq] at hbj
    change cP NW NT bwB (cb.getD j 0) = (cfgL DK (tupN (cP NW NT wrB) omB 7) bpB).getD
      (bposB.getD j 0) 0 at hbj
    rw [hC, getD_map_of_lt _ (by omega), show tupL (cP NW NT wrB) x.1 = tupN (cP NW NT wrB) x.1 7
      from rfl, e, getD_map_of_lt _ (by omega), ← hbj, idx_mul, cP_idx hB hbw (cb_lt' hj)]
  obtain ⟨u', hu', hu5⟩ := strip_spec hB _ 0 C c (g * wordElt bwB) (by omega)
    (CFSG.Sporadic.Fi24.mem_lvl_zero _) (by rw [hC, List.length_map]; omega) hCv hstrip
  have hb5 : cb.getD 5 0 = 186844 := rfl
  rw [hb5] at hu5
  rcases lvl5_cases hB hu' with h1 | h1 | h1
  · rw [h1, idx_one] at hu5
    exact n1 hu5.symm
  · rw [h1, L24_val hB _ (by norm_num)] at hu5
    exact n2 hu5.symm
  · have hl : LN NW 24 186844 < 306936 := by
      rw [← L24_val hB 186844 (by norm_num)]
      exact idx_lt _ (by norm_num)
    rw [h1, pow_two, idx_mul, L24_val hB 186844 (by norm_num), L24_val hB _ hl] at hu5
    exact n3 hu5.symm

theorem card_cent_B (hB : Bridge) :
    Nat.card (Subgroup.centralizer ({wordElt wrB} : Set J)) = 2058 := by
  obtain ⟨hw, hws, hom, -, -, -, -, -, -, hbw⟩ := sideB
  obtain ⟨F, hF1, hF2, hF3⟩ := covOK_spec CFSG.KD.Fi24ThreeO.vn CFSG.KD.Fi24Sev.Ck.covB_t
  have hsz : szB = 2058 := by decide +kernel
  rw [hsz] at hF2
  refine card_cent hB hw hws hom hF1 hF2 hF3
    (comm_of_rel hB hw hws CFSG.KD.Fi24Sev.Ck.relB_t) (fun q hq g hc => ?_) (fun g hc hg => ?_)
  · obtain ⟨i, hi, rfl⟩ := mem_reps hq
    rcases Nat.lt_or_ge i rfB.length with h | h
    · exact rep_of_ref hB sideB CFSG.KD.Fi24Sev.Ck.refB_t h g hc
    · have : i = rfB.length := by have := repsB_len.1; omega
      rw [this]
      exact twin_not hB g hc
  · have hfix := base_fix hB sideB CFSG.KD.Fi24Sev.Ck.baseB_t
      (fun j hj => by rw [bsB_eq]; exact cb_lt' hj) g hc hg
    refine conj_one (u := wordElt bwB) (eq_one_of_fixB fun j hj => ?_)
    have := hfix j hj
    rw [bsB_eq] at this
    exact this

end CFSG.KD.Fi24Sev.Cent

end
