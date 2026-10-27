module

public import Certificates.Kernel.RuBorel.Checks
public import Certificates.Kernel.RuSz.Final
public import Certificates.Kernel.Tc.RuThreeFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzInvCent
public import CFSG.Sporadic.Schreier.Co3ChainUtil
public import CFSG.Certificates.Kernel.Misc.RuInvPack

public noncomputable section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelRuBorel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.RuInv
  CFSG.KC.Misc.RuInv.P CFSG.KS.MoveK CertificateChecks.KernelSporSch CertificateChecks.KernelRuSz
  CFSG.EvenSporadicStandard.Induction.RuSz CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Certificates CFSG.Certificates.Native
open CFSG.KS.Raw.Orb (PRep prep_of_rep)
open CFSG.KC.Misc.RuBase (apP_mulP)

@[expose] def sJ (j : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruField4060 3)[j]!

@[expose] def prodJ (v : List ℕ) : Equiv.Perm (Fin 4060) := (v.map sJ).prod

theorem prep_S {j : ℕ} (hj : j < 18) : PRep 4060 12 (RuJO.S j) (sJ j) := by
  have hb := RuJ.bindsO.2.2.2.2.1 j hj
  have hp := Orb.allN_iff.1 RuJ.permO j hj
  have hinv := invEqK_sound hp
  have hrep : Rep 4060 (unpack 4060 12 (RuJO.S j)) (permOfArr 4060 (unpack 4060 12 (RuJO.S j))) :=
    (rep_permOfArr hinv.2).1
  unfold sJ
  rw [hb]
  exact prep_of_rep hrep

theorem prep_wordJ : ∀ v : List ℕ, (∀ j ∈ v, j < 18) → PRep 4060 12 (wordJ v) (prodJ v)
  | [], _ => by
    have e1 : prodJ [] = 1 := by simp [prodJ]
    have e2 : wordJ [] = idP := rfl
    rw [e1, e2]
    exact prep_idP
  | j :: v, hv => by
    have e : wordJ (j :: v) = mulP (RuJO.S j) (wordJ v) :=
      Orb.strictN_eq (wordJ v) fun X => mulP (RuJO.S j) X
    have ep : prodJ (j :: v) = sJ j * prodJ v := by
      simp only [prodJ, List.map_cons, List.prod_cons]
    rw [e, ep]
    exact prep_mulP (prep_S (hv j (List.mem_cons_self ..)))
      (prep_wordJ v fun i hi => hv i (List.mem_cons_of_mem _ hi))


theorem prodJ_mem (v : List ℕ) (hv : ∀ j ∈ v, j < 18) : prodJ v ∈ ruP := by
  unfold prodJ
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact CertificateChecks.KernelTc.Ru.strong_mem (hv j hj)

theorem prep_kG (w : String) : PRep 4060 12 (wP w) (kG w) := fun x => by
  have h1 := (tr_kTab w).2 x.val x.2
  have h2 := ap_kTab w x
  change apP (wP w) x.val = (kG w x).val
  rw [← h2, h1]
  rfl

theorem apP_of {P : ℕ} {g : Equiv.Perm (Fin 4060)} (h : PRep 4060 12 P g) {i : ℕ}
    (hi : i < 4060) : apP P i = (g ⟨i, hi⟩).val := h ⟨i, hi⟩

theorem comm_of {P Q : ℕ} {g h : Equiv.Perm (Fin 4060)} (hP : PRep 4060 12 P g)
    (hQ : PRep 4060 12 Q h) (e : commB P Q = true) : g * h = h * g :=
  prep_unique (prep_mulP hP hQ) (by rw [Nat.eq_of_beq_eq_true e]; exact prep_mulP hQ hP)

theorem comm4_spec {X : ℕ} (h : comm4 (wP (rWords.getD 0 "")) (wP (rWords.getD 1 ""))
    (wP (rWords.getD 2 "")) (wP (rWords.getD 3 "")) X = true) :
    ∀ j < 4, commB (wP (rWords.getD j "")) X = true := by
  unfold comm4 at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro j hj
  interval_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem cent_parts : Nat.beq (mulP x0P x0P) idP = true ∧ (!(Nat.beq (apP x0P 2) 2)) = true ∧
    (∀ j < 4, commB (wP (rWords.getD j "")) x0P = true) ∧
    ∀ w ∈ borelGens, ∀ j < 4,
      commB (wP (rWords.getD j "")) (mulP (mulP (invP (wP w)) x0P) (wP w)) = true := by
  have h := cent_ok
  simp only [centB, Orb.strictB_eq, bAnd_iff, List.all_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, comm4_spec h3, fun w hw => comm4_spec (h4 w hw)⟩

theorem x_sq : kG x0Word * kG x0Word = 1 := by
  have e := Nat.eq_of_beq_eq_true cent_parts.1
  have h := prep_mulP (prep_kG x0Word) (prep_kG x0Word)
  change PRep 4060 12 (mulP x0P x0P) _ at h
  rw [e] at h
  exact prep_unique h prep_idP

theorem x_ne_one : kG x0Word ≠ 1 := by
  intro e
  have h := cent_parts.2.1
  rw [Bool.not_eq_true'] at h
  change Nat.beq (apP (wP x0Word) 2) 2 = false at h
  rw [apP_of (prep_kG x0Word) (by norm_num : 2 < 4060), e] at h
  simp at h

@[expose] def R1 : Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure (Set.range fun j : Fin 4 => kG (rWords.getD j.val ""))

@[expose] def chainOK : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | acc, c :: cs => acc.contains c.1 && chainOK (c.2.2 :: acc) cs

theorem reach {P : ℕ → Prop} : ∀ (rows : List (ℕ × ℕ × ℕ)) (acc : List ℕ),
    (∀ c ∈ rows, P c.1 → P c.2.2) → (∀ p ∈ acc, P p) → chainOK acc rows = true →
      ∀ c ∈ rows, P c.2.2
  | [], _, _, _, _ => by simp
  | c :: cs, acc, hs, ha, hc => by
    simp only [chainOK, Bool.and_eq_true, List.contains_iff_mem] at hc
    have hc1 : P c.2.2 := hs c (List.mem_cons_self ..) (ha _ hc.1)
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hc1
    · refine reach cs (c.2.2 :: acc) (fun e he => hs e (List.mem_cons_of_mem _ he)) ?_ hc.2 d hd
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hc1
      · exact ha p hp

theorem orb_parts : ∀ c ∈ orbRows, apP (wP (rWords.getD c.2.1 "")) c.1 = c.2.2 := by
  have h := orb_ok
  simp only [orbB, orbRowsB, Orb.strictB_eq, List.all_eq_true] at h
  intro c hc
  have hj : c.2.1 < 4 := by
    have : ∀ d ∈ orbRows, d.2.1 < 4 := by decide
    exact this c hc
  have e : sel4 (wP (rWords.getD 0 "")) (wP (rWords.getD 1 "")) (wP (rWords.getD 2 ""))
      (wP (rWords.getD 3 "")) c.2.1 = wP (rWords.getD c.2.1 "") := by
    generalize c.2.1 = j at hj
    interval_cases j <;> rfl
  rw [← e]
  exact Nat.eq_of_beq_eq_true (h c hc)

@[expose] def orbPts : List ℕ := 2 :: orbRows.map fun c => c.2.2

theorem orbPts_mem : ∀ p ∈ orbPts, ∃ hp : p < 4060, ∃ g ∈ R1, g ⟨2, by norm_num⟩ = ⟨p, hp⟩ := by
  have hlt : ∀ c ∈ orbRows, c.1 < 4060 ∧ c.2.1 < 4 := by decide
  have hs : ∀ c ∈ orbRows, (∃ hp : c.1 < 4060, ∃ g ∈ R1, g ⟨2, by norm_num⟩ = ⟨c.1, hp⟩) →
      ∃ hp : c.2.2 < 4060, ∃ g ∈ R1, g ⟨2, by norm_num⟩ = ⟨c.2.2, hp⟩ := by
    rintro c hc ⟨hp, g, hg, hg2⟩
    have hj := (hlt c hc).2
    have e := orb_parts c hc
    rw [apP_of (prep_kG _) hp] at e
    refine ⟨by rw [← e]; exact Fin.isLt _, kG (rWords.getD c.2.1 "") * g,
      R1.mul_mem (Subgroup.subset_closure ⟨⟨c.2.1, hj⟩, rfl⟩) hg, Fin.ext ?_⟩
    rw [Equiv.Perm.mul_apply, hg2]
    exact e
  have h0 : ∃ hp : 2 < 4060, ∃ g ∈ R1, g ⟨2, by norm_num⟩ = ⟨2, hp⟩ :=
    ⟨by norm_num, 1, R1.one_mem, rfl⟩
  have hc : chainOK [2] orbRows = true := by decide
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h0
  · obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hp
    exact reach (P := fun p => ∃ hp : p < 4060, ∃ g ∈ R1, g ⟨2, by norm_num⟩ = ⟨p, hp⟩)
      orbRows [2] hs (fun p hp => by
        rw [List.mem_singleton] at hp
        rw [hp]
        exact h0) hc c hc'

theorem card_R1 : 64 ≤ Nat.card R1 := by
  have hlen : orbPts.length = 64 := by decide
  have hnd : orbPts.Nodup := by decide
  choose hlt g hg hg2 using fun i : Fin 64 =>
    orbPts_mem (orbPts[i.val]'(by rw [hlen]; exact i.2)) (List.getElem_mem _)
  let F : Fin 64 → R1 := fun i => ⟨g i, hg i⟩
  have hF : Function.Injective F := by
    intro i j hij
    have e : g i = g j := congrArg Subtype.val hij
    have e2 := congrArg (fun h : Equiv.Perm (Fin 4060) => (h ⟨2, by norm_num⟩).val) e
    simp only [hg2] at e2
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 e2)
  have := Nat.card_le_card_of_injective F hF
  simpa using this

theorem R1_eq : R1 = K0 ⊓ Subgroup.centralizer ({kG x0Word} : Set (Equiv.Perm (Fin 4060))) := by
  have hle : R1 ≤ K0 ⊓ Subgroup.centralizer ({kG x0Word} : Set (Equiv.Perm (Fin 4060))) := by
    rw [R1, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨kG_mem _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of (prep_kG _) (prep_kG _) (cent_parts.2.2.1 j.val j.2)
  have h2 : orderOf (kG x0Word) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact x_sq) x_ne_one
  have hc := card_centK0 (kG_mem x0Word) h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; exact card_R1)

theorem comm_y {w : String} (hw : w ∈ borelGens) {r : Equiv.Perm (Fin 4060)} (hr : r ∈ K0)
    (hrx : r * kG x0Word = kG x0Word * r) :
    r * ((kG w)⁻¹ * kG x0Word * kG w) = ((kG w)⁻¹ * kG x0Word * kG w) * r := by
  have hmem : r ∈ R1 := by
    rw [R1_eq]
    exact ⟨hr, Subgroup.mem_centralizer_singleton_iff.2 hrx⟩
  have hle : R1 ≤ Subgroup.centralizer
      ({(kG w)⁻¹ * kG x0Word * kG w} : Set (Equiv.Perm (Fin 4060))) := by
    rw [R1, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (comm_of (prep_kG _)
      (prep_mulP (prep_mulP (prep_invP (prep_kG w)) (prep_kG x0Word)) (prep_kG w))
      (cent_parts.2.2.2 w hw j.val j.2))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)

theorem fix_parts : Nat.beq (apP (wP (hBWords.getD 0 "")) 0) 0 = true ∧
    Nat.beq (apP (wP (hBWords.getD 1 "")) 0) 0 = true ∧
    Nat.beq (apP (wP (hBWords.getD 2 "")) 0) 0 = true ∧
    ((List.range 4060).filter (fun x =>
      bAnd(Nat.beq (apP (wP (hBWords.getD 0 "")) x) x, bAnd(Nat.beq (apP (wP (hBWords.getD 1 ""))
        x) x, Nat.beq (apP (wP (hBWords.getD 2 "")) x) x))) == [0, 1, 3645, 3692]) = true ∧
    Nat.beq (apP (wP k1Word) 0) 1 = true := by
  have h := fix_ok
  simp only [fixB, fixWB, Orb.strictB_eq] at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff] at h
  exact h

theorem hB_cases {w : String} (hw : w ∈ hBWords) :
    w = hBWords.getD 0 "" ∨ w = hBWords.getD 1 "" ∨ w = hBWords.getD 2 "" := by
  simp only [hBWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  exact hw

theorem h_zero {w : String} (hw : w ∈ hBWords) :
    kG w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  obtain ⟨h0, h1, h2, -, -⟩ := fix_parts
  apply Fin.ext
  rw [← apP_of (prep_kG w) (by norm_num : 0 < 4060)]
  rcases hB_cases hw with rfl | rfl | rfl
  · exact Nat.eq_of_beq_eq_true h0
  · exact Nat.eq_of_beq_eq_true h1
  · exact Nat.eq_of_beq_eq_true h2

theorem fix_mem (p : Fin 4060) (hp : ∀ w ∈ hBWords, kG w p = p) :
    p.val ∈ [0, 1, 3645, 3692] := by
  obtain ⟨-, -, -, hf, -⟩ := fix_parts
  rw [beq_iff_eq] at hf
  rw [← hf, List.mem_filter]
  have ef : ∀ i < 3, apP (wP (hBWords.getD i "")) p.val = p.val := by
    intro i hi
    rw [apP_of (prep_kG _) p.2]
    have hm : hBWords.getD i "" ∈ hBWords := by
      interval_cases i <;> simp [hBWords]
    exact congrArg Fin.val (hp _ hm)
  refine ⟨List.mem_range.2 p.2, ?_⟩
  beta_reduce
  rw [bAnd_iff, bAnd_iff, ef 0 (by norm_num), ef 1 (by norm_num), ef 2 (by norm_num)]
  exact ⟨Nat.beq_refl _, Nat.beq_refl _, Nat.beq_refl _⟩

theorem k1_zero : kG k1Word ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := by
  apply Fin.ext
  rw [← apP_of (prep_kG k1Word) (by norm_num : 0 < 4060)]
  exact Nat.eq_of_beq_eq_true fix_parts.2.2.2.2

theorem tail_parts : Nat.beq (apP (wordJ qWord) 0) 0 = true ∧
    Nat.beq (apP (wordJ qWord) 1) 896 = true ∧ Nat.beq (apP (wordJ qWord) 2) 3739 = true ∧
    (∀ c ∈ pathSteps,
      Nat.beq (apP (nIf(Nat.beq c.1 1, wP n1Word, wP n2Word)) c.2.1) c.2.2 = true) ∧
    ∀ c ∈ tailRows, tailRowB (mulP (mulP (invP (wordJ qWord)) (wP n1Word)) (wordJ qWord)) c =
      true := by
  have h := tail_ok
  simp only [tailB, Orb.strictB_eq] at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, List.all_eq_true, List.all_eq_true] at h
  exact h

theorem tailRow_spec {X : ℕ} {c : ℕ × List ℕ × ℕ} (h : tailRowB X c = true) :
    apP (wordJ c.2.1) 0 = 0 ∧ apP (wordJ c.2.1) 1 = 1 ∧ apP (wordJ c.2.1) 2 = 2 ∧
      apP (wordJ c.2.1) 3 = c.1 ∧
      apP (wordJ c.2.1) (apP X c.2.2) ≠ apP X (apP (wordJ c.2.1) c.2.2) := by
  unfold tailRowB at h
  rw [Orb.strictB_eq, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, Bool.not_eq_true'] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, fun e => ?_⟩
  rw [e, Nat.beq_refl] at h4
  cases h4

theorem fixes_of_comm {k g : Equiv.Perm (Fin 4060)} (hcomm : g * k = k * g) {a b : Fin 4060}
    (hk : k a = b) (hg : g a = a) : g b = b := by
  calc g b = g (k a) := by rw [hk]
    _ = (g * k) a := rfl
    _ = (k * g) a := by rw [hcomm]
    _ = k (g a) := rfl
    _ = b := by rw [hg, hk]

theorem step_n1 {a b : ℕ} (h : (1, a, b) ∈ pathSteps) (ha : a < 4060) (hb : b < 4060) :
    kG n1Word ⟨a, ha⟩ = ⟨b, hb⟩ := by
  have e := tail_parts.2.2.2.1 _ h
  apply Fin.ext
  rw [← apP_of (prep_kG n1Word) ha]
  exact Nat.eq_of_beq_eq_true e

theorem step_n2 {a b : ℕ} (h : (2, a, b) ∈ pathSteps) (ha : a < 4060) (hb : b < 4060) :
    kG n2Word ⟨a, ha⟩ = ⟨b, hb⟩ := by
  have e := tail_parts.2.2.2.1 _ h
  apply Fin.ext
  rw [← apP_of (prep_kG n2Word) ha]
  exact Nat.eq_of_beq_eq_true e

theorem hbc : ruChainJoin.baseCount = 4 := rfl

theorem mem_lev3 {h : Equiv.Perm (Fin 4060)} (hP : h ∈ ruP)
    (h0 : h ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) (h1 : h ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩)
    (h2 : h ⟨2, by norm_num⟩ = ⟨2, by norm_num⟩) : h ∈ ruChainJoin.levelSubgroup 3 := by
  have hQ : ValidSchreier ruChainJoin := ruChain_valid ruChainJoin_check.1
  rw [ruChainJoin.mem_levelSubgroup_iff hQ 3 (by decide)]
  refine ⟨by rw [ruChainJoin_sub, ← ruP_eq_sup]; exact hP, ?_⟩
  intro b hb
  have e : ruChainJoin.base.toList = ruFinList 4060 (by decide) ruJoinBase :=
    RawSchreierDatum.ofArrays_base_toList
  rw [e] at hb
  simp [ruFinList, ruJoinBase] at hb
  rcases hb with rfl | rfl | rfl
  · simpa using h0
  · simpa using h1
  · simpa using h2

theorem card_lev3 : Nat.card (ruChainJoin.levelSubgroup 3) = 32 := by
  have hQ : ValidSchreier ruChainJoin := ruChain_valid ruChainJoin_check.1
  have hV := validSchreier_of_chainOK CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.ruChainJoin_arrays
    (by norm_num : 0 < 4) ruChainJoin_check.1
  have horb : (List.finRange ruChainJoin.baseCount).map ruChainJoin.orbitSize =
      [4060, 1755, 640, 32] := by
    rw [CFSG.Sporadic.Schreier.Co3.orbitSizes_eq_of_valid
      (by rw [hbc]; simp [ruBaseArr, ruJoinBase]) hV.2]
    exact ruChainJoin_check.2.1
  let i3 : Fin ruChainJoin.baseCount := ⟨3, by rw [hbc]; norm_num⟩
  have h3 : ruChainJoin.orbitSize i3 = 32 := by
    have hl : 3 < ((List.finRange ruChainJoin.baseCount).map ruChainJoin.orbitSize).length := by
      rw [List.length_map, List.length_finRange]
      exact i3.2
    have e1 := List.getElem_of_eq horb hl
    rw [List.getElem_map, List.getElem_finRange] at e1
    exact e1
  have hlev := RawSchreierDatum.level_card_eq_orbit_mul_next ruChainJoin hQ i3
  have h4 : ruChainJoin.levelSubgroup (i3.val + 1) = ⊥ := by
    have := RawSchreierDatum.levelSubgroup_terminal_eq_bot ruChainJoin hQ
    rw [hbc] at this
    exact this
  rw [h4, Subgroup.card_bot, mul_one, ← RawSchreierDatum.orbitSize_eq_card, h3] at hlev
  exact hlev

@[expose] def elems : List (ℕ × List ℕ) := (3, []) :: tailRows.map fun c => (c.1, c.2.1)

theorem elems_lt : ∀ c ∈ elems, ∀ j ∈ c.2, j < 18 := by decide

theorem elems_spec : ∀ c ∈ elems, prodJ c.2 ∈ ruChainJoin.levelSubgroup 3 ∧
    ∃ hc : c.1 < 4060, prodJ c.2 ⟨3, by norm_num⟩ = ⟨c.1, hc⟩ := by
  intro c hc
  have hP := prep_wordJ c.2 (elems_lt c hc)
  rcases List.mem_cons.1 hc with rfl | hc'
  · exact ⟨Subgroup.one_mem _, by norm_num, rfl⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
    have hP : PRep 4060 12 (wordJ d.2.1) (prodJ d.2.1) := hP
    obtain ⟨t0, t1, t2, t3, -⟩ := tailRow_spec (tail_parts.2.2.2.2 d hd)
    have hlt : d.1 < 4060 := by
      have : ∀ e ∈ tailRows, e.1 < 4060 := by decide
      exact this d hd
    have fx : ∀ (a b : ℕ) (ha : a < 4060) (hb : b < 4060), apP (wordJ d.2.1) a = b →
        prodJ d.2.1 ⟨a, ha⟩ = ⟨b, hb⟩ := fun a b ha hb e => by
      apply Fin.ext
      rw [← apP_of hP ha]
      exact e
    refine ⟨mem_lev3 (prodJ_mem _ (elems_lt _ hc)) (fx 0 0 (by norm_num) (by norm_num) t0)
      (fx 1 1 (by norm_num) (by norm_num) t1) (fx 2 2 (by norm_num) (by norm_num) t2), hlt,
      fx 3 d.1 (by norm_num) hlt t3⟩

theorem lev3_eq {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruChainJoin.levelSubgroup 3) :
    ∃ c ∈ elems, prodJ c.2 = g := by
  classical
  let E : Finset (Equiv.Perm (Fin 4060)) := (elems.map fun c => prodJ c.2).toFinset
  have hsub : (E : Set (Equiv.Perm (Fin 4060))) ⊆ ruChainJoin.levelSubgroup 3 := by
    intro h hh
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hh)
    exact (elems_spec c hc).1
  have hnd : (elems.map Prod.fst).Nodup := by decide
  have hmap : (elems.map fun c => prodJ c.2).map (fun h => (h ⟨3, by norm_num⟩).val) =
      elems.map Prod.fst := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    obtain ⟨-, hlt, e⟩ := elems_spec c hc
    simp only [Function.comp_apply, e]
  have hnd2 : (elems.map fun c => prodJ c.2).Nodup := by
    rw [← hmap] at hnd
    exact List.Nodup.of_map _ hnd
  have hE : E.card = 32 := by
    rw [List.toFinset_card_of_nodup hnd2, List.length_map]
    rfl
  have heq : (E : Set (Equiv.Perm (Fin 4060))) = ruChainJoin.levelSubgroup 3 := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hE, ← Nat.card_coe_set_eq]
    exact card_lev3.le
  have hgE : g ∈ (E : Set (Equiv.Perm (Fin 4060))) := by
    rw [heq]
    exact hg
  obtain ⟨c, hc, e⟩ := List.mem_map.1 (List.mem_toFinset.1 hgE)
  exact ⟨c, hc, e⟩

theorem eq_one_tail {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (h0 : g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) (h1 : g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩)
    (c1 : g * kG n1Word = kG n1Word * g) (c2 : g * kG n2Word = kG n2Word * g) : g = 1 := by
  obtain ⟨q0, q1, q2, -, hrows⟩ := tail_parts
  have hql : ∀ j ∈ qWord, j < 18 := by decide
  set q := prodJ qWord with hq
  have hqP := prep_wordJ qWord hql
  have hqm : q ∈ ruP := prodJ_mem qWord hql
  have fq : ∀ (a b : ℕ) (ha : a < 4060) (hb : b < 4060), Nat.beq (apP (wordJ qWord) a) b = true →
      q ⟨a, ha⟩ = ⟨b, hb⟩ := fun a b ha hb e => by
    apply Fin.ext
    rw [← apP_of hqP ha]
    exact Nat.eq_of_beq_eq_true e
  have g3616 := fixes_of_comm c1 (step_n1 (by decide) (by norm_num) (by norm_num : 3616 < 4060)) h0
  have g245 := fixes_of_comm c2 (step_n2 (by decide) (by norm_num) (by norm_num : 245 < 4060))
    g3616
  have g896 := fixes_of_comm c1 (step_n1 (by decide) (by norm_num) (by norm_num : 896 < 4060)) g245
  have g3739 := fixes_of_comm c1 (step_n1 (by decide) (by norm_num) (by norm_num : 3739 < 4060)) h1
  set g' := q⁻¹ * g * q with hg'
  have hfix : ∀ (a b : ℕ) (ha : a < 4060) (hb : b < 4060), q ⟨a, ha⟩ = ⟨b, hb⟩ →
      g ⟨b, hb⟩ = ⟨b, hb⟩ → g' ⟨a, ha⟩ = ⟨a, ha⟩ := fun a b ha hb e1 e2 => by
    rw [hg', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e1, e2, Equiv.Perm.inv_eq_iff_eq]
    exact e1.symm
  have g'0 := hfix 0 0 (by norm_num) (by norm_num) (fq 0 0 (by norm_num) (by norm_num) q0) h0
  have g'1 := hfix 1 896 (by norm_num) (by norm_num) (fq 1 896 (by norm_num) (by norm_num) q1)
    g896
  have g'2 := hfix 2 3739 (by norm_num) (by norm_num)
    (fq 2 3739 (by norm_num) (by norm_num) q2) g3739
  have hg'P : g' ∈ ruP := ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hqm) hg) hqm
  obtain ⟨c, hc, hcg⟩ := lev3_eq (mem_lev3 hg'P g'0 g'1 g'2)
  set X1 := q⁻¹ * kG n1Word * q with hX1
  have hX1P : PRep 4060 12 (mulP (mulP (invP (wordJ qWord)) (wP n1Word)) (wordJ qWord)) X1 :=
    prep_mulP (prep_mulP (prep_invP hqP) (prep_kG n1Word)) hqP
  have hcomm : g' * X1 = X1 * g' := by
    calc g' * X1 = q⁻¹ * (g * kG n1Word) * q := by rw [hg', hX1]; group
      _ = q⁻¹ * (kG n1Word * g) * q := by rw [c1]
      _ = X1 * g' := by rw [hg', hX1]; group
  have hg'1 : g' = 1 := by
    rcases List.mem_cons.1 hc with rfl | hc'
    · rw [← hcg]
      simp [prodJ]
    · exfalso
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
      obtain ⟨-, -, -, -, hne⟩ := tailRow_spec (hrows d hd)
      have hel : d.2.2 < 4060 := by
        have : ∀ e ∈ tailRows, e.2.2 < 4060 := by decide
        exact this d hd
      have hP := prep_wordJ d.2.1 (elems_lt _ hc)
      apply hne
      have h1' := (prep_mulP hP hX1P) ⟨d.2.2, hel⟩
      have h2' := (prep_mulP hX1P hP) ⟨d.2.2, hel⟩
      change apP (mulP (wordJ d.2.1) _) d.2.2 = _ at h1'
      change apP (mulP _ (wordJ d.2.1)) d.2.2 = _ at h2'
      rw [apP_mulP hel] at h1' h2'
      have hcg' : prodJ d.2.1 = g' := hcg
      rw [h1', h2', hcg', hcomm]
  have : g = q * g' * q⁻¹ := by rw [hg']; group
  rw [this, hg'1, mul_one, mul_inv_cancel]

end CertificateChecks.KernelRuBorel

end
