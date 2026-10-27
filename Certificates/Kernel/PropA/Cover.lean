module

public import Certificates.Kernel.PropA.Gens
public import Certificates.Kernel.PropA.Sylow
public import CFSG.Certificates.Kernel.PropA28.Order
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.CheckWord
import CFSG.Certificates.Kernel.OrbRow.PRepFacts
import CFSG.Certificates.Kernel.SporSch.SylowCover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.KS.Raw.Orb CFSG.KS.PRec CFSG.EvenSporadicStandard.M12Std.PropA
  CFSG.EvenSporadicStandard.M12Std.PropA.Native

@[expose] noncomputable def pa450010wv (b : Bool) (kS : ℕ) (wd : List Int) : Perm (Fin 28) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin kS => pa450010gK b h)
    (CFSG.Monster.B.Co2.toLetters kS wd)

@[expose] noncomputable def pa450010x : Perm (Fin 28) := wordP (pa450010gK false) 2 pa450010wx

@[expose] noncomputable def pa450010rep (b : Bool) (i : ℕ) : Perm (Fin 28) :=
  pa450010wv b 4 (pa450010wReps.getD i [])

@[expose] def pa450010sz : List ℕ := [495, 495, 396, 396, 792, 792]

theorem pa450010gK_mem (b : Bool) (j : ℕ) : pa450010gK b j ∈ K28 b := by
  rcases j with _ | _ | _ | _ | j
  · exact subset_closure (by simp [pa450010gK])
  · exact subset_closure (by simp [pa450010gK])
  · exact subset_closure (by simp [pa450010gK])
  · exact subset_closure (by simp [pa450010gK])
  · have e : pa450010gK b (j + 4) = 1 := by simp [pa450010gK]
    rw [e]
    exact one_mem _

theorem pa450010wv_mem (b : Bool) (kS : ℕ) (wd : List Int) : pa450010wv b kS wd ∈ K28 b := by
  refine (closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact pa450010gK_mem b h

theorem pa450010wv_memD (b : Bool) (wd : List Int) : pa450010wv b 2 wd ∈ D28 := by
  refine (closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨⟨h, hh⟩, rfl⟩
  change pa450010gK b h ∈ closure ({pA, pB} : Set (Perm (Fin 28)))
  interval_cases h
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem pa450010wv_eq_wordP (b : Bool) (kS : ℕ) : ∀ wd : List Int,
    (∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ kS) → pa450010wv b kS wd = wordP (pa450010gK b) kS wd
  | [], _ => by
    simp [pa450010wv, wordP, CFSG.Sporadic.Th.wordG, CFSG.Monster.B.Co2.toLetters,
      Quiver.SchreierGraph.evalWord_nil]
  | l :: wd, hw => by
    have hl := hw l List.mem_cons_self
    have ih := pa450010wv_eq_wordP b kS wd fun l' h' => hw l' (List.mem_cons_of_mem _ h')
    have hcons : CFSG.Monster.B.Co2.toLetters kS (l :: wd) =
        (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: CFSG.Monster.B.Co2.toLetters kS wd := by
      simp [CFSG.Monster.B.Co2.toLetters, hl.1, hl.2]
    have hwp : wordP (pa450010gK b) kS (l :: wd) =
        letterG (pa450010gK b) kS l * wordP (pa450010gK b) kS wd := by
      simp [wordP, CFSG.Sporadic.Th.wordG]
    unfold pa450010wv at ih ⊢
    rw [hcons, hwp, ← ih]
    unfold letterG
    by_cases hp : 0 < l
    · rw [decide_eq_true hp, Quiver.SchreierGraph.evalWord_cons_true, if_pos ⟨hp, by omega⟩]
      have e : (l - 1).toNat = l.natAbs - 1 := by omega
      rw [e]
    · rw [decide_eq_false hp, Quiver.SchreierGraph.evalWord_cons_false, if_neg (by omega),
        if_pos ⟨by omega, by omega⟩]
      have e : (-l - 1).toNat = l.natAbs - 1 := by omega
      rw [e]

theorem pa450010_wx_letters (kS : ℕ) (hkS : 2 ≤ kS) :
    ∀ l ∈ pa450010wx, l ≠ 0 ∧ l.natAbs ≤ kS := by
  intro l hl
  simp only [pa450010wx, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> omega

theorem pa450010wv_wx (b : Bool) {kS : ℕ} (h2 : 2 ≤ kS) :
    pa450010wv b kS pa450010wx = pa450010x := by
  rw [pa450010wv_eq_wordP b kS _ (pa450010_wx_letters kS h2), pa450010x,
    wordP_congr h2 (fun l _ => rfl) (by decide +kernel : wordsLE 2 pa450010wx = true)]
  refine wordP_congr le_rfl (fun l hl => ?_) (by decide +kernel : wordsLE 2 pa450010wx = true)
  interval_cases l <;> rfl

theorem pa450010wv_wK (b : Bool) : ∀ j < 4, pa450010wv b 4 pa450010wK[j]! = pa450010gK b j := by
  intro j hj
  interval_cases j <;>
    simp [pa450010wv, pa450010wK, CFSG.Monster.B.Co2.toLetters,
      Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_nil]

theorem pa450010wv_wD (b : Bool) : ∀ j < 2, pa450010wv b 2 pa450010wD[j]! = pa450010gK b j := by
  intro j hj
  interval_cases j <;>
    simp [pa450010wv, pa450010wD, CFSG.Monster.B.Co2.toLetters,
      Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_nil]

theorem pa450010_clK (b : Bool) :
    closure ((fun j => pa450010wv b 4 pa450010wK[j]!) '' {j | j < pa450010wK.length}) =
      K28 b := by
  have h : (fun j => pa450010wv b 4 pa450010wK[j]!) '' {j | j < pa450010wK.length} =
      {pA, pB, pG b, pT} := by
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : j < 4 := hj
      rw [pa450010wv_wK b j hj']
      interval_cases j <;> simp [pa450010gK]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by decide, by rw [pa450010wv_wK b 0 (by norm_num)]; rfl⟩
      · exact ⟨1, by decide, by rw [pa450010wv_wK b 1 (by norm_num)]; rfl⟩
      · exact ⟨2, by decide, by rw [pa450010wv_wK b 2 (by norm_num)]; rfl⟩
      · exact ⟨3, by decide, by rw [pa450010wv_wK b 3 (by norm_num)]; rfl⟩
  rw [h]
  rfl

theorem pa450010_clD (b : Bool) :
    closure ((fun j => pa450010wv b 2 pa450010wD[j]!) '' {j | j < pa450010wD.length}) = D28 := by
  have h : (fun j => pa450010wv b 2 pa450010wD[j]!) '' {j | j < pa450010wD.length} =
      {pA, pB} := by
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : j < 2 := hj
      rw [pa450010wv_wD b j hj']
      interval_cases j <;> simp [pa450010gK]
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, by rw [pa450010wv_wD b 0 (by norm_num)]; rfl⟩
      · exact ⟨1, by decide, by rw [pa450010wv_wD b 1 (by norm_num)]; rfl⟩
  rw [h]
  rfl

theorem pa450010_prepSk (b : Bool) {kS : ℕ} (hkS : kS ≤ 4) :
    ∀ h < kS, PRep 28 5 (pa450010S b h) (pa450010gK b h) :=
  fun h hh => pa450010_prepS b h (by omega)

theorem pa450010_prepSIk (b : Bool) {kS : ℕ} (hkS : kS ≤ 4) :
    ∀ h < kS, PRep 28 5 (pa450010SI b h) (pa450010gK b h)⁻¹ :=
  fun h hh => pa450010_prepSI b h (by omega)

theorem pa450010_root {b : Bool} {kS : ℕ} (hkS : kS ≤ 4) {wd : List Int} {R : ℕ}
    (h : wordEqK 28 5 (mask 5) (pidn 28 5) (pa450010S b) (pa450010SI b) kS wd R = true) :
    PRep 28 5 R (pa450010wv b kS wd) := by
  unfold wordEqK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨-, hl, he⟩ := h
  rw [← Nat.eq_of_beq_eq_true he]
  exact (prep_wordK (by norm_num) (by norm_num) (pa450010_prepSk b hkS)
    (pa450010_prepSIk b hkS) _ hl).1

theorem pa450010_conj {b : Bool} {kS R N k cnt : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ}
    {ws : List (List Int)} {r : Perm (Fin 28)} (hkS : kS ≤ 4) (hr : PRep 28 5 R r)
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) R N k G GI cnt T PL kS (pa450010S b)
      (pa450010SI b) ws = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) true G GI k cnt T PL POS SRT SRI 0 N = true) :
    ∃ c : ℕ → Perm (Fin 28), (∀ i < cnt, PRep 28 5 (T i) (c i)) ∧
      (∀ a < cnt, ∀ a' < cnt, c a = c a' → a = a') ∧ cnt = N ∧
      ∀ y, (∃ h ∈ closure ((fun j => pa450010wv b kS ws[j]!) '' {j | j < ws.length}),
        h * r * h⁻¹ = y) ↔ ∃ i < cnt, c i = y := by
  obtain ⟨hh, hN, hk, hg, hgi⟩ := recHdK_gens (by norm_num) (by norm_num)
    (pa450010_prepSk b hkS) (pa450010_prepSIk b hkS) hd
  subst hk
  obtain ⟨c, hc, hinj, hcls⟩ := penumConj_class (by norm_num) (by norm_num) hg hgi hr hh
    (fun i hi => penumSlK_pt hsl (Nat.zero_le i) (by omega) hi)
  exact ⟨c, hc, hinj, hN, hcls⟩

theorem pa450010_left {b : Bool} {kS N k cnt : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ}
    {ws : List (List Int)} (hkS : kS ≤ 4)
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) N k G GI cnt T PL kS
      (pa450010S b) (pa450010SI b) ws = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 N = true) :
    ∃ x : ℕ → Perm (Fin 28), (∀ i < cnt, PRep 28 5 (T i) (x i)) ∧
      (∀ i < cnt, canonK 28 5 (mask 5) (28 * 5) (T i) = true) ∧ cnt = N ∧
      (∀ y, y ∈ closure ((fun j => pa450010wv b kS ws[j]!) '' {j | j < ws.length}) ↔
        ∃ i < cnt, x i = y) ∧
      Nat.card (closure ((fun j => pa450010wv b kS ws[j]!) '' {j | j < ws.length})) = cnt := by
  obtain ⟨hh, hN, hk, hg, -⟩ := recHdK_gens (by norm_num) (by norm_num)
    (pa450010_prepSk b hkS) (pa450010_prepSIk b hkS) hd
  subst hk
  have hp := fun i (hi : i < cnt) => penumSlK_pt hsl (Nat.zero_le i) (by omega) hi
  obtain ⟨x, hx, -, hmem, hcard⟩ := penumLeft_group (by norm_num) (by norm_num) hg hh hp
  exact ⟨x, hx, fun i hi => (penumPt_specH (hp i hi)).1, hN, hmem, hcard⟩

theorem pa450010_card_cent {H : Subgroup (Perm (Fin 28))} {r : Perm (Fin 28)} (hr : r ∈ H) :
    Nat.card (centralizer ({⟨r, hr⟩} : Set H)) =
      Nat.card ↥(H ⊓ centralizer ({r} : Set (Perm (Fin 28)))) :=
  Nat.card_congr
    { toFun := fun c => ⟨(c : H), (c : H).2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2))⟩
      invFun := fun c => ⟨⟨c, c.2.1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 c.2.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem pa450010_card_cent_conj {H : Subgroup (Perm (Fin 28))} {r g : Perm (Fin 28)} (hr : r ∈ H)
    (hg : g ∈ H) : Nat.card ↥(H ⊓ centralizer ({g * r * g⁻¹} : Set (Perm (Fin 28)))) =
      Nat.card ↥(H ⊓ centralizer ({r} : Set (Perm (Fin 28)))) := by
  have hc : g * r * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hr) (H.inv_mem hg)
  rw [← pa450010_card_cent hr, ← pa450010_card_cent hc]
  refine CFSG.KC.OrbGroup.card_centralizer_of_isConj (isConj_iff.2 ⟨⟨g, hg⟩⁻¹, ?_⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  group

theorem pa450010_size {H : Subgroup (Perm (Fin 28))} {r : Perm (Fin 28)} (hr : r ∈ H) {cnt : ℕ}
    {c : ℕ → Perm (Fin 28)} (hcls : ∀ y, (∃ h ∈ H, h * r * h⁻¹ = y) ↔ ∃ i < cnt, c i = y)
    (hinj : ∀ a < cnt, ∀ b < cnt, c a = c b → a = b) :
    cnt * Nat.card ↥(H ⊓ centralizer ({r} : Set (Perm (Fin 28)))) = Nat.card H := by
  rw [← pa450010_card_cent hr]
  exact card_centralizer_of_class hr hcls hinj

theorem pa450010_syl {H Y : Subgroup (Perm (Fin 28))} {k : ℕ} (hYH : Y ≤ H)
    (hY : Nat.card Y = 2 ^ k) (hk : ¬ 2 ^ (k + 1) ∣ Nat.card H) {c : Perm (Fin 28)} (hc : c ∈ H)
    (hc4 : c ^ 4 = 1) : ∃ g ∈ H, g * c * g⁻¹ ∈ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYc : Nat.card (Y.subgroupOf H) = 2 ^ k := by
    rw [← hY]
    exact Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv
  have h4 : (⟨c, hc⟩ : H) ^ 4 = 1 := Subtype.ext (by simpa using hc4)
  have hdvd : orderOf (⟨c, hc⟩ : H) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  obtain ⟨g, hg⟩ := CFSG.KS.SylowCount.conj_into_of_card (Y.subgroupOf H) hYc hk he
  rw [mem_subgroupOf] at hg
  exact ⟨g, g.2, by simpa using hg⟩

theorem pa450010_pidn_shr : pidn 28 5 >>> (28 * 5) = 0 := by decide +kernel

theorem pa450010_coverK_of {b : Bool} {k cnt : ℕ}
    {G GI T PL POS SRT SRI : ℕ → ℕ} {ws : List (List Int)}
    {L : List (ℕ × (ℕ → ℕ) × (ℕ → ℕ))}
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 256 k G GI cnt T PL 4
      (pa450010S b) (pa450010SI b) ws = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 256 = true)
    (hcov : sqCoverK 28 5 (mask 5) (pidn 28 5) (pa450010S b 3) T L cnt = true)
    (hL : ∀ r ∈ L, ∃ i < 6, ∀ q < r.1, ∀ s, PRep 28 5 (r.2.1 q) s →
      ∃ h ∈ K28 b, h * pa450010rep b i * h⁻¹ = s)
    {c : Perm (Fin 28)} (hc : c ∈ K28 b) (hsq : c * c = 1 ∨ c * c = pT) (h1 : c ≠ 1)
    (ht : c ≠ pT) : ∃ i < 6, ∃ h ∈ K28 b, h * pa450010rep b i * h⁻¹ = c := by
  obtain ⟨x, hx, hcan, hN, hmem, hcard⟩ := pa450010_left (by norm_num) hd hsl
  have hYK : closure ((fun j => pa450010wv b 4 ws[j]!) '' {j | j < ws.length}) ≤ K28 b := by
    rw [closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact pa450010wv_mem b 4 _
  have hTT : pT * pT = 1 := pT_mul_self
  have hc4 : c ^ 4 = 1 := by
    have e : c ^ 4 = (c * c) * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rcases hsq with hs | hs <;> rw [e, hs]
    · exact one_mul 1
    · exact hTT
  obtain ⟨g, hg, hz⟩ := pa450010_syl (k := 8) hYK (by rw [hcard, hN]; norm_num)
    (by rw [card_K28]; norm_num) hc hc4
  obtain ⟨i, hi, hxi⟩ := (hmem _).1 hz
  have hTi : PRep 28 5 (T i) (g * c * g⁻¹) := hxi ▸ hx i hi
  have hgt : g * pT * g⁻¹ = pT := by
    rw [pT_commute_of_mem_K28 b g hg]
    group
  have hzz : (g * c * g⁻¹) * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
  have hshr : T i >>> (28 * 5) = 0 := (PF.canon_facts (hcan i hi)).2.2.1
  have hpc := prep_pcomp (by norm_num) hTi hTi
  have hpshr := PF.pcomp_shr (n := 28) (w := 5) (T i) (T i) (by norm_num) (by norm_num)
  have hS3 : PRep 28 5 (pa450010S b 3) pT := pa450010_prepS b 3 (by norm_num)
  have hS3shr : pa450010S b 3 >>> (28 * 5) = 0 :=
    (permOK_facts (allN_iff.1 (pa450010_perm b) 3 (by norm_num))).1
  have hid : PRep 28 5 (pidn 28 5) 1 := prep_pidn (by norm_num) (by norm_num)
  have hsqK : pcomp 28 5 (mask 5) (T i) (T i) = pidn 28 5 ∨
      pcomp 28 5 (mask 5) (T i) (T i) = pa450010S b 3 := by
    rw [hzz] at hpc
    rcases hsq with hs | hs <;> rw [hs] at hpc
    · left
      rw [mul_one, mul_inv_cancel] at hpc
      exact CFSG.KC.OrbRow.eq_of_prep (by norm_num) hpc hid hpshr pa450010_pidn_shr
    · right
      rw [hgt] at hpc
      exact CFSG.KC.OrbRow.eq_of_prep (by norm_num) hpc hS3 hpshr hS3shr
  have hne1 : T i ≠ pidn 28 5 := by
    intro e
    rw [e] at hTi
    apply h1
    have e2 := CFSG.KC.OrbGroup.prep_eq hTi hid
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [e2]; group
  have hnet : T i ≠ pa450010S b 3 := by
    intro e
    rw [e] at hTi
    apply ht
    have e2 := CFSG.KC.OrbGroup.prep_eq hTi hS3
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = g⁻¹ * pT * g := by rw [e2]
      _ = pT := by rw [pT_commute_of_mem_K28 b _ ((K28 b).inv_mem hg)]; group
  obtain ⟨r, hr, hq, hrT⟩ := sqCoverK_spec hcov i hi hsqK hne1 hnet
  obtain ⟨j, hj, hcl⟩ := hL r hr
  obtain ⟨h, hh, e⟩ := hcl _ hq _ (by rw [hrT]; exact hTi)
  refine ⟨j, hj, g⁻¹ * h, (K28 b).mul_mem ((K28 b).inv_mem hg) hh, ?_⟩
  calc g⁻¹ * h * pa450010rep b j * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * pa450010rep b j * h⁻¹) * g := by
        group
    _ = c := by rw [e]; group

theorem pa450010_clsK {b : Bool} {i R N k cnt : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ}
    (hR : wordEqK 28 5 (mask 5) (pidn 28 5) (pa450010S b) (pa450010SI b) 4
      (pa450010wReps.getD i []) R = true)
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) R N k G GI cnt T PL 4 (pa450010S b)
      (pa450010SI b) pa450010wK = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) true G GI k cnt T PL POS SRT SRI 0 N = true) :
    (∀ q < cnt, ∀ s, PRep 28 5 (T q) s → ∃ h ∈ K28 b, h * pa450010rep b i * h⁻¹ = s) ∧
      N * Nat.card ↥(K28 b ⊓ centralizer ({pa450010rep b i} : Set (Perm (Fin 28)))) =
        Nat.card (K28 b) := by
  obtain ⟨c, hc, hinj, hN, hcls⟩ := pa450010_conj le_rfl (pa450010_root le_rfl hR) hd hsl
  rw [pa450010_clK] at hcls
  refine ⟨fun q hq s hs => ?_, ?_⟩
  · rw [CFSG.KC.OrbGroup.prep_eq hs (hc q hq)]
    exact (hcls _).2 ⟨q, hq, rfl⟩
  · rw [← hN]
    exact pa450010_size (pa450010wv_mem b 4 _) hcls hinj

theorem pa450010_L1_ok : ∀ r ∈ pa450010L1, ∃ i < 6, ∀ q < r.1, ∀ s, PRep 28 5 (r.2.1 q) s →
    ∃ h ∈ K28 false, h * pa450010rep false i * h⁻¹ = s := by
  intro r hr
  simp only [pa450010L1, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num,
      (pa450010_clsK (b := false) pa450010_C10_root pa450010_C10_hd pa450010_C10_sl).1⟩
  · exact ⟨1, by norm_num,
      (pa450010_clsK (b := false) pa450010_C11_root pa450010_C11_hd pa450010_C11_sl).1⟩
  · exact ⟨2, by norm_num,
      (pa450010_clsK (b := false) pa450010_C12_root pa450010_C12_hd pa450010_C12_sl).1⟩
  · exact ⟨3, by norm_num,
      (pa450010_clsK (b := false) pa450010_C13_root pa450010_C13_hd pa450010_C13_sl).1⟩
  · exact ⟨4, by norm_num,
      (pa450010_clsK (b := false) pa450010_C14_root pa450010_C14_hd pa450010_C14_sl).1⟩
  · exact ⟨5, by norm_num,
      (pa450010_clsK (b := false) pa450010_C15_root pa450010_C15_hd pa450010_C15_sl).1⟩

theorem pa450010_L2_ok : ∀ r ∈ pa450010L2, ∃ i < 6, ∀ q < r.1, ∀ s, PRep 28 5 (r.2.1 q) s →
    ∃ h ∈ K28 true, h * pa450010rep true i * h⁻¹ = s := by
  intro r hr
  simp only [pa450010L2, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num,
      (pa450010_clsK (b := true) pa450010_C20_root pa450010_C20_hd pa450010_C20_sl).1⟩
  · exact ⟨1, by norm_num,
      (pa450010_clsK (b := true) pa450010_C21_root pa450010_C21_hd pa450010_C21_sl).1⟩
  · exact ⟨2, by norm_num,
      (pa450010_clsK (b := true) pa450010_C22_root pa450010_C22_hd pa450010_C22_sl).1⟩
  · exact ⟨3, by norm_num,
      (pa450010_clsK (b := true) pa450010_C23_root pa450010_C23_hd pa450010_C23_sl).1⟩
  · exact ⟨4, by norm_num,
      (pa450010_clsK (b := true) pa450010_C24_root pa450010_C24_hd pa450010_C24_sl).1⟩
  · exact ⟨5, by norm_num,
      (pa450010_clsK (b := true) pa450010_C25_root pa450010_C25_hd pa450010_C25_sl).1⟩

theorem pa450010_sizeK (b : Bool) : ∀ i < 6,
    pa450010sz.getD i 0 *
      Nat.card ↥(K28 b ⊓ centralizer ({pa450010rep b i} : Set (Perm (Fin 28)))) = 380160 := by
  intro i hi
  rw [← card_K28 b]
  cases b <;> interval_cases i
  · exact (pa450010_clsK (b := false) pa450010_C10_root pa450010_C10_hd pa450010_C10_sl).2
  · exact (pa450010_clsK (b := false) pa450010_C11_root pa450010_C11_hd pa450010_C11_sl).2
  · exact (pa450010_clsK (b := false) pa450010_C12_root pa450010_C12_hd pa450010_C12_sl).2
  · exact (pa450010_clsK (b := false) pa450010_C13_root pa450010_C13_hd pa450010_C13_sl).2
  · exact (pa450010_clsK (b := false) pa450010_C14_root pa450010_C14_hd pa450010_C14_sl).2
  · exact (pa450010_clsK (b := false) pa450010_C15_root pa450010_C15_hd pa450010_C15_sl).2
  · exact (pa450010_clsK (b := true) pa450010_C20_root pa450010_C20_hd pa450010_C20_sl).2
  · exact (pa450010_clsK (b := true) pa450010_C21_root pa450010_C21_hd pa450010_C21_sl).2
  · exact (pa450010_clsK (b := true) pa450010_C22_root pa450010_C22_hd pa450010_C22_sl).2
  · exact (pa450010_clsK (b := true) pa450010_C23_root pa450010_C23_hd pa450010_C23_sl).2
  · exact (pa450010_clsK (b := true) pa450010_C24_root pa450010_C24_hd pa450010_C24_sl).2
  · exact (pa450010_clsK (b := true) pa450010_C25_root pa450010_C25_hd pa450010_C25_sl).2

theorem pa450010_cover (b : Bool) {c : Perm (Fin 28)}
    (hc : c ∈ K28 b) (hsq : c * c = 1 ∨ c * c = pT) (h1 : c ≠ 1) (ht : c ≠ pT) :
    ∃ i < 6, (∃ h ∈ K28 b, h * pa450010rep b i * h⁻¹ = c) ∧
      pa450010sz.getD i 0 * Nat.card ↥(K28 b ⊓ centralizer ({c} : Set (Perm (Fin 28)))) =
        380160 := by
  have hex : ∃ i < 6, ∃ h ∈ K28 b, h * pa450010rep b i * h⁻¹ = c := by
    cases b
    · exact pa450010_coverK_of (b := false) pa450010_SY1_hd pa450010_SY1_sl pa450010_cover1
        pa450010_L1_ok hc hsq h1 ht
    · exact pa450010_coverK_of (b := true) pa450010_SY2_hd pa450010_SY2_sl pa450010_cover2
        pa450010_L2_ok hc hsq h1 ht
  obtain ⟨i, hi, h, hh, rfl⟩ := hex
  refine ⟨i, hi, ⟨h, hh, rfl⟩, ?_⟩
  rw [pa450010_card_cent_conj (r := pa450010rep b i) (pa450010wv_mem b 4 _) hh]
  exact pa450010_sizeK b i hi

theorem pa450010_card_Kx (b : Bool) :
    Nat.card ↥(K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) = 960 := by
  have h := pa450010_sizeK b 2 (by norm_num)
  have e : pa450010rep b 2 = pa450010x := pa450010wv_wx b (by norm_num)
  rw [e] at h
  change 396 * _ = 380160 at h
  omega

theorem pa450010_I3 : ∀ y ∈ D28, orderOf y = 2 →
    Nat.card ↥(D28 ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 240 →
      ∃ a ∈ D28, a * y * a⁻¹ = pa450010x := by
  intro y hy hy2 hcy
  obtain ⟨xs, hx, hcan, hN, hmem, hcard⟩ :=
    pa450010_left (b := false) (by norm_num) pa450010_SD_hd pa450010_SD_sl
  have hYD : closure ((fun j => pa450010wv false 2 pa450010wSD[j]!) '' {j | j < pa450010wSD.length})
      ≤ D28 := by
    rw [closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact pa450010wv_memD false _
  have hyy : y * y = 1 := by
    rw [← pow_two, ← hy2]
    exact pow_orderOf_eq_one y
  have hy4 : y ^ 4 = 1 := by
    have e : y ^ 4 = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, hyy, one_mul]
  obtain ⟨g, hg, hz⟩ := pa450010_syl (k := 6) hYD (by rw [hcard, hN]; norm_num)
    (by rw [card_D28]; norm_num) hy hy4
  obtain ⟨i, hi, hxi⟩ := (hmem _).1 hz
  have hTi : PRep 28 5 (pa450010SD.T i) (g * y * g⁻¹) := hxi ▸ hx i hi
  have hid : PRep 28 5 (pidn 28 5) 1 := prep_pidn (by norm_num) (by norm_num)
  have hpc := prep_pcomp (by norm_num) hTi hTi
  have hzz : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
    have e : (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    rw [e, hyy]
    group
  rw [hzz] at hpc
  have hsq : pcomp 28 5 (mask 5) (pa450010SD.T i) (pa450010SD.T i) = pidn 28 5 :=
    CFSG.KC.OrbRow.eq_of_prep (by norm_num) hpc hid
      (PF.pcomp_shr (n := 28) (w := 5) _ _ (by norm_num) (by norm_num)) pa450010_pidn_shr
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hne1 : pa450010SD.T i ≠ pidn 28 5 := by
    intro e
    rw [e] at hTi
    apply hy1
    have e2 := CFSG.KC.OrbGroup.prep_eq hTi hid
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [e2]; group
  obtain ⟨r, hr, hq, hrT⟩ := sqCoverK_spec pa450010_coverD i hi (Or.inl hsq) hne1 hne1
  have hzD : g * y * g⁻¹ ∈ D28 := D28.mul_mem (D28.mul_mem hg hy) (D28.inv_mem hg)
  have hcz : Nat.card ↥(D28 ⊓ centralizer ({g * y * g⁻¹} : Set (Perm (Fin 28)))) = 240 := by
    rw [pa450010_card_cent_conj hy hg, hcy]
  simp only [pa450010LD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only at hq hrT
  · obtain ⟨c, hc, -, -, hcls⟩ := pa450010_conj (b := false) (by norm_num)
      (pa450010_root (b := false) (by norm_num) pa450010_XD_root) pa450010_XD_hd pa450010_XD_sl
    rw [pa450010_clD] at hcls
    have hzc : c (r32 pa450010FD0 i) = g * y * g⁻¹ :=
      CFSG.KC.OrbGroup.prep_eq (hc _ hq) (by rw [hrT]; exact hTi)
    obtain ⟨h, hh, e⟩ := (hcls _).2 ⟨_, hq, hzc⟩
    rw [pa450010wv_wx false le_rfl] at e
    refine ⟨h⁻¹ * g, D28.mul_mem (D28.inv_mem hh) hg, ?_⟩
    calc h⁻¹ * g * y * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * y * g⁻¹) * h := by group
      _ = pa450010x := by rw [← e]; group
  · obtain ⟨c, hc, hinj, hN', hcls⟩ := pa450010_conj (b := false) (by norm_num)
      (pa450010_root (b := false) (by norm_num) pa450010_AD_root) pa450010_AD_hd pa450010_AD_sl
    rw [pa450010_clD] at hcls
    have hzc : c (r32 pa450010FD1 i) = g * y * g⁻¹ :=
      CFSG.KC.OrbGroup.prep_eq (hc _ hq) (by rw [hrT]; exact hTi)
    obtain ⟨h, hh, e⟩ := (hcls _).2 ⟨_, hq, hzc⟩
    have hs := pa450010_size (pa450010wv_memD false _) hcls hinj
    rw [← e, pa450010_card_cent_conj (pa450010wv_memD false _) hh] at hcz
    rw [hcz, hN', card_D28] at hs
    omega

end CertificateChecks.KernelPropA

end
