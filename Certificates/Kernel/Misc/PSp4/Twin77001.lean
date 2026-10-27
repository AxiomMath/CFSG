module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSp4Inputs
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.Fischer.Classification.PartIII.Beta.Data
public import Certificates.Kernel.Misc.PSp4.Twin77001K
public import CFSG.Certificates.Kernel.BfsPinAlg
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Twin77001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups.NativeChecks
  CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin CFSG.CGT.PushingUpLit.SolKNA CFSG.KGroups.Native

abbrev Q (p : Nat) : Prop := PP 45 6 p

theorem pe_Q : Q pe := PP.id kSz

theorem pc_Q {p q : Nat} (hp : Q p) (hq : Q q) : Q (pc p q) := PP.mul hp hq

theorem cmp' {p q : Nat} (hp : Q p) (hq : Q q) :
    compA 45 (unpack 45 6 p) (unpack 45 6 q) = unpack 45 6 (pc p q) := compA_PP hp hq

theorem eq' {p q : Nat} (hp : Q p) (hq : Q q) :
    eqA 45 (unpack 45 6 p) (unpack 45 6 q) = Nat.beq p q := eqA_PP hp hq

theorem id' : idA 45 = unpack 45 6 pe := idA_eq kSz

theorem prods_spec : ∀ Ts : List (List Nat), (∀ T ∈ Ts, ∀ t ∈ T, Q t) →
    productsA 45 (Ts.map (List.map (unpack 45 6))) = (prodsP Ts).map (unpack 45 6) ∧
      ∀ p ∈ prodsP Ts, Q p
  | [], _ => ⟨by simp [productsA, prodsP, id'], fun p hp => by
      simp only [prodsP, List.mem_singleton] at hp
      rw [hp]
      exact pe_Q⟩
  | T :: Ts, h => by
    obtain ⟨ih1, ih2⟩ := prods_spec Ts (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
    have hT : ∀ t ∈ T, Q t := h T List.mem_cons_self
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, productsA, prodsP, ih1, List.flatMap_map, List.map_flatMap,
        List.map_map]
      refine List.flatMap_congr fun t ht => List.map_congr_left fun p hp => ?_
      simp only [Function.comp_apply]
      exact cmp' (hT t ht) (ih2 p hp)
    · intro p hp
      simp only [prodsP] at hp
      obtain ⟨t, ht, hp⟩ := List.mem_flatMap.1 hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact pc_Q (hT t ht) (ih2 q hq)

theorem all_congr' {L : List Nat} {f g : Nat → Bool} (h : ∀ p ∈ L, f p = g p) :
    L.all f = L.all g := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem any_congr' {L : List Nat} {f g : Nat → Bool} (h : ∀ p ∈ L, f p = g p) :
    L.any f = L.any g := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem filter_unpack {L : List Nat} {f : Array Nat → Bool} {g : Nat → Bool}
    (h : ∀ p ∈ L, f (unpack 45 6 p) = g p) :
    (L.map (unpack 45 6)).filter f = (L.filter g).map (unpack 45 6) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun p hp => by simpa using h p hp

theorem twin_eq {L : List Nat} (hL : ∀ p ∈ L, Q p) {t : Nat} (ht : Q t) :
    twinCheckA 45 (L.map (unpack 45 6)) (unpack 45 6 t) = twinK L t := by
  unfold twinCheckA twinK
  dsimp only
  rw [filter_unpack (g := fun g => Nat.beq (pc g t) (pc t g)) (fun p hp => by
    rw [cmp' (hL p hp) ht, cmp' ht (hL p hp), eq' (pc_Q (hL p hp) ht) (pc_Q ht (hL p hp))])]
  have hCm : ∀ p ∈ L.filter (fun g => Nat.beq (pc g t) (pc t g)), Q p :=
    fun p hp => hL p (List.mem_filter.1 hp).1
  generalize L.filter (fun g => Nat.beq (pc g t) (pc t g)) = C at hCm ⊢
  rw [List.all_map]
  apply all_congr'
  intro a ha
  have qa := hCm a ha
  simp only [Function.comp_apply]
  rw [cmp' qa qa, eq' (pc_Q qa qa) ht]
  rw [filter_unpack (g := fun b => (Nat.beq (pc (pc a b) (pc a b)) pe && !(Nat.beq (pc a b) pe)) &&
      !(Nat.beq (pc a b) t)) (fun b hb => by
    have qb := hCm b hb
    have qab := pc_Q qa qb
    rw [cmp' qa qb]
    unfold isInvolA
    rw [cmp' qab qab, id', eq' (pc_Q qab qab) pe_Q, eq' qab pe_Q, eq' qab ht])]
  rw [List.any_map]
  congr 1
  apply any_congr'
  intro b hb
  have qb := hCm b (List.mem_filter.1 hb).1
  simp only [Function.comp_apply]
  rw [List.any_map]
  apply any_congr'
  intro g hg
  have qg := hCm g hg
  simp only [Function.comp_apply]
  rw [cmp' qb qg, cmp' qg qa, eq' (pc_Q qb qg) (pc_Q qg qa)]

theorem cover_eq {L ts : List Nat} (hL : ∀ p ∈ L, Q p) (hts : ∀ p ∈ ts, Q p) :
    invCoverCheckA 45 (L.map (unpack 45 6)) (ts.map (unpack 45 6)) = coverK L ts := by
  unfold invCoverCheckA coverK covF
  rw [List.all_map]
  apply all_congr'
  intro u hu
  have qu := hL u hu
  simp only [Function.comp_apply]
  unfold isInvolA
  rw [cmp' qu qu, id', eq' (pc_Q qu qu) pe_Q, eq' qu pe_Q, List.any_map]
  congr 1
  apply any_congr'
  intro t ht
  have qt := hts t ht
  simp only [Function.comp_apply]
  rw [List.any_map]
  apply any_congr'
  intro g hg
  have qg := hL g hg
  simp only [Function.comp_apply]
  rw [cmp' qg qt, cmp' qu qg, eq' (pc_Q qg qt) (pc_Q qu qg)]

theorem lt_of_blt' {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem prods_mem {x : Nat} (hx : x ∈ prodsP lvls) :
    ∃ a < 45, ∃ b < 32, ∃ c < 9, ∃ d < 2, x = el a b c d := by
  simp only [prodsP, lvls] at hx
  obtain ⟨t0, ht0, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht0
  obtain ⟨t1, ht1, hp0⟩ := List.mem_flatMap.1 hp0
  obtain ⟨p1, hp1, rfl⟩ := List.mem_map.1 hp0
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ht1
  obtain ⟨t2, ht2, hp1⟩ := List.mem_flatMap.1 hp1
  obtain ⟨p2, hp2, rfl⟩ := List.mem_map.1 hp1
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ht2
  obtain ⟨t3, ht3, hp2⟩ := List.mem_flatMap.1 hp2
  obtain ⟨p3, hp3, rfl⟩ := List.mem_map.1 hp2
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ht3
  rw [List.mem_singleton] at hp3
  subst hp3
  rw [List.mem_range] at ha hb hc hd
  exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩

theorem el_mem {a b c d : Nat} (ha : a < 45) (hb : b < 32) (hc : c < 9) (hd : d < 2) :
    el a b c d ∈ prodsP lvls := by
  simp only [prodsP, lvls]
  refine List.mem_flatMap.2 ⟨LV a, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩, List.mem_map.2 ⟨_,
    List.mem_flatMap.2 ⟨LV (45 + b), List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩, List.mem_map.2 ⟨_,
    List.mem_flatMap.2 ⟨LV (77 + c), List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩, List.mem_map.2 ⟨_,
    List.mem_flatMap.2 ⟨LV (86 + d), List.mem_map.2 ⟨d, List.mem_range.2 hd, rfl⟩,
      List.mem_map.2 ⟨pe, List.mem_singleton.2 rfl, rfl⟩⟩, rfl⟩⟩, rfl⟩⟩, rfl⟩⟩

theorem coverA_all {a : Nat} (ha : a < 45) : coverA a = true := by
  interval_cases a
  exacts [coverA0, coverA1, coverA2, coverA3, coverA4, coverA5, coverA6, coverA7, coverA8, coverA9,
    coverA10, coverA11, coverA12, coverA13, coverA14, coverA15, coverA16, coverA17, coverA18,
    coverA19, coverA20, coverA21, coverA22, coverA23, coverA24, coverA25, coverA26, coverA27,
    coverA28, coverA29, coverA30, coverA31, coverA32, coverA33, coverA34, coverA35, coverA36,
    coverA37, coverA38, coverA39, coverA40, coverA41, coverA42, coverA43, coverA44]

theorem cover_ok : coverK (prodsP lvls) [TW 1, TW 0] = true := by
  unfold coverK
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := prods_mem hx
  have hA : allN 32 (fun b => allN 9 (fun c => allN 2 (fun d => cv a b c d))) = true := coverA_all ha
  have hcv := allN_spec (allN_spec (allN_spec hA b hb) c hc) d hd
  unfold cv at hcv
  unfold covF
  have e : (Nat.beq (pc (el a b c d) (el a b c d)) pe && !(Nat.beq (el a b c d) pe)) =
    invB (el a b c d) := rfl
  rw [e]
  cases hi : invB (el a b c d)
  · rfl
  · rw [hi] at hcv
    simp only [Bool.not_true, Bool.false_or] at hcv ⊢
    unfold witOK at hcv
    rw [Bool.and_eq_true] at hcv
    obtain ⟨hj, heq⟩ := hcv
    have hj' := lt_of_blt' hj
    generalize WC (((a * 32 + b) * 9 + c) * 2 + d) = w at hj' heq
    rw [List.any_eq_true]
    refine ⟨tOf (w % 2), ?_, ?_⟩
    · unfold tOf
      cases Nat.beq (w % 2) 0 <;> simp
    · rw [List.any_eq_true]
      refine ⟨elIdx (w / 2), ?_, heq⟩
      unfold elIdx
      exact el_mem (by omega) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
        (Nat.mod_lt _ (by norm_num))

open CFSG.CGT.PushingUpLit.SolKNA CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin
  CFSG.GH74.KGroups.NativeChecks CFSG.ComponentClassification.CatFactsSmall.PSp43 in
open Certificates in
theorem c77001 : (twinCheckA 45 (enumA QP45) (toA tw1) = true)
    ∧ (twinCheckA 45 (enumA QP45) (toA tw2) = true)
    ∧ (invCoverCheckA 45 (enumA QP45) (tws.map toA) = true) := by
  have hLV : ∀ k < 88, Q (LV k) := fun k hk => PP_of_permOK kSz (allN_spec kPerm k hk)
  have hTW : ∀ k < 2, Q (TW k) := fun k hk => PP_of_permOK kSz (allN_spec kPermT k hk)
  have hlv : ∀ T ∈ lvls, ∀ t ∈ T, Q t := by
    intro T hT t ht
    simp only [lvls, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl <;>
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht <;> rw [List.mem_range] at hk <;> exact hLV _ (by omega)
  obtain ⟨hP, hPm⟩ := prods_spec lvls hlv
  have hE : enumA QP45 = (prodsP lvls).map (unpack 45 6) := by
    unfold enumA
    rw [kBind, hP]
  obtain ⟨t1, t2⟩ := kTw
  refine ⟨?_, ?_, ?_⟩
  · rw [hE, t1, twin_eq hPm (hTW 0 (by omega))]
    exact kT1
  · rw [hE, t2, twin_eq hPm (hTW 1 (by omega))]
    exact kT2
  · have hts : tws.map toA = [TW 1, TW 0].map (unpack 45 6) := by
      simp [tws, t1, t2]
    have hq : ∀ p ∈ [TW 1, TW 0], Q p := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [hTW 1 (by omega), hTW 0 (by omega)]
    rw [hE, hts, cover_eq hPm hq]
    exact cover_ok

end CertificateChecks.KernelMisc.Twin77001

end
