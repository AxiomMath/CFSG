module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoAll
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R13695pc
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R13695aut
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R13695rat
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R136300
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R136301
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBData
public import CFSG.YGroups.Y443.Native.Words
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.LookChk
public import CFSG.Certificates.Kernel.KDenseP.LookSound
public import CFSG.Certificates.Kernel.KDenseP.ReplaySound
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoEChk1
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoEChk2
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoEChk3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.MonSeven

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonSeven
  CFSG.KC.KDenseP.TwoPoint CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CertificateChecks.KernelKDenseP CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks _root_.Timmesfeld.Mon7

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.M7M.MT = true := by
  kd_monoTabL CFSG.KD.M7ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.M7M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem look_eq : CFSG.KD.M7L.look = fun k => findIdx k CFSG.KD.M7M.MT.keys :=
  funext fun l => lookT_eq CFSG.KD.M7L.tab_ok CFSG.KD.M7L.len_ok l

theorem m7_loc (P : Prs) :
    ∀ (S S' : ℕ → St) (c : ℕ), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) →
      CFSG.KD.M7L.chkPL P S c = CFSG.KD.M7L.chkPL P S' c := by
  intro S S' c h3 h4
  unfold CFSG.KD.M7L.chkPL chunkOKNL
  rw [h3, h4]

theorem m7_prod (P : Prs) :
    ∀ (S : ℕ → St) (c : ℕ), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      CFSG.KD.M7L.chkPL P S c =
        stEqN 4 (CFSG.KD.M7L.runCP P c (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold CFSG.KD.M7L.chkPL chunkOKNL
  rw [h] <;> rfl

theorem chunks_ix {P : ℕ → Prop} {CH IXf : ℕ → ℕ} {nu nr : ℕ} (hu : ∀ k < nu, P (CH k))
    (h : ((List.range nr).all fun k => Nat.blt (IXf k) nu) = true) : ∀ k < nr, P (CH (IXf k)) :=
  fun k hk => by
    have e := List.all_eq_true.1 h k (List.mem_range.2 hk)
    rw [Nat.blt_eq] at e
    exact hu _ e

theorem tp3E_sound
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen)) (hL : pairsLetterOK (tp3 eqs nes) = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words (tp3 eqs nes)) S (CH k) = true)
    (hplan : planOKP (Y443.words (tp3 eqs nes)) CH nch IT = true)
    (hwk : wkOK IT (tpWK eqs.length nes.length) = true) :
    ∀ e ∈ eqs, (∀ g ∈ e.1, g.validB = true) ∧ (∀ g ∈ e.2, g.validB = true) ∧
      wordLin e.1 = wordLin e.2 := by
  have h1 := (tp3B_sound hd eqs nes hL hS hc hplan hwk).1
  have h2 := (tp3L_sound hd eqs nes hL hS hc hplan hwk).1
  intro e he
  have h := List.all_eq_true.1 h1 e he
  simp only [agree, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h2 e he⟩

open Lean in
macro "kd_m7% " pre:ident w?:(num)? eqs:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  let (s0, w, lt) ← match w? with
    | some w => pure ((n "S0" : Term), w, ← `(fun x hx =>
        (CFSG.KC.KDenseP.rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans
          (by interval_cases x <;> rfl)))
    | none => pure (← `(CFSG.KD.KDF.I), Syntax.mkNumLit "3",
        ← `(fun x hx => CFSG.KC.KDenseP.rlS_lt hx))
  `(tp3E_sound CertificateChecks.KernelKDenseP.MonSeven.data_ok $eqs [] (by quickRfl)
      (S := CFSG.KC.KDenseP.rlS (CFSG.KD.M7L.runCP $(n "P")) $(n "CH") $(n "PRf") $s0 $w)
      $lt (CH := $(n "CHI"))
      (nch := kd_count% $pre $(mkIdent `IX)) (IT := $(n "IT"))
      (chunks_ix (CH := $(n "CH")) (IXf := $(n "IXf"))
        (P := fun c => CFSG.KC.KDenseP.chunkOKN 4 2 5 CFSG.KD.KDF.F CFSG.KD.M7M.MT
          (Y443.words (tp3 $eqs []))
          (CFSG.KC.KDenseP.rlS (CFSG.KD.M7L.runCP $(n "P")) $(n "CH") $(n "PRf") $s0 $w)
          c = true)
        (nu := kd_count% $pre $(mkIdent `CH))
        (fun k hk => CFSG.KC.KDenseP.chunkOKN_of_look
          CertificateChecks.KernelKDenseP.MonSeven.look_eq
          (CFSG.KC.KDenseP.replay_sound (m7_loc $(n "P")) (m7_prod $(n "P")) (CH := $(n "CH"))
            (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf")) (S0 := $s0) (w := $w)
            (ng := kd_count% $pre $(mkIdent `u)) (by kd_allE $pre $(mkIdent `u)) (by quickRfl)
            k hk))
        (by quickRfl))
      (by quickRfl) (by quickRfl))

theorem wordLin_powL (k : ℕ) (w : List Native.Gen) : wordLin (powL k w) = wordLin w ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [powL, List.replicate_succ', List.flatten_append, wordLin_append, ← powL, ih]
    simp [pow_succ']

theorem Wrho_append (a b : List ℕ) : Wrho (a ++ b) = Wrho b ++ Wrho a := by
  simp only [Wrho, List.map_append, List.reverse_append, List.flatten_append]

theorem Wrho_replicate (m k : ℕ) : Wrho (List.replicate m k) = powL m wq[k]! := by
  simp only [Wrho, List.map_replicate, List.reverse_replicate, powL]

theorem Wrho_flatMap (v : Array ℕ) (l : List ℕ) :
    Wrho (l.flatMap fun k => List.replicate v[k]! k) =
      l.reverse.flatMap fun k => powL v[k]! wq[k]! := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, Wrho_append, ih, Wrho_replicate, List.reverse_cons, List.flatMap_append]
    simp

theorem lt_of_mem_wordOfVec {n : ℕ} {v : Array ℕ} {k : ℕ} (h : k ∈ wordOfVec n v) : k < n := by
  simp only [wordOfVec, List.mem_flatMap, List.mem_range, List.mem_replicate] at h
  obtain ⟨i, hi, -, rfl⟩ := h
  exact hi

theorem Wrho_valid {wo : List ℕ} (hwq : ∀ k < 6, ∀ g ∈ wq[k]!, g.validB = true)
    (hwo : ∀ k ∈ wo, k < 6) : ∀ g ∈ Wrho wo, g.validB = true := by
  intro g hg
  simp only [Wrho, List.mem_flatten, List.mem_reverse, List.mem_map] at hg
  obtain ⟨l, ⟨k, hk, rfl⟩, hg⟩ := hg
  exact hwq k (hwo k hk) g hg

theorem wordLin_flatMap_congr {f g : ℕ → List Native.Gen} :
    ∀ l : List ℕ, (∀ k ∈ l, wordLin (f k) = wordLin (g k)) →
      wordLin (l.flatMap f) = wordLin (l.flatMap g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, wordLin_append, wordLin_append, h a List.mem_cons_self,
      wordLin_flatMap_congr l fun k hk => h k (List.mem_cons_of_mem a hk)]

theorem wordLin_bal {w w' : List Native.Gen} (h7 : wordLin w ^ 7 = 1) (hi : wordLin (w ++ w') = 1)
    {e : ℕ} (he : e ≤ 7) :
    wordLin (if e ≤ 3 then powL e w else powL (7 - e) w') = wordLin (powL e w) := by
  split
  · rfl
  · rw [wordLin_powL, wordLin_powL]
    rw [wordLin_append] at hi
    rw [eq_inv_of_mul_eq_one_left hi, inv_pow]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, Nat.add_sub_cancel' he, h7]

theorem wordLin_WrhoBOf {iw : ℕ → List Native.Gen} (h7 : ∀ k < 6, wordLin wq[k]! ^ 7 = 1)
    (hi : ∀ k < 6, wordLin (wq[k]! ++ iw k) = 1) {v : Array ℕ} (hv : ∀ k < 6, v[k]! ≤ 7) :
    wordLin (WrhoBOf iw v) = wordLin (Wrho (wordOfVec 6 v)) := by
  rw [wordOfVec, Wrho_flatMap]
  unfold WrhoBOf
  exact wordLin_flatMap_congr _ fun k hk => by
    have hk' : k < 6 := List.mem_range.1 (List.mem_reverse.1 hk)
    exact wordLin_bal (h7 k hk') (hi k hk') (hv k hk')

theorem cw7_le : ∀ x < 36, ∀ k < 6, (cw7[x]!)[k]! ≤ 7 := by decide +kernel

theorem alphaVecs_le : ∀ a < 2, ∀ i < 6, ∀ k < 6, ((alphaVecs[a]!)[i]!)[k]! ≤ 7 := by
  decide +kernel

theorem orbVec_le : ∀ x < 22, ∀ k < 6, (orbVec[x]!)[k]! ≤ 7 := by decide +kernel

theorem orbWord_eq : ∀ x < 22, orbWord[x]! = wordOfVec 6 orbVec[x]! := by decide +kernel

theorem agreeAll_of_rel {ps qs : Prs}
    (hq : ∀ q ∈ qs, wordLin q.1 = wordLin q.2)
    (h : ∀ p ∈ ps, (∀ g ∈ p.1, g.validB = true) ∧ (∀ g ∈ p.2, g.validB = true) ∧
      ∃ q ∈ qs, wordLin p.1 = wordLin q.1 ∧ wordLin p.2 = wordLin q.2) : agreeAll ps = true :=
  agreeAll_of_wordLin (fun p hp => ⟨(h p hp).1, (h p hp).2.1⟩) fun p hp => by
    obtain ⟨-, -, q, hq', e1, e2⟩ := h p hp
    rw [e1, e2]
    exact hq q hq'

@[expose] def OpEqs (qs : Prs) : Prop :=
  ∀ e ∈ qs, (∀ g ∈ e.1, g.validB = true) ∧ (∀ g ∈ e.2, g.validB = true) ∧
    wordLin e.1 = wordLin e.2

theorem pc_gens (hb : OpEqs e13695pc) :
    (∀ k < 6, ∀ g ∈ wq[k]!, g.validB = true) ∧ (∀ k < 6, wordLin wq[k]! ^ 7 = 1) ∧
      ∀ k < 6, wordLin (wq[k]! ++ MonSeven.invW k) = 1 := by
  have m1 : ∀ k < 6, (powL 7 wq[k]!, ([] : List Native.Gen)) ∈ e13695pc := fun k hk => by
    unfold e13695pc pcOf
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  have m3 : ∀ k < 6, (wq[k]! ++ MonSeven.invW k, ([] : List Native.Gen)) ∈ e13695pc := fun k hk => by
    unfold e13695pc pcOf
    exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  refine ⟨fun k hk g hg => (hb _ (m1 k hk)).1 g ?_, fun k hk => ?_, fun k hk => (hb _ (m3 k hk)).2.2⟩
  · change g ∈ powL 7 wq[k]!
    simp only [powL, List.mem_flatten, List.mem_replicate]
    exact ⟨wq[k]!, ⟨by norm_num, rfl⟩, hg⟩
  · have e := (hb _ (m1 k hk)).2.2
    rw [wordLin_powL] at e
    exact e

theorem pc_ok (hb : OpEqs e13695pc) : agreeAll pcPairs = true := by
  obtain ⟨hv, h7, hi⟩ := pc_gens hb
  refine agreeAll_of_rel (qs := e13695pc) (fun q hq => (hb q hq).2.2) fun p hp => ?_
  unfold pcPairs at hp
  rcases List.mem_append.1 hp with hp | hp
  · have hq : p ∈ e13695pc := by
      unfold e13695pc pcOf
      exact List.mem_append_left _ (List.mem_append_left _ hp)
    exact ⟨(hb p hq).1, (hb p hq).2.1, p, hq, rfl, rfl⟩
  · simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hp
    obtain ⟨i, hi6, j, hj6, he⟩ := hp
    split at he
    · rename_i hij
      obtain rfl := Option.some_inj.1 he
      have hq : (wq[j]! ++ wq[i]!, wq[i]! ++ WrhoBOf MonSeven.invW cw7[i * 6 + j]!) ∈ e13695pc := by
        unfold e13695pc pcOf
        refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2
          ⟨i, List.mem_range.2 hi6, List.mem_filterMap.2 ⟨j, List.mem_range.2 hj6, ?_⟩⟩))
        rw [if_pos hij]
      refine ⟨(hb _ hq).1, fun g hg => ?_, _, hq, rfl, ?_⟩
      · rcases List.mem_append.1 hg with hg | hg
        · exact hv i hi6 g hg
        · exact Wrho_valid hv (fun k hk => lt_of_mem_wordOfVec hk) g hg
      · rw [wordLin_append, wordLin_append,
          wordLin_WrhoBOf h7 hi (cw7_le (i * 6 + j) (by omega))]
    · exact absurd he (by simp)

theorem aut_ok (hb : OpEqs e13695pc) (ha : OpEqs e13695aut) :
    agreeAll autPairs = true := by
  obtain ⟨hv, h7, hi⟩ := pc_gens hb
  refine agreeAll_of_rel (qs := e13695aut) (fun q hq => (ha q hq).2.2) fun p hp => ?_
  unfold autPairs at hp
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨a, ha2, i, hi6, rfl⟩ := hp
  have hq : (wq[i]! ++ autW[a]!, autW[a]! ++ WrhoBOf MonSeven.invW ((alphaVecs[a]!)[i]!)) ∈ e13695aut := by
    unfold e13695aut autOf
    exact List.mem_flatMap.2 ⟨a, List.mem_range.2 ha2, List.mem_map.2 ⟨i, List.mem_range.2 hi6, rfl⟩⟩
  refine ⟨(ha _ hq).1, fun g hg => ?_, _, hq, rfl, ?_⟩
  · rcases List.mem_append.1 hg with hg | hg
    · exact (ha _ hq).1 g (List.mem_append_right _ hg)
    · exact Wrho_valid hv (fun k hk => lt_of_mem_wordOfVec hk) g hg
  · rw [wordLin_append, wordLin_append, wordLin_WrhoBOf h7 hi (alphaVecs_le a ha2 i hi6)]

theorem orb_ok (lo hi : ℕ) (hhi : hi ≤ 22) (hb : OpEqs e13695pc)
    (ho : OpEqs (orbOf MonSeven.invW lo hi)) : agreeAll (orbPairs lo hi) = true := by
  obtain ⟨hv, h7, hi7⟩ := pc_gens hb
  refine agreeAll_of_rel (qs := orbOf MonSeven.invW lo hi) (fun q hq => (ho q hq).2.2) fun p hp => ?_
  unfold orbPairs at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  have hk22 : k < 22 := by
    rw [List.mem_range'_1] at hk
    omega
  have hq : (WrhoBOf MonSeven.invW orbVec[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!) ∈
      orbOf MonSeven.invW lo hi := by
    unfold orbOf
    exact List.mem_map.2 ⟨k, hk, rfl⟩
  refine ⟨fun g hg => ?_, (ho _ hq).2.1, _, hq, ?_, rfl⟩
  · rcases List.mem_append.1 hg with hg | hg
    · refine Wrho_valid hv (fun x hx => ?_) g hg
      rw [orbWord_eq k hk22] at hx
      exact lt_of_mem_wordOfVec hx
    · exact (ho _ hq).1 g (List.mem_append_right _ hg)
  · rw [wordLin_append, wordLin_append, orbWord_eq k hk22,
      wordLin_WrhoBOf h7 hi7 (orbVec_le k hk22)]

theorem pc_facts : OpEqs e13695pc := kd_m7% CFSG.KD.M7.c13695pc 27 e13695pc

theorem rat_facts : OpEqs e13695rat := kd_m7% CFSG.KD.M7.c13695rat e13695rat

theorem c13695 : agreeAll pcPairs = true ∧ agreeAll autPairs = true ∧ agreeAll ratPairs = true :=
  ⟨pc_ok pc_facts, aut_ok pc_facts (kd_m7% CFSG.KD.M7.c13695aut 36 e13695aut),
    agreeAll_of_wordLin (fun p hp => ⟨(rat_facts p hp).1, (rat_facts p hp).2.1⟩)
      fun p hp => (rat_facts p hp).2.2⟩

theorem c136300 : agreeAll (orbPairs 0 11) = true :=
  orb_ok 0 11 (by norm_num) pc_facts (kd_m7% CFSG.KD.M7.c136300 24 e136300)

theorem c136301 : agreeAll (orbPairs 11 22) = true :=
  orb_ok 11 22 (by norm_num) pc_facts (kd_m7% CFSG.KD.M7.c136301 42 e136301)

end CertificateChecks.KernelKDenseP.MonSeven

end
