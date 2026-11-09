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
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoEChk4
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.AutGen

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
  rw [h]
  rfl

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

theorem wordLin_pieceW {iw : ℕ → List Native.Gen} (h7 : ∀ k < 6, wordLin wq[k]! ^ 7 = 1)
    (hi : ∀ k < 6, wordLin (wq[k]! ++ iw k) = 1) : ∀ k < 6, ∀ e ≤ 7,
      wordLin (pieceW iw k e) = wordLin wq[k]! ^ e := fun k hk e he => by
  unfold pieceW
  rw [wordLin_bal (h7 k hk) (hi k hk) he, wordLin_powL]

theorem wordLin_pieceR {iw : ℕ → List Native.Gen} (hp : ∀ p ∈ powPrs iw, wordLin p.1 = wordLin p.2)
    (h7 : ∀ k < 6, wordLin wq[k]! ^ 7 = 1) (hi : ∀ k < 6, wordLin (wq[k]! ++ iw k) = 1) :
    ∀ k < 6, ∀ e ≤ 7, wordLin (pieceR iw k e) = wordLin wq[k]! ^ e := fun k hk e he => by
  rw [← wordLin_pieceW h7 hi k hk e he]
  by_cases h : (k, e) ∈ [(1, 2), (1, 5), (3, 4), (4, 2), (4, 4)]
  · exact hp _ (List.mem_map.2 ⟨(k, e), h, rfl⟩)
  · unfold pieceR
    split <;> first | exact absurd (by decide) h | rfl

theorem wordLin_WrhoBOf {pw : ℕ → ℕ → List Native.Gen}
    (hw : ∀ k < 6, ∀ e ≤ 7, wordLin (pw k e) = wordLin wq[k]! ^ e) {v : Array ℕ}
    (hv : ∀ k < 6, v[k]! ≤ 7) : wordLin (WrhoBOf pw v) = wordLin (Wrho (wordOfVec 6 v)) := by
  rw [wordOfVec, Wrho_flatMap]
  unfold WrhoBOf
  exact wordLin_flatMap_congr _ fun k hk => by
    have hk' : k < 6 := List.mem_range.1 (List.mem_reverse.1 hk)
    rw [wordLin_powL]
    exact hw k hk' _ (hv k hk')

theorem cw7_le : ∀ x < 36, ∀ k < 6, (cw7[x]!)[k]! ≤ 7 := by decide +kernel

theorem alphaVecs_le : ∀ a < 2, ∀ i < 6, ∀ k < 6, ((alphaVecs[a]!)[i]!)[k]! ≤ 7 := by
  decide +kernel

theorem orbVec_le : ∀ x < 22, ∀ k < 6, (orbVec[x]!)[k]! ≤ 7 := by decide +kernel

theorem orbWord_eq : ∀ x < 22, orbWord[x]! = wordOfVec 6 orbVec[x]! := by decide +kernel

theorem wordLin_flatMap_inv {f g : ℕ → List Native.Gen} :
    ∀ l : List ℕ, (∀ k ∈ l, wordLin (g k) * wordLin (f k) = 1) →
      wordLin (l.flatMap g) * wordLin (l.reverse.flatMap f) = 1
  | [], _ => by simp [wordLin_nil]
  | a :: l, h => by
    rw [List.flatMap_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, wordLin_append, wordLin_append]
    have ha := h a List.mem_cons_self
    have hl := wordLin_flatMap_inv l fun k hk => h k (List.mem_cons_of_mem a hk)
    rw [mul_assoc, ← mul_assoc (wordLin (g a)), ha, one_mul, hl]

theorem orb_of_split {pw : ℕ → ℕ → List Native.Gen}
    (hw : ∀ k < 6, ∀ e ≤ 7, wordLin (pw k e) = wordLin wq[k]! ^ e)
    (h7 : ∀ k < 6, wordLin wq[k]! ^ 7 = 1) {k s : ℕ} (hk : k < 22) (hs : s ≤ 6)
    (h : wordLin (orbSplitPr pw k s).1 = wordLin (orbSplitPr pw k s).2) :
    wordLin (WrhoBOf pw orbVec[k]! ++ orbT[k]!) = wordLin (orbT[k]! ++ targetW orbKind[k]!) := by
  have hr : List.range 6 = List.range s ++ List.range' s (6 - s) := by
    interval_cases s <;> rfl
  have hinv := wordLin_flatMap_inv (f := fun j => pw j (orbVec[k]!)[j]!)
    (g := fun j => pw j (7 - (orbVec[k]!)[j]!)) (List.range' s (6 - s)) fun j hj => by
      have hj6 : j < 6 := by
        rw [List.mem_range'_1] at hj
        omega
      have he := orbVec_le k hk j hj6
      rw [hw j hj6 _ (Nat.sub_le 7 _), hw j hj6 _ he, ← pow_add, Nat.sub_add_cancel he,
        h7 j hj6]
  unfold orbSplitPr at h
  unfold WrhoBOf
  rw [hr, List.reverse_append, List.flatMap_append]
  simp only [wordLin_append, mul_assoc] at h ⊢
  rw [← mul_assoc, h, mul_assoc, mul_assoc, hinv, mul_one]

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

theorem pow7_of_conj {G : Type*} [Group G] {g x y z : G} {a b : ℕ} (hg : g ^ 7 = 1)
    (hz : z ^ 7 = 1) (hgz : g * z * g⁻¹ = z) (hyz : Commute y z)
    (hx : g * x * g⁻¹ = x * y * z ^ a) (hy : g * y * g⁻¹ = y * z ^ b) : y ^ 7 = 1 := by
  have key : ∀ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = x * y ^ k * z ^ (a * k + b * (List.range k).sum) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = MulAut.conj g (g ^ k * x * (g ^ k)⁻¹) := by
        rw [MulAut.conj_apply, pow_succ']
        group
      rw [hc, ih, map_mul, map_mul, map_pow, map_pow, MulAut.conj_apply, MulAut.conj_apply,
        MulAut.conj_apply, hx, hy, hgz, (hyz.pow_right b).mul_pow, List.range_succ, List.sum_append,
        List.sum_singleton, ← pow_mul]
      have e : a * (k + 1) + b * ((List.range k).sum + k) =
          a + b * k + (a * k + b * (List.range k).sum) := by ring
      rw [e, pow_add z (a + b * k), pow_add z a, pow_succ' y k]
      have hc2 : z ^ a * y ^ k = y ^ k * z ^ a := ((hyz.pow_pow k a).symm).eq
      simp only [mul_assoc]
      rw [← mul_assoc (z ^ a) (y ^ k), hc2, mul_assoc]
  have h7 := key 7
  have e : a * 7 + b * (List.range 7).sum = 7 * (a + 3 * b) := by
    simp only [List.range_succ, List.sum_append, List.sum_singleton, List.range_zero, List.sum_nil]
    ring
  rw [hg, one_mul, inv_one, mul_one, e, pow_mul, hz, one_pow, mul_one] at h7
  exact mul_eq_left.1 h7.symm

theorem comm_of_comm_pow6 {G : Type*} [Group G] {x c : G} (h7 : c ^ 7 = 1)
    (h : Commute x (c ^ 6)) : Commute x c := by
  have e : (c ^ 6) ^ 6 = c := by
    rw [← pow_mul, show 6 * 6 = 7 * 5 + 1 by norm_num, pow_add, pow_mul, h7, one_pow, one_mul, pow_one]
  rw [← e]
  exact h.pow_right 6

theorem comm_of_conj6 {G : Type*} [Group G] {a b c x : G} (h7 : c ^ 7 = 1)
    (hab : a * b * a⁻¹ = b * c ^ 6) (hxa : Commute x a) (hxb : Commute x b) : Commute x c := by
  refine comm_of_comm_pow6 h7 ?_
  have e : c ^ 6 = b⁻¹ * (a * b * a⁻¹) := by rw [hab, inv_mul_cancel_left]
  rw [e]
  exact hxb.inv_right.mul_right ((hxa.mul_right hxb).mul_right hxa.inv_right)

theorem conj6_twist {G : Type*} [Group G] {u v k l : G} (hku : Commute k u) (hkv : Commute k v)
    (hkl : Commute k l) (hlu : Commute l u) :
    (u * k)⁻¹ * (v * l) * (u * k) * (v * l)⁻¹ = u⁻¹ * v * u * v⁻¹ := by
  have hk : Commute k (u⁻¹ * (v * l) * u) := (hku.inv_right.mul_right (hkv.mul_right hkl)).mul_right hku
  calc (u * k)⁻¹ * (v * l) * (u * k) * (v * l)⁻¹ = k⁻¹ * (u⁻¹ * (v * l) * u) * k * (v * l)⁻¹ := by
        group
    _ = u⁻¹ * v * (l * u * l⁻¹) * v⁻¹ := by
        rw [hk.inv_mul_cancel]
        group
    _ = u⁻¹ * v * u * v⁻¹ := by rw [hlu.mul_inv_cancel]

theorem conj_fix_of_conj6 {G : Type*} [Group G] {g a b c d : G} {m n : ℕ} (h7 : c ^ 7 = 1)
    (hab : a * b * a⁻¹ = b * c ^ 6) (hga : g * a * g⁻¹ = a * b * c ^ m)
    (hgb : g * b * g⁻¹ = b * d * c ^ n) (hda : Commute d a) (hdb : Commute d b)
    (hca : Commute c a) (hcb : Commute c b) (hcd : Commute c d) : g * c * g⁻¹ = c := by
  have e : c ^ 6 = b⁻¹ * (a * b * a⁻¹) := by rw [hab, inv_mul_cancel_left]
  have hd : Commute d (b⁻¹ * a * b * b) := ((hdb.inv_right.mul_right hda).mul_right hdb).mul_right hdb
  have h6 : g * c ^ 6 * g⁻¹ = c ^ 6 := by
    calc g * c ^ 6 * g⁻¹ = (g * b * g⁻¹)⁻¹ * (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ := by
          rw [e]
          group
      _ = (b * d)⁻¹ * (a * b) * (b * d) * (a * b)⁻¹ := by
          rw [hga, hgb]
          exact conj6_twist ((hcb.mul_right hcd).pow_left n) ((hca.mul_right hcb).pow_left n)
            ((Commute.refl c).pow_pow n m) ((hcb.mul_right hcd).pow_left m)
      _ = d⁻¹ * (b⁻¹ * a * b * b) * d * b⁻¹ * a⁻¹ := by group
      _ = c ^ 6 := by
          rw [mul_assoc d⁻¹, hd.inv_mul_cancel_assoc, e]
          group
  exact mul_inv_eq_of_eq_mul (comm_of_comm_pow6 h7 (mul_inv_eq_iff_eq_mul.1 h6)).eq

theorem conj_fix_of_conj1 {G : Type*} [Group G] {g a b c : G} {m n : ℕ} (h7 : c ^ 7 = 1)
    (hab : a * b * a⁻¹ = b * c ^ 6) (hga : g * a * g⁻¹ = a * c ^ m) (hgb : g * b * g⁻¹ = b * c ^ n)
    (hca : Commute c a) (hcb : Commute c b) : g * c * g⁻¹ = c := by
  have e : c ^ 6 = b⁻¹ * (a * b * a⁻¹) := by rw [hab, inv_mul_cancel_left]
  have h6 : g * c ^ 6 * g⁻¹ = c ^ 6 := by
    calc g * c ^ 6 * g⁻¹ = (g * b * g⁻¹)⁻¹ * (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ := by
          rw [e]
          group
      _ = c ^ 6 := by
          rw [hga, hgb, conj6_twist (hcb.pow_left n) (hca.pow_left n) ((Commute.refl c).pow_pow n m)
            (hcb.pow_left m), e]
          group
  exact mul_inv_eq_of_eq_mul (comm_of_comm_pow6 h7 (mul_inv_eq_iff_eq_mul.1 h6)).eq

theorem swap_pow_of_mul {G : Type*} [Group G] {x y d : G} (h : y * x = x * y * d)
    (hx : Commute x d) (hy : Commute y d) (m n : ℕ) : y ^ m * x ^ n = x ^ n * y ^ m * d ^ (m * n) := by
  have h1 : ∀ n : ℕ, y * x ^ n = x ^ n * y * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y * x ^ (n + 1) = (y * x ^ n) * x := by rw [pow_succ, mul_assoc]
        _ = x ^ n * y * (d ^ n * x) := by rw [ih]; simp only [mul_assoc]
        _ = x ^ n * (y * x) * d ^ n := by rw [← (hx.pow_right n).eq]; simp only [mul_assoc]
        _ = x ^ (n + 1) * y * d ^ (n + 1) := by
          rw [h, pow_succ, pow_succ']; simp only [mul_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    calc y ^ (m + 1) * x ^ n = y ^ m * (y * x ^ n) := by rw [pow_succ, mul_assoc]
      _ = (y ^ m * x ^ n) * y * d ^ n := by rw [h1]; simp only [mul_assoc]
      _ = x ^ n * y ^ m * (d ^ (m * n) * y) * d ^ n := by rw [ih]; simp only [mul_assoc]
      _ = x ^ n * y ^ (m + 1) * d ^ ((m + 1) * n) := by
        rw [← (hy.pow_right (m * n)).eq, add_mul, one_mul, pow_add d, pow_succ]
        simp only [mul_assoc]

theorem swap_of_conj6 {G : Type*} [Group G] {x y d : G} (h : x * y * x⁻¹ = y * d ^ 6)
    (hd : d ^ 7 = 1) (hxd : Commute x d) : y * x = x * y * d := by
  have hd' : d ^ 6 * d = 1 := by rw [← pow_succ]; exact hd
  rw [mul_inv_eq_iff_eq_mul.1 h, mul_assoc (y * d ^ 6), hxd.eq, ← mul_assoc, mul_assoc y, hd', mul_one]

theorem piece_pow {G : Type*} [Group G] {q w : G} (h7 : q ^ 7 = 1) (hw : w = q⁻¹) {e : ℕ}
    (he : e ≤ 7) : (if e ≤ 3 then q ^ e else w ^ (7 - e)) = q ^ e := by
  split
  · rfl
  · rw [hw, inv_pow]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add, Nat.add_sub_cancel' he, h7]

@[expose] def m7nf {G : Type*} [Group G] (a b c d : G) (i j k l : ℕ) : G :=
  a ^ i * b ^ j * c ^ k * d ^ l

theorem m7nf_mul {G : Type*} [Group G] {a b c d : G} (hab : b * a = a * b * d) (hac : Commute a c)
    (hbc : Commute b c) (had : Commute a d) (hbd : Commute b d) (hcd : Commute c d)
    (i j k l i' j' k' l' : ℕ) :
    m7nf a b c d i j k l * m7nf a b c d i' j' k' l' =
      m7nf a b c d (i + i') (j + j') (k + k') (l + l' + j * i') := by
  have e3 := swap_pow_of_mul hab had hbd j i'
  unfold m7nf
  rw [pow_add a, pow_add b, pow_add c, pow_add d, pow_add d]
  simp only [mul_assoc, (had.pow_pow i' l).symm.left_comm, (hbd.pow_pow j' l).symm.left_comm,
    (hcd.pow_pow k' l).symm.left_comm, (hac.pow_pow i' k).symm.left_comm,
    (hbc.pow_pow j' k).symm.left_comm]
  have e3' : ∀ r : G, b ^ j * (a ^ i' * r) = a ^ i' * (b ^ j * (d ^ (j * i') * r)) := fun r => by
    rw [← mul_assoc, e3]
    simp only [mul_assoc]
  rw [e3']
  simp only [(hbd.pow_pow j' (j * i')).symm.left_comm, (hcd.pow_pow k (j * i')).symm.left_comm,
    (hcd.pow_pow k' (j * i')).symm.left_comm]
  simp only [← pow_add]
  rw [Nat.add_comm (j * i'), Nat.add_assoc]

theorem m7nf_pow {G : Type*} [Group G] {a b c d : G} (hab : b * a = a * b * d) (hac : Commute a c)
    (hbc : Commute b c) (had : Commute a d) (hbd : Commute b d) (hcd : Commute c d)
    (i j k l n : ℕ) :
    m7nf a b c d i j k l ^ n =
      m7nf a b c d (n * i) (n * j) (n * k) (n * l + n.choose 2 * (j * i)) := by
  induction n with
  | zero => simp [m7nf]
  | succ n ih =>
    rw [pow_succ, ih, m7nf_mul hab hac hbc had hbd hcd]
    congr 1
    · ring
    · ring
    · ring
    · rw [Nat.choose_succ_succ', Nat.choose_one_right]
      ring

theorem m7nf_conj {G : Type*} [Group G] {g a b c d : G} (hga : g * a * g⁻¹ = a * b * d ^ 4)
    (hgb : g * b * g⁻¹ = b * c * d ^ 5) (hgc : g * c * g⁻¹ = c * d ^ 2) (hgd : g * d * g⁻¹ = d)
    (i j k l : ℕ) :
    g * m7nf a b c d i j k l * g⁻¹ = m7nf a b c d 1 1 0 4 ^ i * m7nf a b c d 0 1 1 5 ^ j *
      m7nf a b c d 0 0 1 2 ^ k * m7nf a b c d 0 0 0 l := by
  rw [← MulAut.conj_apply]
  unfold m7nf
  simp only [map_mul, map_pow, MulAut.conj_apply, hga, hgb, hgc, hgd, pow_zero, pow_one, one_mul,
    mul_one]

theorem pow7_conj_nest {G : Type*} [Group G] {g x u : G} (hg : g ^ 7 = 1)
    (hx : g * x * g⁻¹ = x * u) :
    u * (g * (u * (g * (u * (g * (u * (g * (u * (g * (u * (g * (u * (g * 1 * g⁻¹)) * g⁻¹)) *
      g⁻¹)) * g⁻¹)) * g⁻¹)) * g⁻¹)) * g⁻¹) = 1 := by
  have h1 : x⁻¹ * g * x = u * g := by
    rw [← mul_inv_cancel_right (x⁻¹ * g * x) g, ← inv_mul_cancel_left x u, ← hx]
    group
  have h7 : (u * g) ^ 7 * (g ^ 7)⁻¹ = 1 := by
    have e := map_pow (MulAut.conj x⁻¹) g 7
    simp only [MulAut.conj_apply, inv_inv] at e
    rw [← h1, ← e, hg]
    group
  simp only [pow_succ, pow_zero, one_mul] at h7
  refine Eq.trans ?_ h7
  group

theorem pow7_q3 {G : Type*} [Group G] {g a b c d : G} (hab : b * a = a * b * d)
    (hac : Commute a c) (hbc : Commute b c) (had : Commute a d) (hbd : Commute b d)
    (hcd : Commute c d) (hga : g * a * g⁻¹ = a * b * d ^ 4) (hgb : g * b * g⁻¹ = b * c * d ^ 5)
    (hgc : g * c * g⁻¹ = c * d ^ 2) (hgd : g * d * g⁻¹ = d) (hg : g ^ 7 = 1) (hc : c ^ 7 = 1)
    (hd : d ^ 7 = 1) : b ^ 7 = 1 := by
  have h := pow7_conj_nest (x := a) (u := m7nf a b c d 0 1 0 4) hg
    (by rw [hga]; simp [m7nf, mul_assoc])
  rw [← show m7nf a b c d 0 0 0 0 = 1 by simp [m7nf]] at h
  simp only [m7nf_conj hga hgb hgc hgd, m7nf_pow hab hac hbc had hbd hcd,
    m7nf_mul hab hac hbc had hbd hcd, Nat.choose_two_right, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceDiv] at h
  unfold m7nf at h
  rw [show (21 : ℕ) = 7 * 3 from rfl, show (203 : ℕ) = 7 * 29 from rfl, pow_mul, pow_mul, hc,
    hd] at h
  simpa using h

theorem pow7_q2 {G : Type*} [Group G] {g x a b c d : G} (hab : b * a = a * b * d)
    (hac : Commute a c) (hbc : Commute b c) (had : Commute a d) (hbd : Commute b d)
    (hcd : Commute c d) (hga : g * a * g⁻¹ = a * b * d ^ 4) (hgb : g * b * g⁻¹ = b * c * d ^ 5)
    (hgc : g * c * g⁻¹ = c * d ^ 2) (hgd : g * d * g⁻¹ = d) (hg : g ^ 7 = 1) (hb : b ^ 7 = 1)
    (hc : c ^ 7 = 1) (hd : d ^ 7 = 1) (hx : g * x * g⁻¹ = x * a * d ^ 3) : a ^ 7 = 1 := by
  have h := pow7_conj_nest (x := x) (u := m7nf a b c d 1 0 0 3) hg
    (by rw [hx]; simp [m7nf, mul_assoc])
  rw [← show m7nf a b c d 0 0 0 0 = 1 by simp [m7nf]] at h
  simp only [m7nf_conj hga hgb hgc hgd, m7nf_pow hab hac hbc had hbd hcd,
    m7nf_mul hab hac hbc had hbd hcd, Nat.choose_two_right, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceDiv] at h
  unfold m7nf at h
  rw [show (21 : ℕ) = 7 * 3 from rfl, show (35 : ℕ) = 7 * 5 from rfl,
    show (385 : ℕ) = 7 * 55 from rfl, pow_mul, pow_mul, pow_mul, hb, hc, hd] at h
  simpa using h

theorem wordLin_revFlatMap (f : ℕ → List Native.Gen) : ∀ l : List ℕ,
    wordLin (l.reverse.flatMap f) = (l.map fun k => wordLin (f k)).prod
  | [] => rfl
  | a :: l => by
    rw [List.reverse_cons, List.flatMap_append, wordLin_append, wordLin_revFlatMap f l]
    simp

theorem prod_range_six {G : Type*} [Monoid G] (T : ℕ → G) :
    ((List.range 6).map T).prod = T 0 * T 1 * T 2 * T 3 * T 4 * T 5 := by
  simp [List.range_succ, mul_assoc]

theorem wordLin_piece (v : Array ℕ) (k e : ℕ) (h : v[k]! = e) :
    wordLin (if v[k]! ≤ 3 then powL v[k]! wq[k]! else powL (7 - v[k]!) (MonSeven.invW k)) =
      if e ≤ 3 then wordLin wq[k]! ^ e else wordLin (MonSeven.invW k) ^ (7 - e) := by
  subst h
  split <;> rw [wordLin_powL]

theorem pc_conj (hb : OpEqs e13695pc) {i j : ℕ} (hi : i < 6) (hj : j < 6) (hij : i < j)
    (hd : j < 5 ∨ i = 2 ∨ i = 3) :
    wordLin wq[i]! * wordLin wq[j]! * (wordLin wq[i]!)⁻¹ =
      ((List.range 6).map fun k => wordLin (if (cw7[i * 6 + j]!)[k]! ≤ 3 then
        powL (cw7[i * 6 + j]!)[k]! wq[k]! else powL (7 - (cw7[i * 6 + j]!)[k]!) (MonSeven.invW k))).prod := by
  have hq : (wq[j]! ++ wq[i]!, wq[i]! ++ WrhoBOf (pieceW MonSeven.invW) cw7[i * 6 + j]!) ∈
      e13695pc := by
    unfold e13695pc pcOf
    refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2
      ⟨i, List.mem_range.2 hi, List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩⟩))
    rw [ite_eq_left ⟨hij, hd⟩]
  have e := (hb _ hq).2.2
  rw [wordLin_append, wordLin_append] at e
  rw [e, mul_inv_cancel_right]
  unfold WrhoBOf pieceW
  rw [wordLin_revFlatMap]

theorem pc_gens (hb : OpEqs e13695pc) :
    (∀ k < 6, ∀ g ∈ wq[k]!, g.validB = true) ∧ (∀ k < 6, wordLin wq[k]! ^ 7 = 1) ∧
      (∀ k < 6, wordLin (wq[k]! ++ MonSeven.invW k) = 1) ∧
      ∀ i < 5, Commute (wordLin wq[i]!) (wordLin wq[5]!) := by
  have m1 : ∀ k ∈ [0, 1, 5], (powL 7 wq[k]!, ([] : List Native.Gen)) ∈ e13695pc := fun k hk => by
    unfold e13695pc pcOf
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨k, hk, rfl⟩))
  have m3 : ∀ k < 6, (wq[k]! ++ MonSeven.invW k, ([] : List Native.Gen)) ∈ e13695pc := fun k hk => by
    unfold e13695pc pcOf
    exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  have hi : ∀ k < 6, wordLin (wq[k]! ++ MonSeven.invW k) = 1 := fun k hk => (hb _ (m3 k hk)).2.2
  have hinv : ∀ k < 6, wordLin (MonSeven.invW k) = (wordLin wq[k]!)⁻¹ := fun k hk => by
    have e := hi k hk
    rw [wordLin_append] at e
    exact eq_inv_of_mul_eq_one_left e
  have h7d : ∀ k ∈ [0, 1, 5], wordLin wq[k]! ^ 7 = 1 := fun k hk => by
    have e := (hb _ (m1 k hk)).2.2
    rw [wordLin_powL] at e
    exact e
  have h4 : ∀ k < 2, wordLin wq[k]! ^ 7 = 1 := fun k hk => h7d k (by interval_cases k <;> simp)
  have h5 : wordLin wq[5]! ^ 7 = 1 := h7d 5 (by simp)
  have hw : (wordLin wq[5]!)⁻¹ = wordLin wq[5]! ^ 6 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h5])
  have p5 : ∀ {e : ℕ}, e ≤ 7 → (if e ≤ 3 then wordLin wq[5]! ^ e else
      wordLin (MonSeven.invW 5) ^ (7 - e)) = wordLin wq[5]! ^ e :=
    fun he => piece_pow h5 (hinv 5 (by norm_num)) he
  have hz23 : ∀ i, 2 ≤ i → i < 4 →
      wordLin wq[i]! * wordLin wq[5]! * (wordLin wq[i]!)⁻¹ = wordLin wq[5]! := fun i hi2 hi4 => by
    rw [pc_conj hb (by omega) (by norm_num) (by omega) (by omega), prod_range_six]
    interval_cases i <;>
    rw [wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 0 (by decide +kernel),
      wordLin_piece _ 4 0 (by decide +kernel), wordLin_piece _ 5 1 (by decide +kernel)] <;>
    norm_num
  have hzc23 : ∀ i, 2 ≤ i → i < 4 → Commute (wordLin wq[i]!) (wordLin wq[5]!) := fun i hi2 hi4 =>
    mul_inv_eq_iff_eq_mul.1 (hz23 i hi2 hi4)
  have c02 : wordLin wq[0]! * wordLin wq[2]! * (wordLin wq[0]!)⁻¹ =
      wordLin wq[2]! * wordLin wq[3]! * wordLin wq[5]! ^ 4 := by
    have e := pc_conj hb (i := 0) (j := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 1 (by decide +kernel), wordLin_piece _ 3 1 (by decide +kernel),
      wordLin_piece _ 4 0 (by decide +kernel), wordLin_piece _ 5 4 (by decide +kernel),
      p5 (by norm_num)] at e
    norm_num at e
    exact e
  have c03 : wordLin wq[0]! * wordLin wq[3]! * (wordLin wq[0]!)⁻¹ =
      wordLin wq[3]! * wordLin wq[4]! * wordLin wq[5]! ^ 5 := by
    have e := pc_conj hb (i := 0) (j := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 1 (by decide +kernel),
      wordLin_piece _ 4 1 (by decide +kernel), wordLin_piece _ 5 5 (by decide +kernel),
      p5 (by norm_num)] at e
    norm_num at e
    exact e
  have c12 : wordLin wq[1]! * wordLin wq[2]! * (wordLin wq[1]!)⁻¹ =
      wordLin wq[2]! * wordLin wq[5]! ^ 6 := by
    have e := pc_conj hb (i := 1) (j := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 1 (by decide +kernel), wordLin_piece _ 3 0 (by decide +kernel),
      wordLin_piece _ 4 0 (by decide +kernel), wordLin_piece _ 5 6 (by decide +kernel),
      p5 (by norm_num)] at e
    norm_num at e
    exact e
  have c13 : wordLin wq[1]! * wordLin wq[3]! * (wordLin wq[1]!)⁻¹ =
      wordLin wq[3]! * wordLin wq[5]! ^ 1 := by
    have e := pc_conj hb (i := 1) (j := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 1 (by decide +kernel),
      wordLin_piece _ 4 0 (by decide +kernel), wordLin_piece _ 5 1 (by decide +kernel)] at e
    norm_num at e
    rw [pow_one]
    exact e
  have c23 : wordLin wq[2]! * wordLin wq[3]! * (wordLin wq[2]!)⁻¹ =
      wordLin wq[3]! * wordLin wq[5]! ^ 6 := by
    have e := pc_conj hb (i := 2) (j := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 1 (by decide +kernel),
      wordLin_piece _ 4 0 (by decide +kernel), wordLin_piece _ 5 6 (by decide +kernel),
      p5 (by norm_num)] at e
    norm_num at e
    exact e
  have c4 : ∀ i, 2 ≤ i → i < 4 → Commute (wordLin wq[i]!) (wordLin wq[4]!) := fun i hi2 hi4 => by
    have e := pc_conj hb (i := i) (j := 4) (by omega) (by norm_num) (by omega) (by norm_num)
    rw [prod_range_six] at e
    interval_cases i <;>
    rw [wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 0 (by decide +kernel),
      wordLin_piece _ 4 1 (by decide +kernel), wordLin_piece _ 5 0 (by decide +kernel)] at e <;>
    norm_num at e <;>
    exact mul_inv_eq_iff_eq_mul.1 e
  have h45 : Commute (wordLin wq[4]!) (wordLin wq[5]!) :=
    comm_of_conj6 h5 c23 (c4 2 le_rfl (by norm_num)).symm (c4 3 (by norm_num) (by norm_num)).symm
  have hz : ∀ i < 5, wordLin wq[i]! * wordLin wq[5]! * (wordLin wq[i]!)⁻¹ = wordLin wq[5]! :=
    fun i hi5 => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i < 4) ∨ i = 4) with rfl | rfl | ⟨h2, h4⟩ | rfl
      · exact conj_fix_of_conj6 h5 c23 c02 c03 (c4 2 le_rfl (by norm_num)).symm
          (c4 3 (by norm_num) (by norm_num)).symm (hzc23 2 le_rfl (by norm_num)).symm
          (hzc23 3 (by norm_num) (by norm_num)).symm h45.symm
      · exact conj_fix_of_conj1 h5 c23 c12 c13 (hzc23 2 le_rfl (by norm_num)).symm
          (hzc23 3 (by norm_num) (by norm_num)).symm
      · exact hz23 i h2 h4
      · exact h45.mul_inv_cancel
  have hzc : ∀ i < 5, Commute (wordLin wq[i]!) (wordLin wq[5]!) := fun i hi5 =>
    mul_inv_eq_iff_eq_mul.1 (hz i hi5)
  have h4' : wordLin wq[4]! ^ 7 = 1 := by
    have e3 := pc_conj hb (i := 0) (j := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 1 (by decide +kernel),
      wordLin_piece _ 4 1 (by decide +kernel), wordLin_piece _ 5 5 (by decide +kernel),
      hinv 5 (by norm_num), hw, ← pow_mul] at e3
    norm_num at e3
    have e4 := pc_conj hb (i := 0) (j := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 0 (by decide +kernel),
      wordLin_piece _ 4 1 (by decide +kernel), wordLin_piece _ 5 2 (by decide +kernel)] at e4
    norm_num at e4
    exact pow7_of_conj (h4 0 (by norm_num)) h5 (hz 0 (by norm_num)) (hzc 4 (by norm_num)) e3 e4
  have c01 : wordLin wq[0]! * wordLin wq[1]! * (wordLin wq[0]!)⁻¹ =
      wordLin wq[1]! * wordLin wq[2]! * wordLin wq[5]! ^ 3 := by
    have e := pc_conj hb (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 1 (by decide +kernel),
      wordLin_piece _ 2 1 (by decide +kernel), wordLin_piece _ 3 0 (by decide +kernel),
      wordLin_piece _ 4 0 (by decide +kernel), wordLin_piece _ 5 3 (by decide +kernel)] at e
    norm_num at e
    exact e
  have c04 : wordLin wq[0]! * wordLin wq[4]! * (wordLin wq[0]!)⁻¹ =
      wordLin wq[4]! * wordLin wq[5]! ^ 2 := by
    have e := pc_conj hb (i := 0) (j := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [prod_range_six, wordLin_piece _ 0 0 (by decide +kernel), wordLin_piece _ 1 0 (by decide +kernel),
      wordLin_piece _ 2 0 (by decide +kernel), wordLin_piece _ 3 0 (by decide +kernel),
      wordLin_piece _ 4 1 (by decide +kernel), wordLin_piece _ 5 2 (by decide +kernel)] at e
    norm_num at e
    exact e
  have hab := swap_of_conj6 c23 h5 (hzc 2 (by norm_num))
  have h3 := pow7_q3 hab (c4 2 le_rfl (by norm_num)) (c4 3 (by norm_num) (by norm_num))
    (hzc 2 (by norm_num)) (hzc 3 (by norm_num)) (hzc 4 (by norm_num)) c02 c03 c04 (hz 0 (by norm_num))
    (h4 0 (by norm_num)) h4' h5
  have h2 := pow7_q2 hab (c4 2 le_rfl (by norm_num)) (c4 3 (by norm_num) (by norm_num))
    (hzc 2 (by norm_num)) (hzc 3 (by norm_num)) (hzc 4 (by norm_num)) c02 c03 c04 (hz 0 (by norm_num))
    (h4 0 (by norm_num)) h3 h4' h5 c01
  refine ⟨fun k hk g hg => (hb _ (m3 k hk)).1 g (List.mem_append_left _ hg), fun k hk => ?_, hi, hzc⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exact h4 k hk2
  · interval_cases k
    · exact h2
    · exact h3
    · exact h4'
    · exact h5

theorem pc_pair (hb : OpEqs e13695pc) (hv : ∀ k < 6, ∀ g ∈ wq[k]!, g.validB = true)
    (h7 : ∀ k < 6, wordLin wq[k]! ^ 7 = 1) (hi : ∀ k < 6, wordLin (wq[k]! ++ MonSeven.invW k) = 1)
    (hz : ∀ i < 5, Commute (wordLin wq[i]!) (wordLin wq[5]!)) :
    ∀ p ∈ pcPairs, (∀ g ∈ p.1, g.validB = true) ∧ (∀ g ∈ p.2, g.validB = true) ∧
      wordLin p.1 = wordLin p.2 := by
  intro p hp
  unfold pcPairs at hp
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
    have hk6 := List.mem_range.1 hk
    refine ⟨fun g hg => ?_, by simp, ?_⟩
    · simp only [powL, List.mem_flatten, List.mem_replicate] at hg
      obtain ⟨l, ⟨-, rfl⟩, hg⟩ := hg
      exact hv k hk6 g hg
    · rw [wordLin_powL, h7 k hk6]
      rfl
  · simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hp
    obtain ⟨i, hi6, j, hj6, he⟩ := hp
    split at he
    · rename_i hij
      obtain rfl := Option.some_inj.1 he
      refine ⟨fun g hg => ?_, fun g hg => ?_, ?_⟩
      · rcases List.mem_append.1 hg with hg | hg
        · exact hv j hj6 g hg
        · exact hv i hi6 g hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact hv i hi6 g hg
        · exact Wrho_valid hv (fun k hk => lt_of_mem_wordOfVec hk) g hg
      by_cases hd : j < 5 ∨ i = 2 ∨ i = 3
      · have hq : (wq[j]! ++ wq[i]!, wq[i]! ++ WrhoBOf (pieceW MonSeven.invW) cw7[i * 6 + j]!) ∈
            e13695pc := by
          unfold e13695pc pcOf
          refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2
            ⟨i, List.mem_range.2 hi6, List.mem_filterMap.2 ⟨j, List.mem_range.2 hj6, ?_⟩⟩))
          rw [ite_eq_left ⟨hij, hd⟩]
        refine (hb _ hq).2.2.trans ?_
        rw [wordLin_append, wordLin_append,
          wordLin_WrhoBOf (wordLin_pieceW h7 hi) (cw7_le (i * 6 + j) (by omega))]
      · obtain rfl : j = 5 := by omega
        have hw5 : ∀ i < 5, wordOfVec 6 cw7[i * 6 + 5]! = [5] := by decide +kernel
        rw [wordLin_append, wordLin_append, hw5 i (by omega)]
        simp only [Wrho, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.flatten_cons, List.flatten_nil, List.append_nil]
        exact (hz i (by omega)).eq
    · exact absurd he (by simp)

theorem pc_ok (hb : OpEqs e13695pc) : agreeAll pcPairs = true := by
  obtain ⟨hv, h7, hi, hz⟩ := pc_gens hb
  have H := pc_pair hb hv h7 hi hz
  exact agreeAll_of_wordLin (fun p hp => ⟨(H p hp).1, (H p hp).2.1⟩) fun p hp => (H p hp).2.2

@[expose] def PieceOK (pw : ℕ → ℕ → List Native.Gen) : Prop :=
  (∀ k < 6, wordLin wq[k]! ^ 7 = 1) → (∀ k < 6, wordLin (wq[k]! ++ MonSeven.invW k) = 1) →
    ∀ k < 6, ∀ e ≤ 7, wordLin (pw k e) = wordLin wq[k]! ^ e

theorem aut_ok_gens {pw : ℕ → ℕ → List Native.Gen} (hb : OpEqs e13695pc) (hw : PieceOK pw)
    (ha : OpEqs (autGOf pw)) : agreeAll autPairs = true := by
  obtain ⟨hv, h7, hi, -⟩ := pc_gens hb
  have mem : ∀ a < 2, ∀ i < 2,
      (wq[i]! ++ autW[a]!, autW[a]! ++ WrhoBOf pw ((alphaVecs[a]!)[i]!)) ∈ autGOf pw :=
    fun a ha2 i hi2 => by
      unfold autGOf
      exact List.mem_flatMap.2 ⟨a, List.mem_range.2 ha2, List.mem_map.2 ⟨i, List.mem_range.2 hi2, rfl⟩⟩
  have hA : ∀ a < 2, ∀ g ∈ autW[a]!, g.validB = true := fun a ha2 g hg =>
    (ha _ (mem a ha2 0 (by norm_num))).1 g (List.mem_append_right _ hg)
  have h01 : ∀ a < 2, ∀ i < 2,
      gw (wq[i]! ++ autW[a]!) = gw (autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!))) :=
    fun a ha2 i hi2 => by
      have e := (ha _ (mem a ha2 i hi2)).2.2
      rw [wordLin_append, wordLin_append,
        wordLin_WrhoBOf (hw h7 hi) (alphaVecs_le a ha2 i (by omega))] at e
      refine Subtype.ext ?_
      change wordLin _ = wordLin _
      rw [wordLin_append, wordLin_append]
      exact e
  have hall := AutGen.autPairs_of_gens (pc_ok hb) h01
  have hP : ∀ p ∈ autPairs, ∃ a < 2, ∃ i < 6,
      p = (wq[i]! ++ autW[a]!, autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!))) := by
    intro p hp
    unfold autPairs at hp
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
    obtain ⟨a, ha2, i, hi6, rfl⟩ := hp
    exact ⟨a, ha2, i, hi6, rfl⟩
  refine agreeAll_of_rel (qs := autPairs) (fun q hq => ?_) fun p hp => ?_
  · obtain ⟨a, ha2, i, hi6, rfl⟩ := hP q hq
    exact congrArg Subtype.val (hall a ha2 i hi6)
  · obtain ⟨a, ha2, i, hi6, rfl⟩ := hP p hp
    refine ⟨fun g hg => ?_, fun g hg => ?_, _, hp, rfl, rfl⟩
    · rcases List.mem_append.1 hg with hg | hg
      · exact hv i hi6 g hg
      · exact hA a ha2 g hg
    · rcases List.mem_append.1 hg with hg | hg
      · exact hA a ha2 g hg
      · exact Wrho_valid hv (fun k hk => lt_of_mem_wordOfVec hk) g hg

theorem orb_facts_of_split {pw : ℕ → ℕ → List Native.Gen}
    (hw : ∀ k < 6, ∀ e ≤ 7, wordLin (pw k e) = wordLin wq[k]! ^ e)
    (h7 : ∀ k < 6, wordLin wq[k]! ^ 7 = 1) {k s : ℕ} (hk : k < 22) (hs : s ≤ 6)
    (h : (∀ g ∈ (orbSplitPr pw k s).1, g.validB = true) ∧
      (∀ g ∈ (orbSplitPr pw k s).2, g.validB = true) ∧
      wordLin (orbSplitPr pw k s).1 = wordLin (orbSplitPr pw k s).2) :
    (∀ g ∈ orbT[k]!, g.validB = true) ∧
      (∀ g ∈ orbT[k]! ++ targetW orbKind[k]!, g.validB = true) ∧
      wordLin (WrhoBOf pw orbVec[k]! ++ orbT[k]!) = wordLin (orbT[k]! ++ targetW orbKind[k]!) := by
  refine ⟨fun g hg => h.1 g (List.mem_append_right _ hg), fun g hg => ?_,
    orb_of_split hw h7 hk hs h.2.2⟩
  rcases List.mem_append.1 hg with hg | hg
  · exact h.2.1 g (List.mem_append_left _ (List.mem_append_right _ hg))
  · exact h.2.1 g (List.mem_append_right _ hg)

theorem orb_ok {pw : ℕ → ℕ → List Native.Gen} (lo hi : ℕ) (hhi : hi ≤ 22) (hb : OpEqs e13695pc)
    (hw : PieceOK pw) (ho : ∀ k ∈ List.range' lo (hi - lo), (∀ g ∈ orbT[k]!, g.validB = true) ∧
      (∀ g ∈ orbT[k]! ++ targetW orbKind[k]!, g.validB = true) ∧
      wordLin (WrhoBOf pw orbVec[k]! ++ orbT[k]!) = wordLin (orbT[k]! ++ targetW orbKind[k]!)) :
    agreeAll (orbPairs lo hi) = true := by
  obtain ⟨hv, h7, hi7, -⟩ := pc_gens hb
  refine agreeAll_of_rel (qs := orbOf pw lo hi) (fun q hq => ?_) fun p hp => ?_
  · unfold orbOf at hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
    exact (ho k hk).2.2
  unfold orbPairs at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  have hk22 : k < 22 := by
    rw [List.mem_range'_1] at hk
    omega
  have hq : (WrhoBOf pw orbVec[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!) ∈
      orbOf pw lo hi := by
    unfold orbOf
    exact List.mem_map.2 ⟨k, hk, rfl⟩
  refine ⟨fun g hg => ?_, (ho k hk).2.1, _, hq, ?_, rfl⟩
  · rcases List.mem_append.1 hg with hg | hg
    · refine Wrho_valid hv (fun x hx => ?_) g hg
      rw [orbWord_eq k hk22] at hx
      exact lt_of_mem_wordOfVec hx
    · exact (ho k hk).1 g hg
  · rw [wordLin_append, wordLin_append, orbWord_eq k hk22,
      wordLin_WrhoBOf (hw h7 hi7) (orbVec_le k hk22)]

theorem pc_facts : OpEqs e13695pc := kd_m7% CFSG.KD.M7.c13695pc 282 e13695pc

theorem rat_facts : OpEqs e13695rat := kd_m7% CFSG.KD.M7.c13695rat e13695rat

theorem f136301 : OpEqs e136301 := kd_m7% CFSG.KD.M7.c136301 267 e136301

theorem pieceR_ok : PieceOK (pieceR MonSeven.invW) :=
  wordLin_pieceR fun p hp => (f136301 p (List.mem_append_right _ hp)).2.2

theorem c13695 : agreeAll pcPairs = true ∧ agreeAll autPairs = true ∧ agreeAll ratPairs = true :=
  ⟨pc_ok pc_facts, aut_ok_gens pc_facts pieceR_ok (kd_m7% CFSG.KD.M7.c13695aut 126 e13695autG),
    agreeAll_of_wordLin (fun p hp => ⟨(rat_facts p hp).1, (rat_facts p hp).2.1⟩)
      fun p hp => (rat_facts p hp).2.2⟩

theorem c136300 : agreeAll (orbPairs 0 11) = true := by
  obtain ⟨-, h7, hi7, -⟩ := pc_gens pc_facts
  have H : OpEqs e136300 := kd_m7% CFSG.KD.M7.c136300 204 e136300
  have hs : ∀ k < 11, #[6, 6, 6, 4, 4, 4, 6, 4, 4, 6, 4][k]! ≤ 6 := by decide
  refine orb_ok 0 11 (by norm_num) pc_facts pieceR_ok fun k hk => ?_
  rw [List.mem_range'_1] at hk
  exact orb_facts_of_split (pieceR_ok h7 hi7) h7 (by omega) (hs k (by omega))
    (H _ (List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩))

theorem c136301 : agreeAll (orbPairs 11 22) = true := by
  obtain ⟨-, h7, hi7, -⟩ := pc_gens pc_facts
  refine orb_ok 11 22 (by norm_num) pc_facts pieceR_ok fun k hk => ?_
  rw [List.mem_range'_1] at hk
  have hm : orbSplitPr (pieceR MonSeven.invW) k (if k ≤ 17 then 4 else 1) ∈ e136301 := by
    refine List.mem_append_left _ ?_
    split
    · refine List.mem_append_left _ (List.mem_map.2 ⟨k, ?_, rfl⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · refine List.mem_append_right _ (List.mem_map.2 ⟨k, ?_, rfl⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
  exact orb_facts_of_split (pieceR_ok h7 hi7) h7 (by omega) (by split <;> omega) (f136301 _ hm)

end CertificateChecks.KernelKDenseP.MonSeven

end
