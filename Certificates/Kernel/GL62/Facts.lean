module

public import Certificates.Kernel.GL62.Glue
import Certificates.Kernel.GL62.Checks
import CFSG.Certificates.Kernel.GL62.Sound
import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group

namespace CFSG.KC.GL62.F36405

open CFSG.OddStandard.AltStdSmall4.GL62 CFSG.OddStandard.AltStdSmall4.GL62.Code CFSG.KD.GL62
open CFSG.KC.GL62 CFSG.KC.GL62.Checks

local notation "GG" => GL (Fin 6) (ZMod 2)
local notation "MM" => Matrix (Fin 6) (Fin 6) (ZMod 2)

noncomputable def uC (c c' : ℕ) : GG :=
  if h : Code.mul c c' = Code.one ∧ Code.mul c' c = Code.one then decodeGL c c' h else 1

theorem coe_uC {c c' : ℕ} (h : Code.mul c c' = Code.one ∧ Code.mul c' c = Code.one) :
    (uC c c' : MM) = mat c := by
  rw [uC, dif_pos h]
  rfl

theorem coe_uC_inv {c c' : ℕ} (h : Code.mul c c' = Code.one ∧ Code.mul c' c = Code.one) :
    (((uC c c')⁻¹ : GG) : MM) = mat c' := by
  rw [uC, dif_pos h]
  rfl

theorem units_eq {g h : GG} {x : ℕ} (hg : (g : MM) = mat x) (hh : (h : MM) = mat x) : g = h :=
  Units.ext (hg.trans hh.symm)

theorem mat_ZC : mat 38959071361 = (z₀ : MM) := by decide

section Checks

theorem hbK : bK BL BIL BP BIP BT = true := ch36405_b

theorem BL_length : BL.length = 336 := (bK_sound hbK).1

theorem BL_nodup : BL.Nodup := (bK_sound hbK).2.1.imp fun h => Nat.ne_of_lt h

theorem BL_lt {x : ℕ} (hx : x ∈ BL) : x < 2 ^ 36 := (bK_sound hbK).2.2.1 x hx

theorem BL_blk {x : ℕ} (hx : x ∈ BL) : blkK x = true := (bK_sound hbK).2.2.2.1 x hx

theorem BL_inv {k : ℕ} (hk : k < 336) : Code.mul (BL.getD k 0) (BIL.getD k 0) = Code.one ∧
    Code.mul (BIL.getD k 0) (BL.getD k 0) = Code.one :=
  (bK_sound hbK).2.2.2.2.2.2.2.2.1 k hk

theorem BL_tree {k : ℕ} (hk : k < 336) : letT BT k ≤ 2 ∧ ((depT BT k = 0 ∧ BL.getD k 0 = Code.one) ∨
    (depT BT k ≠ 0 ∧ parT BT k < 336 ∧ depT BT (parT BT k) + 1 = depT BT k ∧
      Code.mul (BL.getD (parT BT k) 0) (genK (letT BT k)) = BL.getD k 0)) :=
  (bK_sound hbK).2.2.2.2.2.2.2.2.2 k hk

theorem getD_eq' {α : Type} {L : List α} {d : α} {p : ℕ} (h : p < L.length) :
    L.getD p d = L[p] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_mem' {L : List ℕ} {k : ℕ} (hk : k < L.length) : L.getD k 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem _

theorem BL_getD_mem {k : ℕ} (hk : k < 336) : BL.getD k 0 ∈ BL :=
  getD_mem' (by rw [BL_length]; exact hk)

theorem hgood : goodK BP BIP GD = true := ch36405_good

end Checks

noncomputable def T3 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

noncomputable def P3 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

theorem mat_T3 : mat 34764505281 = dgMat !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by decide

theorem mat_P3 : mat 9131004162 = dgMat !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by decide

noncomputable def genU (l : ℕ) : GG := if l = 0 then z₀ else if l = 1 then dg T3 else dg P3

theorem genU_mem (l : ℕ) : genU l ∈ B₀ := by
  unfold genU
  split
  · exact z0_mem_B₀
  · split
    · exact dg_mem_B₀ _
    · exact dg_mem_B₀ _

theorem coe_genU {l : ℕ} (hl : l ≤ 2) : (genU l : MM) = mat (genK l) := by
  interval_cases l
  · exact mat_ZC.symm
  · exact (coe_dg T3).trans mat_T3.symm
  · exact (coe_dg P3).trans mat_P3.symm

noncomputable def bG (k : ℕ) : GG := uC (BL.getD k 0) (BIL.getD k 0)

theorem coe_bG {k : ℕ} (hk : k < 336) : (bG k : MM) = mat (BL.getD k 0) := coe_uC (BL_inv hk)

theorem coe_bG_inv {k : ℕ} (hk : k < 336) : (((bG k)⁻¹ : GG) : MM) = mat (BIL.getD k 0) :=
  coe_uC_inv (BL_inv hk)

theorem bG_mem_aux (d : ℕ) : ∀ k < 336, depT BT k = d → bG k ∈ B₀ := by
  induction d with
  | zero =>
    intro k hk hd
    rcases (BL_tree hk).2 with ⟨-, h1⟩ | ⟨h0, -⟩
    · have : bG k = 1 := Units.ext (by rw [coe_bG hk, h1, mat_one, Units.val_one])
      rw [this]
      exact B₀.one_mem
    · exact absurd hd h0
  | succ d ih =>
    intro k hk hd
    rcases (BL_tree hk).2 with ⟨h0, -⟩ | ⟨-, hp, hdp, hm⟩
    · omega
    · have hpk : bG k = bG (parT BT k) * genU (letT BT k) := Units.ext (by
        rw [coe_bG hk, Units.val_mul, coe_bG hp, coe_genU (BL_tree hk).1, ← mat_mul, hm])
      rw [hpk]
      exact B₀.mul_mem (ih _ hp (by omega)) (genU_mem _)

theorem bG_mem {k : ℕ} (hk : k < 336) : bG k ∈ B₀ := bG_mem_aux _ k hk rfl

theorem BL_getD_inj {k k' : ℕ} (hk : k < 336) (hk' : k' < 336)
    (h : BL.getD k 0 = BL.getD k' 0) : k = k' := by
  have hl : BL.length = 336 := BL_length
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at h
  exact (BL_nodup.getElem_inj_iff).1 h

theorem bG_inj {k k' : ℕ} (hk : k < 336) (hk' : k' < 336) (h : bG k = bG k') : k = k' := by
  have hm : mat (BL.getD k 0) = mat (BL.getD k' 0) := by rw [← coe_bG hk, ← coe_bG hk', h]
  exact BL_getD_inj hk hk' (eq_of_mat_eq (BL_lt (BL_getD_mem hk)) (BL_lt (BL_getD_mem hk')) hm)

theorem ncard_range_set (n : ℕ) : {k : ℕ | k < n}.ncard = n := by
  rw [show {k : ℕ | k < n} = ((Finset.range n : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, Finset.card_range]

theorem ncard_B₀ : (B₀ : Set GG).ncard = 336 := (Nat.card_coe_set_eq _).symm.trans card_B₀

theorem mem_B₀_iff {g : GG} : g ∈ B₀ ↔ ∃ k < 336, bG k = g := by
  have hsub : bG '' {k | k < 336} ⊆ (B₀ : Set GG) := by
    rintro _ ⟨k, hk, rfl⟩
    exact bG_mem hk
  have hcard : (bG '' {k | k < 336}).ncard = 336 := by
    have h := Set.InjOn.ncard_image (f := bG) (s := {k : ℕ | k < 336})
      fun a ha b hb h => bG_inj ha hb h
    rw [h, ncard_range_set]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_B₀, hcard]) (Set.toFinite _)
  constructor
  · intro hg
    have : g ∈ bG '' {k | k < 336} := heq ▸ hg
    obtain ⟨k, hk, rfl⟩ := this
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact bG_mem hk

noncomputable def iG (r : ℕ) : GG := uC r r

theorem coe_iG {r : ℕ} (h : Code.mul r r = Code.one) : (iG r : MM) = mat r := coe_uC ⟨h, h⟩

theorem coe_iG_inv {r : ℕ} (h : Code.mul r r = Code.one) : (((iG r)⁻¹ : GG) : MM) = mat r :=
  coe_uC_inv ⟨h, h⟩

theorem coe_conj {k r : ℕ} (hk : k < 336) {ρ : GG} (hρ : (ρ : MM) = mat r) :
    ((bG k * ρ * (bG k)⁻¹ : GG) : MM) = mat (conjB BL BIL k r) := by
  rw [Units.val_mul, Units.val_mul, coe_bG hk, hρ, coe_bG_inv hk, conjB, mat_mul, mat_mul]

theorem conjB_lt (k r : ℕ) : conjB BL BIL k r < 2 ^ 36 := mul_lt _ _

theorem ncard_stab {r : ℕ} (hr : r < 2 ^ 36) {ρ : GG} (hρ : (ρ : MM) = mat r) :
    {c | c ∈ B₀ ∧ c * ρ = ρ * c}.ncard = stabB BL BIL r := by
  have hset : {c | c ∈ B₀ ∧ c * ρ = ρ * c} = bG '' {k | k < 336 ∧ conjB BL BIL k r = r} := by
    ext c
    constructor
    · rintro ⟨hc, hcr⟩
      obtain ⟨k, hk, rfl⟩ := mem_B₀_iff.1 hc
      refine ⟨k, ⟨hk, ?_⟩, rfl⟩
      apply eq_of_mat_eq (conjB_lt _ _) hr
      rw [← coe_conj hk hρ, ← hρ, hcr, mul_inv_cancel_right]
    · rintro ⟨k, ⟨hk, hkr⟩, rfl⟩
      refine ⟨bG_mem hk, ?_⟩
      have h1 : bG k * ρ * (bG k)⁻¹ = ρ := Units.ext (by rw [coe_conj hk hρ, hkr, hρ])
      calc bG k * ρ = bG k * ρ * (bG k)⁻¹ * bG k := by group
        _ = ρ * bG k := by rw [h1]
  have hnd : ((List.range 336).filter fun k => conjB BL BIL k r = r).Nodup :=
    List.nodup_range.filter _
  rw [hset, Set.InjOn.ncard_image fun a ha b hb h => bG_inj ha.1 hb.1 h, stabB,
    show {k | k < 336 ∧ conjB BL BIL k r = r} =
      (((List.range 336).filter fun k => conjB BL BIL k r = r).toFinset : Set ℕ) by
      ext k
      simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem ncard_orb_code {r : ℕ} (hr : r < 2 ^ 36) {ρ : GG} (hρ : (ρ : MM) = mat r) :
    (orb ρ).ncard * stabB BL BIL r = 336 := by
  rw [← ncard_stab hr hρ]
  exact ncard_orb_mul ρ

theorem stabB_le (r : ℕ) : stabB BL BIL r ≤ 336 := by
  unfold stabB
  exact (List.length_filter_le _ _).trans (by simp)

theorem ncard_orb_div {r : ℕ} (hr : r < 2 ^ 36) {ρ : GG} (hρ : (ρ : MM) = mat r)
    (hs : 0 < stabB BL BIL r) : (orb ρ).ncard = 336 / stabB BL BIL r :=
  (Nat.div_eq_of_eq_mul_left hs (ncard_orb_code hr hρ).symm).symm

theorem ncard_eq_length {S : Set GG} {D : List ℕ} (hD : D.Nodup) (hlt : ∀ x ∈ D, x < 2 ^ 36)
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ D, (g : MM) = mat x) (hsurj : ∀ x ∈ D, ∃ g : GG, (g : MM) = mat x) :
    S.ncard = D.length := by
  have h1 : (fun g : GG => (g : MM)) '' S = mat '' {x | x ∈ D} := by
    ext M
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, hgx⟩ := (hS g).1 hg
      exact ⟨x, hx, hgx.symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g, hg⟩ := hsurj x hx
      exact ⟨g, (hS g).2 ⟨x, hx, hg⟩, hg⟩
  have h2 := Set.ncard_image_of_injective S
    (show Function.Injective fun g : GG => (g : MM) from fun _ _ h => Units.ext h)
  have h3 : (mat '' {x | x ∈ D}).ncard = {x | x ∈ D}.ncard :=
    Set.InjOn.ncard_image fun a ha b hb h => eq_of_mat_eq (hlt a ha) (hlt b hb) h
  have h4 : {x | x ∈ D}.ncard = D.length := by
    rw [show {x | x ∈ D} = (D.toFinset : Set ℕ) by ext; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hD]
  rw [← h2, h1, h3, h4]

theorem orb_eq_of_mem {y d : GG} (hd : d ∈ orb y) : orb d = orb y := by
  obtain ⟨c, hc, rfl⟩ := hd
  ext e
  constructor
  · rintro ⟨c', hc', rfl⟩
    exact ⟨c' * c, B₀.mul_mem hc' hc, by group⟩
  · rintro ⟨c', hc', rfl⟩
    exact ⟨c' * c⁻¹, B₀.mul_mem hc' (B₀.inv_mem hc), by group⟩

theorem self_mem_orb (y : GG) : y ∈ orb y := ⟨1, B₀.one_mem, by group⟩

theorem head_le {L : List ℕ} (hL : L.Pairwise (· < ·)) {x : ℕ} (hx : x ∈ L) : L.getD 0 0 ≤ x := by
  cases L with
  | nil => simp at hx
  | cons a t =>
    rw [List.getD_cons_zero]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.1 hL).1 x hx)

theorem good_facts : GD.length = 17 ∧ rep GD 0 = 38959071361 ∧
    (GD.map fun e => e.2.getD 0 0).Nodup ∧
    ∀ p < 17, rep GD p < 2 ^ 36 ∧ Code.mul (rep GD p) (rep GD p) = Code.one ∧
      0 < stabB BL BIL (rep GD p) ∧ (orbL GD p).Pairwise (· < ·) ∧
      (orbL GD p).length = 336 / stabB BL BIL (rep GD p) ∧
      ∀ x ∈ orbL GD p, ∃ k < 336, conjB BL BIL k (rep GD p) = x :=
  goodK_sound hgood hbK

noncomputable def rG (p : ℕ) : GG := iG (rep GD p)

theorem coe_rG {p : ℕ} (hp : p < 17) : (rG p : MM) = mat (rep GD p) :=
  coe_iG ((good_facts.2.2.2 p hp).2.1)

theorem coe_rG_inv {p : ℕ} (hp : p < 17) : (((rG p)⁻¹ : GG) : MM) = mat (rep GD p) :=
  coe_iG_inv ((good_facts.2.2.2 p hp).2.1)

theorem orbL_lt {p : ℕ} (hp : p < 17) {x : ℕ} (hx : x ∈ orbL GD p) : x < 2 ^ 36 := by
  obtain ⟨k, -, rfl⟩ := (good_facts.2.2.2 p hp).2.2.2.2.2 x hx
  exact conjB_lt _ _

theorem orb_good {p : ℕ} (hp : p < 17) :
    orb (rG p) = {g : GG | ∃ x ∈ orbL GD p, (g : MM) = mat x} := by
  obtain ⟨hlt, -, hs, hsort, hlen, hconj⟩ := good_facts.2.2.2 p hp
  have hsurj : ∀ x ∈ orbL GD p, ∃ k < 336, bG k * rG p * (bG k)⁻¹ ∈ orb (rG p) ∧
      ((bG k * rG p * (bG k)⁻¹ : GG) : MM) = mat x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hconj x hx
    exact ⟨k, hk, ⟨bG k, bG_mem hk, rfl⟩, coe_conj hk (coe_rG hp)⟩
  have hsub : {g : GG | ∃ x ∈ orbL GD p, (g : MM) = mat x} ⊆ orb (rG p) := by
    rintro g ⟨x, hx, hgx⟩
    obtain ⟨k, -, hmem, hm⟩ := hsurj x hx
    rw [units_eq hgx hm]
    exact hmem
  have hT : {g : GG | ∃ x ∈ orbL GD p, (g : MM) = mat x}.ncard = (orbL GD p).length :=
    ncard_eq_length (hsort.imp fun h => Nat.ne_of_lt h) (fun x hx => orbL_lt hp hx)
      (fun g => Iff.rfl) fun x hx => by
        obtain ⟨k, -, -, hm⟩ := hsurj x hx
        exact ⟨_, hm⟩
  exact (Set.eq_of_subset_of_ncard_le hsub
    (by rw [hT, hlen, ncard_orb_div hlt (coe_rG hp) hs]) (Set.toFinite _)).symm

theorem size_good {p : ℕ} (hp : p < 17) : (orb (rG p)).ncard = (orbL GD p).length := by
  obtain ⟨hlt, -, hs, -, hlen, -⟩ := good_facts.2.2.2 p hp
  rw [ncard_orb_div hlt (coe_rG hp) hs, hlen]

theorem orbL_ne_nil {p : ℕ} (hp : p < 17) : (orbL GD p) ≠ [] := by
  obtain ⟨-, -, hs, -, hlen, -⟩ := good_facts.2.2.2 p hp
  intro h
  rw [h, List.length_nil] at hlen
  have := stabB_le (rep GD p)
  have h336 : 1 ≤ 336 / stabB BL BIL (rep GD p) := (Nat.le_div_iff_mul_le hs).2 (by omega)
  omega

theorem head_mem {p : ℕ} (hp : p < 17) : (orbL GD p).getD 0 0 ∈ orbL GD p :=
  getD_mem' (List.length_pos_iff.2 (orbL_ne_nil hp))

theorem head_mem_of_orb {p q : ℕ} (hp : p < 17) (hq : q < 17) (h : orb (rG p) = orb (rG q)) :
    (orbL GD q).getD 0 0 ≤ (orbL GD p).getD 0 0 := by
  have hm := head_mem hp
  obtain ⟨g, hg⟩ : ∃ g : GG, g ∈ orb (rG p) ∧ (g : MM) = mat ((orbL GD p).getD 0 0) := by
    obtain ⟨k, hk, hkx⟩ := (good_facts.2.2.2 p hp).2.2.2.2.2 _ hm
    exact ⟨_, ⟨bG k, bG_mem hk, rfl⟩, (coe_conj hk (coe_rG hp)).trans (by rw [hkx])⟩
  rw [h, orb_good hq] at hg
  obtain ⟨x, hx, hgx⟩ := hg.1
  have : (orbL GD p).getD 0 0 = x :=
    eq_of_mat_eq (orbL_lt hp hm) (orbL_lt hq hx) (hg.2.symm.trans hgx)
  rw [this]
  exact head_le (good_facts.2.2.2 q hq).2.2.2.1 hx

theorem good_disj {p q : ℕ} (hp : p < 17) (hq : q < 17) (hpq : p ≠ q) :
    Disjoint (orb (rG p)) (orb (rG q)) := by
  refine Set.disjoint_left.2 fun g hgp hgq => hpq ?_
  have h1 : orb (rG p) = orb (rG q) := (orb_eq_of_mem hgp).symm.trans (orb_eq_of_mem hgq)
  have he : (orbL GD p).getD 0 0 = (orbL GD q).getD 0 0 :=
    le_antisymm (head_mem_of_orb hq hp h1.symm) (head_mem_of_orb hp hq h1)
  have hl := good_facts.1
  have hn := good_facts.2.2.1
  have hp' : p < (GD.map fun e => e.2.getD 0 0).length := by simp [hl, hp]
  have hq' : q < (GD.map fun e => e.2.getD 0 0).length := by simp [hl, hq]
  refine (hn.getElem_inj_iff (i := p) (j := q) (hi := hp') (hj := hq')).1 ?_
  simp only [List.getElem_map]
  unfold orbL at he
  rw [getD_eq' (L := GD) (d := (0, [])) (by omega : p < GD.length),
    getD_eq' (L := GD) (d := (0, [])) (by omega : q < GD.length)] at he
  exact he

theorem exists_of_orbL {b : ℕ} (hb : b < 17) {x : ℕ} (hx : x ∈ orbL GD b) :
    ∃ g ∈ orb (rG b), (g : MM) = mat x := by
  have h : {g : GG | ∃ x ∈ orbL GD b, (g : MM) = mat x} = orb (rG b) := (orb_good hb).symm
  obtain ⟨k, hk, hkx⟩ := (good_facts.2.2.2 b hb).2.2.2.2.2 x hx
  refine ⟨bG k * rG b * (bG k)⁻¹, ⟨bG k, bG_mem hk, rfl⟩, ?_⟩
  rw [coe_conj hk (coe_rG hb), hkx]

theorem wordV_lt (g : ℕ) (w : List ℕ) : wordV BL g w < 2 ^ 36 := by
  have h : ∀ acc, acc < 2 ^ 36 →
      w.foldl (fun acc a => Code.mul acc (letterV BL g a)) acc < 2 ^ 36 := by
    induction w with
    | nil => exact fun acc h => h
    | cons a w ih => exact fun acc _ => ih _ (mul_lt _ _)
  exact h Code.one one_lt

theorem word_mem {y : GG} {yc : ℕ} (hy : (y : MM) = mat yc) {w : List ℕ}
    (hw : ∀ a ∈ w, a ≤ 336) :
    ∃ e ∈ Subgroup.closure (insert y (B₀ : Set GG)), (e : MM) = mat (wordV BL yc w) := by
  set K := Subgroup.closure (insert y (B₀ : Set GG))
  have hlet : ∀ a, a ≤ 336 → ∃ l ∈ K, (l : MM) = mat (letterV BL yc a) := by
    intro a ha
    unfold letterV
    split
    · exact ⟨y, Subgroup.subset_closure (Set.mem_insert _ _), hy⟩
    · exact ⟨bG (a - 1), Subgroup.subset_closure (Set.mem_insert_of_mem _ (bG_mem (by omega))),
        coe_bG (by omega)⟩
  have h : ∀ acc (g : GG), g ∈ K → (g : MM) = mat acc →
      ∃ e ∈ K, (e : MM) = mat (w.foldl (fun acc a => Code.mul acc (letterV BL yc a)) acc) := by
    induction w with
    | nil => exact fun acc g hg hga => ⟨g, hg, hga⟩
    | cons a w ih =>
      intro acc g hg hga
      obtain ⟨l, hl, hlm⟩ := hlet a (hw a List.mem_cons_self)
      exact ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)) _ (g * l) (K.mul_mem hg hl)
        (by rw [Units.val_mul, hga, hlm, mat_mul])
  exact h Code.one 1 K.one_mem (by rw [Units.val_one, mat_one])

theorem bad_of {y : GG} {yc : ℕ} (hy : (y : MM) = mat yc) {w : List ℕ} (h : BadW BL yc w) :
    Bad y := by
  obtain ⟨hw, hz, hblk⟩ := h
  obtain ⟨e, he, hem⟩ := word_mem hy hw
  refine ⟨e, he, Units.ext ?_, fun heB => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hem, ← mat_ZC, ← mat_mul, ← mat_mul, hz]
  · obtain ⟨k, hk, rfl⟩ := mem_B₀_iff.1 heB
    have : BL.getD k 0 = wordV BL yc w :=
      eq_of_mat_eq (BL_lt (BL_getD_mem hk)) (wordV_lt _ _) (by rw [← coe_bG hk, hem])
    rw [← this, BL_blk (BL_getD_mem hk)] at hblk
    exact Bool.noConfusion hblk

theorem comm_good {a b : ℕ} (ha : a < 17) (hb : b < 17) :
    {x | x ∈ orb (rG b) ∧ x * rG a = rG a * x}.ncard = tab C a b := by
  have hl := good_facts.1
  rw [commK_sound ch36405_comm hgood hbK a (by omega) b (by omega)]
  have hra := coe_rG ha
  have hcomm : ∀ (g : GG) (x : ℕ), (g : MM) = mat x →
      (g * rG a = rG a * g ↔ Code.mul x (rep GD a) = Code.mul (rep GD a) x) := by
    intro g x hgx
    constructor
    · intro h
      exact eq_of_mat_eq (mul_lt _ _) (mul_lt _ _) (by
        rw [mat_mul, mat_mul, ← hgx, ← hra, ← Units.val_mul, ← Units.val_mul, h])
    · intro h
      exact Units.ext (by rw [Units.val_mul, Units.val_mul, hgx, hra, ← mat_mul, ← mat_mul, h])
  refine ncard_eq_length (((good_facts.2.2.2 b hb).2.2.2.1.imp fun h => Nat.ne_of_lt h).filter _)
    (fun x hx => orbL_lt hb (List.mem_of_mem_filter hx)) ?_ ?_
  · intro g
    rw [orb_good hb]
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨x, hx, hgx⟩, hgr⟩
      exact ⟨x, ⟨hx, (hcomm g x hgx).1 hgr⟩, hgx⟩
    · rintro ⟨x, ⟨hx, hxr⟩, hgx⟩
      exact ⟨⟨x, hx, hgx⟩, (hcomm g x hgx).2 hxr⟩
  · intro x hx
    obtain ⟨g, -, hg⟩ := exists_of_orbL hb (List.mem_of_mem_filter hx)
    exact ⟨g, hg⟩

theorem hits : ∀ a < 17, ∀ b < 17,
    (tab H a b = 2 ^ 17 → ∃ e ∈ HB, e.1 = a ∧ e.2.1 = b) ∧
    (tab H a b ≠ 2 ^ 17 →
      (∀ x ∈ orbL GD b, ∃ n < 17, (tab H a b).testBit n = true ∧ ∃ k < 336,
        Code.mul (BL.getD k 0) (rep GD n) =
          Code.mul (Code.mul (Code.mul (rep GD a) x) (rep GD a)) (BL.getD k 0)) ∧
      ∀ n, (tab H a b).testBit n = true → n < 17 ∧ ∃ x ∈ orbL GD b, ∃ k < 336,
        Code.mul (BL.getD k 0) (rep GD n) =
          Code.mul (Code.mul (Code.mul (rep GD a) x) (rep GD a)) (BL.getD k 0)) :=
  hitK_sound hbK hgood fun a ha => by
    interval_cases a
    exacts [ch36405_hit0, ch36405_hit1, ch36405_hit2, ch36405_hit3, ch36405_hit4, ch36405_hit5,
      ch36405_hit6, ch36405_hit7, ch36405_hit8, ch36405_hit9, ch36405_hit10, ch36405_hit11,
      ch36405_hit12, ch36405_hit13, ch36405_hit14, ch36405_hit15, ch36405_hit16]

theorem coe_hit {a : ℕ} (ha : a < 17) {g : GG} {x : ℕ} (hg : (g : MM) = mat x) :
    ((rG a * g * (rG a)⁻¹ : GG) : MM) = mat (Code.mul (Code.mul (rep GD a) x) (rep GD a)) := by
  rw [Units.val_mul, Units.val_mul, coe_rG ha, hg, coe_rG_inv ha, mat_mul, mat_mul]

theorem hit_good {a b : ℕ} (ha : a < 17) (hb : b < 17) (n : ℕ) (hn : (tab H a b).testBit n) :
    (n < 17 ∧ ∃ x ∈ orb (rG b), rG a * x * (rG a)⁻¹ ∈ orb (rG n)) ∨
      (n = 17 ∧ ∃ x ∈ orb (rG b), Bad (rG a * x * (rG a)⁻¹)) := by
  by_cases hH : tab H a b = 2 ^ 17
  · right
    rw [hH, Nat.testBit_two_pow, decide_eq_true_eq] at hn
    refine ⟨hn.symm, ?_⟩
    obtain ⟨e, he, rfl, rfl⟩ := (hits a ha b hb).1 hH
    obtain ⟨-, -, hx, hbad⟩ := hbK_sound ch36405_hb hbK e he
    obtain ⟨g, hg, hgx⟩ := exists_of_orbL hb hx
    exact ⟨g, hg, bad_of (coe_hit ha hgx) hbad⟩
  · left
    obtain ⟨hn17, x, hx, k, hk, hkm⟩ := ((hits a ha b hb).2 hH).2 n hn
    obtain ⟨g, hg, hgx⟩ := exists_of_orbL hb hx
    refine ⟨hn17, g, hg, bG k, bG_mem hk, ?_⟩
    have h1 : bG k * rG n = rG a * g * (rG a)⁻¹ * bG k := Units.ext (by
      rw [Units.val_mul (bG k), Units.val_mul _ (bG k), coe_bG hk, coe_rG hn17, coe_hit ha hgx,
        ← mat_mul, ← mat_mul, hkm])
    rw [h1]
    group

theorem ncard_union_pw {α : Type} (T : α → Set GG) (L : List α)
    (hL : L.Pairwise fun x y => Disjoint (T x) (T y)) :
    {g | ∃ x ∈ L, g ∈ T x}.ncard = (L.map fun x => (T x).ncard).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hset : {g | ∃ x ∈ a :: L, g ∈ T x} = T a ∪ {g | ∃ x ∈ L, g ∈ T x} := by
      ext g
      simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨x, rfl | hx, hg⟩
        · exact Or.inl hg
        · exact Or.inr ⟨x, hx, hg⟩
      · rintro (hg | ⟨x, hx, hg⟩)
        · exact ⟨a, Or.inl rfl, hg⟩
        · exact ⟨x, Or.inr hx, hg⟩
    have hdis : Disjoint (T a) {g | ∃ x ∈ L, g ∈ T x} := by
      refine Set.disjoint_left.2 fun g hg ⟨x, hx, hgx⟩ => ?_
      exact Set.disjoint_left.1 ((List.pairwise_cons.1 hL).1 x hx) hg hgx
    rw [hset, Set.ncard_union_eq hdis, ih (List.pairwise_cons.1 hL).2, List.map_cons,
      List.sum_cons]

@[irreducible] noncomputable def RL : List (ℕ × ℕ × ℕ × ℕ × List ℕ) := RC.flatten

theorem RL_eq : RL = RC.flatten := by
  unfold RL
  rfl

theorem rc_facts : ∀ x ∈ RL, x.1 < 2 ^ 36 ∧ Code.mul x.1 x.1 = Code.one ∧
    (∀ k < 336, x.1 ≤ conjB BL BIL k x.1) ∧ x.2.1 = stabB BL BIL x.1 ∧ 0 < x.2.1 ∧
    x.2.1 ∣ 336 ∧ Code.mul (Code.mul x.2.2.1 38959071361) x.2.2.2.1 = x.1 ∧
    Code.mul x.2.2.1 x.2.2.2.1 = Code.one ∧ Code.mul x.2.2.2.1 x.2.2.1 = Code.one ∧
    (x.1 ∉ GD.map (fun e => e.2.getD 0 0) → BadW BL x.1 x.2.2.2.2) := by
  rw [RL_eq]
  exact rc_sound hbK ch36405_rcLen fun j hj => by
    interval_cases j
    exacts [ch36405_rc0, ch36405_rc1, ch36405_rc2, ch36405_rc3, ch36405_rc4, ch36405_rc5,
      ch36405_rc6, ch36405_rc7, ch36405_rc8, ch36405_rc9, ch36405_rc10, ch36405_rc11, ch36405_rc12]

theorem ord_facts : (RL.map Prod.fst).Pairwise (· < ·) ∧ RL.length = 827 ∧
    (RL.map fun x => 336 / x.2.1).sum = 234360 := by
  rw [RL_eq]
  exact ordK_sound ch36405_ord

def clsG : Set GG := {y | ∃ g : GG, y = g * z₀ * g⁻¹}

theorem orb_min_sub {x : ℕ × ℕ × ℕ × ℕ × List ℕ} (hx : x ∈ RL) : orb (iG x.1) ⊆ clsG := by
  obtain ⟨-, hinv, -, -, -, -, hg, hgg, hgg', -⟩ := rc_facts x hx
  set g := uC x.2.2.1 x.2.2.2.1
  have hρ : iG x.1 = g * z₀ * g⁻¹ := Units.ext (by
    rw [coe_iG hinv, Units.val_mul, Units.val_mul, coe_uC ⟨hgg, hgg'⟩, coe_uC_inv ⟨hgg, hgg'⟩,
      ← mat_ZC, ← mat_mul, ← mat_mul, hg])
  rintro _ ⟨c, -, rfl⟩
  exact ⟨c * g, by rw [hρ]; group⟩

theorem orb_min_ncard {x : ℕ × ℕ × ℕ × ℕ × List ℕ} (hx : x ∈ RL) :
    (orb (iG x.1)).ncard = 336 / x.2.1 := by
  obtain ⟨hlt, hinv, -, hs, hs0, -⟩ := rc_facts x hx
  rw [hs] at hs0 ⊢
  exact ncard_orb_div hlt (coe_iG hinv) hs0

theorem min_le_of_mem {x y : ℕ × ℕ × ℕ × ℕ × List ℕ} (hx : x ∈ RL) (hy : y ∈ RL)
    (h : iG y.1 ∈ orb (iG x.1)) : x.1 ≤ y.1 := by
  obtain ⟨hlt, hinv, hmin, -⟩ := rc_facts x hx
  obtain ⟨hlt', hinv', -⟩ := rc_facts y hy
  obtain ⟨c, hc, hce⟩ := h
  obtain ⟨k, hk, rfl⟩ := mem_B₀_iff.1 hc
  have : y.1 = conjB BL BIL k x.1 :=
    eq_of_mat_eq hlt' (conjB_lt _ _) (by rw [← coe_iG hinv', hce, coe_conj hk (coe_iG hinv)])
  rw [this]
  exact hmin k hk

theorem orb_min_disj {x y : ℕ × ℕ × ℕ × ℕ × List ℕ} (hx : x ∈ RL) (hy : y ∈ RL)
    (hxy : x.1 < y.1) : Disjoint (orb (iG x.1)) (orb (iG y.1)) := by
  refine Set.disjoint_left.2 fun g hgx hgy => ?_
  have h1 : orb (iG x.1) = orb (iG y.1) := (orb_eq_of_mem hgx).symm.trans (orb_eq_of_mem hgy)
  have h2 : iG y.1 ∈ orb (iG x.1) := by
    rw [h1]
    exact self_mem_orb _
  have h3 : iG x.1 ∈ orb (iG y.1) := by
    rw [← h1]
    exact self_mem_orb _
  exact absurd (le_antisymm (min_le_of_mem hx hy h2) (min_le_of_mem hy hx h3)) (Nat.ne_of_lt hxy)

noncomputable def Tm (x : ℕ × ℕ × ℕ × ℕ × List ℕ) : Set GG := orb (iG x.1)

theorem cover_min (g : GG) : ∃ x ∈ RL, g * z₀ * g⁻¹ ∈ orb (iG x.1) := by
  obtain ⟨hpw, -, hsum⟩ := ord_facts
  have h0 : RL.Pairwise fun x y => x.1 < y.1 := List.pairwise_map.1 hpw
  have hpw' : RL.Pairwise fun x y => Disjoint (Tm x) (Tm y) :=
    List.Pairwise.imp_of_mem (fun {a b} ha hb hab => orb_min_disj ha hb hab) h0
  have hU := ncard_union_pw Tm RL hpw'
  have hsum' : (RL.map fun x => (Tm x).ncard).sum = 234360 := by
    rw [← hsum]
    congr 1
    exact List.map_congr_left fun x hx => orb_min_ncard hx
  have hsub : {g | ∃ x ∈ RL, g ∈ Tm x} ⊆ clsG := by
    rintro y ⟨x, hx, hy⟩
    exact orb_min_sub hx hy
  have hcls : clsG.ncard = 234360 := ncard_conj_z0
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcls, hU, hsum']) (Set.toFinite _)
  have : g * z₀ * g⁻¹ ∈ clsG := ⟨g, rfl⟩
  rw [← heq] at this
  exact this

theorem cover_facts (g : GG) : ∃ y, (Bad y ∨ ∃ p < 17, y = rG p) ∧ g * z₀ * g⁻¹ ∈ orb y := by
  obtain ⟨x, hx, hg⟩ := cover_min g
  obtain ⟨hlt, hinv, -, -, -, -, -, -, -, hbad⟩ := rc_facts x hx
  by_cases hh : x.1 ∈ GD.map (fun e => e.2.getD 0 0)
  · obtain ⟨e, he, hex⟩ := List.mem_map.1 hh
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 he
    have hl := good_facts.1
    have hp17 : p < 17 := by omega
    have hO : orbL GD p = GD[p].2 := by
      unfold orbL
      rw [getD_eq' hp]
      rfl
    have hmem : x.1 ∈ orbL GD p := by
      have h := head_mem hp17
      rw [hO] at h ⊢
      rw [← hex]
      exact h
    have hρ : iG x.1 ∈ orb (rG p) := by
      rw [orb_good hp17]
      exact ⟨x.1, hmem, coe_iG hinv⟩
    exact ⟨rG p, Or.inr ⟨p, hp17, rfl⟩, orb_eq_of_mem hρ ▸ hg⟩
  · exact ⟨iG x.1, Or.inl (bad_of (coe_iG hinv) (hbad hh)), hg⟩

def fams : List (ℕ × ℕ × ℕ) := [(9, 3, 3), (127, 360, 4), (16383, 1080, 7), (114691, 168, 14)]

theorem famSizes_eq : (1, 1) :: fams.map (fun f => (f.1, f.2.1)) = famSizesK := rfl

theorem elim_facts : ∀ m < 2 ^ 17, m.testBit 0 →
    (∀ a ∈ memL m, ∀ b ∈ memL m, tab H a b &&& m = tab H a b) →
    (∀ a ∈ memL m, ((memL m).map (tab C a)).sum = ((memL m).map (tab C 0)).sum) →
    (m, ((memL m).map fun b => (orbL GD b).length).sum) ∈
      (1, 1) :: fams.map fun f => (f.1, f.2.1) := by
  intro m hm h0 hcl hhom
  rw [famSizes_eq]
  have hmem : ∀ a, a < 17 → m.testBit a = true → a ∈ memL m := fun a ha hb => by
    simp [memL, ha, hb]
  exact elimK_sound ch36405_elim hgood hbK hm h0
    (fun a ha b hb hta htb => hcl a (hmem a ha hta) b (hmem b hb htb))
    (fun a ha hta => hhom a (hmem a ha hta))

theorem F_heads : F.map (fun e => (e.1, e.2.1, e.2.2.1)) =
    fams.map (fun f => (f.1, f.2.2, rep GD f.2.2)) := by decide

theorem fam_facts : ∀ f ∈ fams, f.2.2 < 17 ∧ f.1.testBit f.2.2 ∧ ∀ b < 17, f.1.testBit b →
    ∃ e ∈ B₀ ⊔ Subgroup.zpowers (rG f.2.2), rG b = e * z₀ * e⁻¹ := by
  intro f hf
  have : (f.1, f.2.2, rep GD f.2.2) ∈ F.map (fun e => (e.1, e.2.1, e.2.2.1)) := by
    rw [F_heads]
    exact List.mem_map_of_mem hf
  obtain ⟨e, he, hef⟩ := List.mem_map.1 this
  simp only [Prod.mk.injEq] at hef
  obtain ⟨h1, h2, h3⟩ := hef
  obtain ⟨hq, hqm, -, hw⟩ := famK_sound ch36405_fam hbK e he
  rw [h2] at hq
  refine ⟨hq, by rw [← h1, ← h2]; exact hqm, fun b hb hbm => ?_⟩
  obtain ⟨-, w, hwl, hwe⟩ := hw b (by rw [h1]; exact hbm)
  rw [h3] at hwe
  obtain ⟨g, hg, hgm⟩ := word_mem (coe_rG hq) hwl
  have hle : Subgroup.closure (insert (rG f.2.2) (B₀ : Set GG)) ≤ B₀ ⊔ Subgroup.zpowers (rG f.2.2) :=
    (Subgroup.closure_le _).2 (Set.insert_subset (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      fun x hx => Subgroup.mem_sup_left hx)
  refine ⟨g, hle hg, ?_⟩
  have hgz : g * z₀ = rG b * g := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hgm, ← mat_ZC, coe_rG hb, ← mat_mul, ← mat_mul, hwe])
  rw [hgz, mul_inv_cancel_right]

theorem rep_codes : rep GD 0 = 38959071361 ∧ rep GD 3 = 4328915976 ∧ rep GD 4 = 1796246880 ∧
    rep GD 7 = 1343259808 ∧ rep GD 14 = 9977598093 := by decide

theorem rG_eq {p c : ℕ} (hp : p < 17) (hc : rep GD p = c) {y : GG} (hy : (y : MM) = mat c) :
    rG p = y := units_eq (by rw [coe_rG hp, hc]) hy

theorem fam_gen_facts : ∀ f ∈ fams, (rG f.2.2 = gN ∧ f.2.1 = 3) ∨ (rG f.2.2 = gW ∧ f.2.1 = 168) ∨
    (rG f.2.2 = gS ∧ f.2.1 = 360) ∨ (rG f.2.2 = gG ∧ f.2.1 = 1080) := by
  intro f hf
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rG_eq (by norm_num) rep_codes.2.1 mat_gN.symm, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rG_eq (by norm_num) rep_codes.2.2.1 mat_gS.symm, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rG_eq (by norm_num) rep_codes.2.2.2.1 mat_gG.symm, rfl⟩))
  · exact Or.inr (Or.inl ⟨rG_eq (by norm_num) rep_codes.2.2.2.2 mat_gW.symm, rfl⟩)

theorem facts : GL62Facts rG (fun p => (orbL GD p).length) (tab C) (tab H) fams where
  rep_zero := rG_eq (by norm_num) rep_codes.1 mat_ZC.symm
  cover := cover_facts
  size := fun p hp => size_good hp
  disj := fun p hp q hq hpq => good_disj hp hq hpq
  comm := fun a ha b hb => comm_good ha hb
  hit := fun a ha b hb n hn => hit_good ha hb n hn
  elim := elim_facts
  fam := fam_facts
  fam_gen := fam_gen_facts

end CFSG.KC.GL62.F36405

public section

namespace CFSG.KC.GL62

theorem facts36405 : ∃ (rep : ℕ → GL (Fin 6) (ZMod 2)) (S : ℕ → ℕ) (C H : ℕ → ℕ → ℕ)
    (fams : List (ℕ × ℕ × ℕ)), GL62Facts rep S C H fams :=
  ⟨_, _, _, _, _, F36405.facts⟩

end CFSG.KC.GL62

end
