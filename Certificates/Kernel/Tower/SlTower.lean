module

public import Certificates.Kernel.Tower.L2SlGlue
public import Certificates.Kernel.Tower.SlDpChecks
public import Certificates.Kernel.Tower.T2Checks
public import Certificates.Kernel.Tower.SGlue
public import CFSG.Certificates.Kernel.Tower.T2SqSound

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower Subgroup

variable {X Y : Type*} [Group X] [Group Y]

theorem nbeq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [h]
  exact Nat.beq_refl b

theorem isModel_map {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}
    (M : IsModel (⊤ : Subgroup X) n mul dec) (e : X →* Y) (he : Function.Bijective e) :
    IsModel (⊤ : Subgroup Y) n mul (fun c => e (dec c)) where
  mem _ _ := mem_top _
  inj a ha b hb h := M.inj a ha b hb (he.1 h)
  surj y _ := by
    obtain ⟨x, rfl⟩ := he.2 y
    obtain ⟨c, hc, rfl⟩ := M.surj x (mem_top x)
    exact ⟨c, hc, rfl⟩
  mul_lt := M.mul_lt
  dec_mul a ha b hb := by rw [M.dec_mul a ha b hb, map_mul]
  zero_lt := M.zero_lt
  dec_zero := by rw [M.dec_zero, map_one]

namespace CycExt

variable {D : ExtData X}

theorem d_mul (a b : CycExt D) : (a * b).d = xor a.d b.d := rfl

theorem d_inv (a : CycExt D) : a⁻¹.d = a.d := by
  obtain ⟨k, d⟩ := a
  cases d <;> rfl

theorem mem_range_incl (a : CycExt D) : a ∈ (CycExt.incl D).range ↔ a.d = false := by
  constructor
  · rintro ⟨k, rfl⟩
    rfl
  · intro h
    obtain ⟨k, d⟩ := a
    change d = false at h
    subst h
    exact ⟨k, rfl⟩

theorem incl_injective : Function.Injective (CycExt.incl D) := fun a b h =>
  congrArg CycExt.k h

end CycExt

theorem slRec_get {a : Nat} (ha : a < 32) :
    recB 8192 4 (wm slSM slAC) slPT (imA slIM a) (slA (Nat.add a 2)) = true := by
  have hk : slRec (a / 8) = true := by
    have h4 : a / 8 < 4 := by omega
    interval_cases h : a / 8
    · exact ch36409_rec0
    · exact ch36409_rec1
    · exact ch36409_rec2
    · exact ch36409_rec3
  have h := allB_eq_true.1 hk (a % 8) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 8 (a / 8)) (a % 8) = a := Nat.div_add_mod a 8
  rw [e] at h
  exact h

theorem l2_sl (D : ExtData (Grp slS)) (hα : D.α (subModel_sl.decW 64) = subModel_sl.decW 64)
    (hg : D.g * subModel_sl.decW 64 = subModel_sl.decW 64 * D.g)
    (hP : PInv (centralizer {CycExt.incl D (subModel_sl.decW 64)} : Subgroup (CycExt D))) :
    L2Facts (CycExt D) (CycExt.incl D (subModel_sl.decW 64)) := by
  set t := subModel_sl.decW 64 with ht_def
  obtain ⟨h, hh, a, ha, himg⟩ := search_sl D.α hα
  set c : CycExt D := ⟨h, true⟩ with hc_def
  have hcN : c ∈ normalizer ((CycExt.incl D).range : Set (CycExt D)) := by
    rw [mem_normalizer_iff]
    intro x
    change x ∈ (CycExt.incl D).range ↔ c * x * c⁻¹ ∈ (CycExt.incl D).range
    rw [CycExt.mem_range_incl, CycExt.mem_range_incl, CycExt.d_mul, CycExt.d_mul, CycExt.d_inv,
      hc_def]
    obtain ⟨k, d⟩ := x
    cases d <;> exact Iff.rfl
  have hc2 : c ^ 2 ∈ (CycExt.incl D).range := by
    rw [CycExt.mem_range_incl, sq, CycExt.d_mul]
    rfl
  have hcK : c ∉ (CycExt.incl D).range := by
    intro hm
    rw [CycExt.mem_range_incl, hc_def] at hm
    exact Bool.noConfusion hm
  set E := ExtData.ofConj CycExt.incl_injective hcN hc2 with hE_def
  have hEα : ∀ x, E.α x = h * D.α x * h⁻¹ := fun x => CycExt.incl_injective (by
    rw [map_ofConj_α]
    change (⟨h, true⟩ * ⟨x, false⟩ * (⟨h, true⟩ : CycExt D)⁻¹ : CycExt D) = ⟨h * D.α x * h⁻¹, false⟩
    rw [CycExt.inv_mk_true, CycExt.mk_mul_mk, CycExt.mk_mul_mk]
    simp only [CycExt.pw, CycExt.sq, ite_true, Bool.and_false, Bool.and_true, Bool.false_eq_true,
      ite_false, Bool.xor_false, Bool.xor_true, Bool.not_true, mul_one, map_mul, map_inv, D.hαg,
      D.hα2, CycExt.mk.injEq, and_true]
    group)
  have hEg : E.g = h * D.α h * D.g := CycExt.incl_injective (by
    rw [map_ofConj_g, sq]
    change (⟨h, true⟩ * (⟨h, true⟩ : CycExt D) : CycExt D) = ⟨h * D.α h * D.g, false⟩
    rw [CycExt.mk_mul_mk]
    simp [CycExt.pw, CycExt.sq])
  have hFA := recB_sound sl_model ch36409_tree (slRec_get ha) E.α.toMonoidHom (fun i hi => by
    change E.α _ = _
    rw [hEα]
    exact himg i hi)
  set gc := sl_model.code E.g with hgc_def
  have hgc : gc < 8192 := sl_model.code_lt (mem_top _)
  have hdg : subModel_sl.decW gc = E.g := sl_model.dec_code (mem_top _)
  have hgt : E.g * t = t * E.g := by
    have h1 : D.α h * t = t * D.α h := by
      rw [← hα, ← map_mul, ← map_mul, hh]
    rw [hEg]
    calc h * D.α h * D.g * t = h * D.α h * (D.g * t) := by group
      _ = h * D.α h * (t * D.g) := by rw [hg]
      _ = h * (D.α h * t) * D.g := by group
      _ = h * (t * D.α h) * D.g := by rw [h1]
      _ = (h * t) * D.α h * D.g := by group
      _ = (t * h) * D.α h * D.g := by rw [hh]
      _ = t * (h * D.α h * D.g) := by group
  have hisG : isG (wm slSM slAC) wGS (slA (Nat.add a 2)) gc = true := by
    rw [isG, Bool.and_eq_true]
    obtain ⟨hF1, hF2⟩ := hFA gc hgc
    refine ⟨nbeq_true (sl_model.inj _ hF1 _ hgc ?_), allB_eq_true.2 fun i hi => ?_⟩
    · change E.α (subModel_sl.decW gc) = _ at hF2
      rw [← hF2, hdg, E.hαg]
    · have hgi := treeB_gen ch36409_tree hi
      obtain ⟨hA1, hA2⟩ := hFA _ hgi
      obtain ⟨hB1, hB2⟩ := hFA _ hA1
      change E.α _ = _ at hA2 hB2
      refine nbeq_true (sl_model.inj _ (sl_model.mul_lt _ hB1 _ hgc) _
        (sl_model.mul_lt _ hgc _ hgi) ?_)
      rw [sl_model.dec_mul _ hB1 _ hgc, sl_model.dec_mul _ hgc _ hgi, ← hB2, ← hA2, E.hα2, hdg]
      group
  have hT2 := allB_eq_true.1 ch36409_t2 a ha
  rw [slT2At, t2At, Bool.and_eq_true, Bool.and_eq_true] at hT2
  have hsq : gc = slGL a 0 ∨ gc = slGL a 1 := by
    obtain ⟨jj, hjj, hjg⟩ := hOK_mem sl_model (by norm_num) ch36409_h E.g hgt
    have hH := ch36409_h
    simp only [hOK, Bool.and_eq_true, allB_eq_true] at hH
    have hHl : hL (slSD 4) jj < 8192 := Nat.le_of_ble_eq_true (hH.1.1 jj hjj).1
    have hcode : hL (slSD 4) jj = gc := sl_model.inj _ hHl _ hgc (by rw [hjg, hdg])
    have hc := allB_eq_true.1 hT2.1.1 jj hjj
    rw [hcode, hisG] at hc
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc
    exact hc.imp Nat.eq_of_beq_eq_true Nat.eq_of_beq_eq_true
  set Φ := cycHom CycExt.incl_injective hcN hc2
  have hΦ : Function.Bijective Φ := by
    refine ⟨cycHom_injective CycExt.incl_injective hcN hc2 hcK, fun y => ?_⟩
    obtain ⟨k, d⟩ := y
    cases d
    · exact ⟨CycExt.incl _ k, cycHom_incl _ _ _ k⟩
    · refine ⟨⟨k * h⁻¹, true⟩, ?_⟩
      rw [cycHom_mk]
      change (⟨k * h⁻¹, false⟩ * (⟨h, true⟩ : CycExt D) : CycExt D) = ⟨k, true⟩
      rw [CycExt.mk_mul_mk]
      simp [CycExt.pw, CycExt.sq]
  have M3 := isModel_map
    (tm_model sl_model E (FA := slA (Nat.add a 2)) (fun c hc => hFA c hc) hgc hdg) Φ hΦ
  have hΦt : Φ (dec2 E subModel_sl.decW 128) = CycExt.incl D t := cycHom_incl _ _ _ t
  have hk : ∀ k < 2, gc = slGL a k → L2Facts (CycExt D) (CycExt.incl D t) := by
    intro k hk2 hgk
    by_cases hd : slDeep a k = true
    · simp only [slDeep, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hd
      obtain ⟨rfl, ((rfl | rfl) | rfl) | rfl⟩ := hd
      · rw [slGL_0] at hgk
        rw [hgk] at M3
        rw [← hΦt]
        exact slE0_l2 M3
      · rw [slGL_2] at hgk
        rw [hgk] at M3
        rw [← hΦt]
        exact slE1_l2 M3
      · rw [slGL_9] at hgk
        rw [hgk] at M3
        rw [← hΦt]
        exact slE2_l2 M3
      · rw [slGL_11] at hgk
        rw [hgk] at M3
        rw [← hΦt]
        exact slE3_l2 M3
    · exfalso
      have hdp := allB_eq_true.1 (allB_eq_true.1 ch36409_dp a ha) k hk2
      rw [Bool.or_eq_true] at hdp
      have hdp0 : bit slT2.b1 (Nat.add (Nat.mul 2 a) k) ≠ 1 := by
        rcases hdp with h | h
        · exact absurd h hd
        · intro h1
          rw [h1] at h
          exact absurd h (by decide)
      have hgd : gDeep (wm slSM slAC) (slSD 4) (slA (Nat.add a 2)) slT2.b0 slT2.b1
          (Nat.add (Nat.mul 2 a) k) = true := by
        interval_cases k
        · exact hT2.1.2
        · exact hT2.2
      have hgl : l16 slT2.b0 (Nat.add (Nat.mul 2 a) k) = gc := hgk.symm
      rw [gDeep, Bool.or_eq_true, Bool.or_eq_true, hgl] at hgd
      have hαt : E.α t = t := by
        rw [hEα, hα, hh, mul_inv_cancel_right]
      rcases hgd with (h1 | h1) | h1
      · have := Nat.eq_of_beq_eq_true h1
        omega
      · exact hdp0 (Nat.eq_of_beq_eq_true h1)
      · have hn := ninv2_eq sl_model E (t := 64) (by norm_num) ch36409_h (fun c hc => hFA c hc)
          hgc hdg hαt
        rw [ninvC_map (MulEquiv.ofBijective Φ hΦ), MulEquiv.ofBijective_apply] at hn
        change Nat.card {x : centralizer {Φ (dec2 E subModel_sl.decW 128)} // x ^ 2 = 1 ∧ x ≠ 1} =
          _ at hn
        rw [hΦt, hP.2] at hn
        rw [← hn] at h1
        exact absurd h1 (by decide)
  rcases hsq with h0 | h1
  · exact hk 0 (by norm_num) h0
  · exact hk 1 (by norm_num) h1

theorem towerFacts_sl : TowerFacts (Grp slS) (t₀ slS z0_mem_slS) := by
  have h64 := subModel_sl.decW_64 mat_sl1 z0_mem_slS
  refine ⟨l1Facts_sl, fun D hα hg hP => ?_⟩
  rw [← h64] at hα hg hP ⊢
  exact l2_sl D hα hg hP

end Certificates.KernelTower
