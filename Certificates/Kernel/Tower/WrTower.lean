module

public import Certificates.Kernel.Tower.WrQGlue
public import Certificates.Kernel.Tower.WrSGlue
public import Certificates.Kernel.Tower.SlTower

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower Subgroup


theorem wrRec_get {a : Nat} (ha : a < 96) :
    recB 8192 4 (wm wrSM wrAC) wrPT (imA wrIM a) (wrA (Nat.add a 2)) = true :=
  ch36408_rec_lt ha

theorem wrT2_get {a : Nat} (ha : a < 96) : wrT2At a = true := by
  have key : ∀ b, allFrom b 48 wrT2At = true → b ≤ a → a < b + 48 → wrT2At a = true := by
    intro b h h1 h2
    have := allFrom_get h (i := a - b) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  by_cases h1 : a < 48
  · exact key 0 ch36408_t2_0 (by omega) (by omega)
  · exact key 48 ch36408_t2_1 (by omega) (by omega)

theorem natRec_find (p : Nat → Bool) (d : Nat) (N : Nat) :
    Nat.rec (motive := fun _ => Nat) d (fun e acc => Bool.rec (motive := fun _ => Nat) acc e (p e))
        N = d ∨
      p (Nat.rec (motive := fun _ => Nat) d
        (fun e acc => Bool.rec (motive := fun _ => Nat) acc e (p e)) N) = true := by
  induction N with
  | zero => exact Or.inl rfl
  | succ N ih =>
    change Bool.rec (motive := fun _ => Nat) (Nat.rec (motive := fun _ => Nat) d
        (fun e acc => Bool.rec (motive := fun _ => Nat) acc e (p e)) N) N (p N) = d ∨
      p (Bool.rec (motive := fun _ => Nat) (Nat.rec (motive := fun _ => Nat) d
        (fun e acc => Bool.rec (motive := fun _ => Nat) acc e (p e)) N) N (p N)) = true
    cases hp : p N
    · exact ih
    · exact Or.inr hp

theorem wrFE_spec {a g : Nat} (h : wrFE a g < 12) : wrEP (wrFE a g) 0 = a ∧ wrEP (wrFE a g) 1 = g := by
  rcases natRec_find (fun e => Nat.beq (wrEP e 0) a && Nat.beq (wrEP e 1) g) 12 12 with h0 | h1
  · have h0' : wrFE a g = 12 := h0
    omega
  · have h1' : (Nat.beq (wrEP (wrFE a g) 0) a && Nat.beq (wrEP (wrFE a g) 1) g) = true := h1
    rw [Bool.and_eq_true] at h1'
    exact ⟨Nat.eq_of_beq_eq_true h1'.1, Nat.eq_of_beq_eq_true h1'.2⟩

variable {X : Type*} [Group X]

theorem wrE_l3 (D : ExtData (Grp wrS)) {e : Nat} (he : e < 12)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add (wrEP e 0) 2)) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add (wrEP e 0) 2)) c))
    (hg : subModel_wr.decW (wrEP e 1) = D.g) (D2 : ExtData (CycExt D))
    (hx : D2.α (dec2 D subModel_wr.decW (l16 (wrED e 5) 0)) = dec2 D subModel_wr.decW 128) :
    L3Facts (CycExt D2) (CycExt.incl D2 (dec2 D subModel_wr.decW 128)) := by
  obtain ⟨h, hht, k, hk, j, hj, hi⟩ := wrE_search D he hFA hg D2.α hx
  have hcN : (⟨h, true⟩ : CycExt D2) ∈
      normalizer ((CycExt.incl D2).range : Set (CycExt D2)) := by
    rw [mem_normalizer_iff]
    intro x
    change x ∈ (CycExt.incl D2).range ↔
      (⟨h, true⟩ : CycExt D2) * x * (⟨h, true⟩ : CycExt D2)⁻¹ ∈ (CycExt.incl D2).range
    rw [CycExt.mem_range_incl, CycExt.mem_range_incl, CycExt.d_mul, CycExt.d_mul, CycExt.d_inv]
    obtain ⟨k, d⟩ := x
    cases d <;> exact Iff.rfl
  have hc2 : (⟨h, true⟩ : CycExt D2) ^ 2 ∈ (CycExt.incl D2).range := by
    rw [CycExt.mem_range_incl, sq, CycExt.d_mul]
    rfl
  have hcK : (⟨h, true⟩ : CycExt D2) ∉ (CycExt.incl D2).range := by
    intro hm
    rw [CycExt.mem_range_incl] at hm
    exact Bool.noConfusion hm
  have hy : (⟨h, true⟩ : CycExt D2) = CycExt.incl D2 h * ⟨1, true⟩ := by
    change (⟨h, true⟩ : CycExt D2) = ⟨h, false⟩ * ⟨1, true⟩
    rw [CycExt.mk_mul_mk]
    simp only [CycExt.pw, CycExt.sq, Bool.false_and, Bool.false_eq_true, ite_false, mul_one,
      Bool.false_xor]
  have hEα : ∀ x, (ExtData.ofConj CycExt.incl_injective hcN hc2).α x = h * D2.α x * h⁻¹ := by
    intro x
    apply CycExt.incl_injective
    rw [map_ofConj_α, hy]
    calc CycExt.incl D2 h * ⟨1, true⟩ * CycExt.incl D2 x * (CycExt.incl D2 h * ⟨1, true⟩)⁻¹
        = CycExt.incl D2 h * ((⟨1, true⟩ : CycExt D2) * CycExt.incl D2 x *
            (⟨1, true⟩ : CycExt D2)⁻¹) * (CycExt.incl D2 h)⁻¹ := by group
      _ = CycExt.incl D2 h * CycExt.incl D2 (D2.α x) * (CycExt.incl D2 h)⁻¹ := by
          rw [CycExt.conj_y]
      _ = CycExt.incl D2 (h * D2.α x * h⁻¹) := by rw [map_mul, map_mul, map_inv]
  have hs : Function.Surjective (cycHom CycExt.incl_injective hcN hc2) := by
    rintro ⟨y, d⟩
    cases d
    · exact ⟨CycExt.incl _ y, cycHom_incl _ _ _ y⟩
    · refine ⟨⟨y * h⁻¹, true⟩, ?_⟩
      rw [cycHom_mk]
      change (⟨y * h⁻¹, false⟩ * (⟨h, true⟩ : CycExt D2) : CycExt D2) = ⟨y, true⟩
      rw [CycExt.mk_mul_mk]
      simp [CycExt.pw, CycExt.sq]
  refine l3Facts_ofConj CycExt.incl_injective hcN hc2 hcK hs
    (l3Facts_tgt D he hk hj hFA hg _ (fun i hi' => by rw [hEα]; exact hi i hi') ?_)
  rw [hEα, hx, hht]
  group

theorem l2_wr (D : ExtData (Grp wrS)) (hα : D.α (subModel_wr.decW 64) = subModel_wr.decW 64)
    (hg : D.g * subModel_wr.decW 64 = subModel_wr.decW 64 * D.g)
    (hP : PInv (centralizer {CycExt.incl D (subModel_wr.decW 64)} : Subgroup (CycExt D))) :
    L2Facts (CycExt D) (CycExt.incl D (subModel_wr.decW 64)) := by
  set t := subModel_wr.decW 64 with ht_def
  obtain ⟨h, hh, a, ha, himg⟩ := search_wr D.α hα
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
  have hFA := recB_sound wr_model ch36408_tree (wrRec_get ha) E.α.toMonoidHom (fun i hi => by
    change E.α _ = _
    rw [hEα]
    exact himg i hi)
  set gc := wr_model.code E.g with hgc_def
  have hgc : gc < 8192 := wr_model.code_lt (mem_top _)
  have hdg : subModel_wr.decW gc = E.g := wr_model.dec_code (mem_top _)
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
  have hisG : isG (wm wrSM wrAC) wGS (wrA (Nat.add a 2)) gc = true := by
    rw [isG, Bool.and_eq_true]
    obtain ⟨hF1, hF2⟩ := hFA gc hgc
    refine ⟨nbeq_true (wr_model.inj _ hF1 _ hgc ?_), allB_eq_true.2 fun i hi => ?_⟩
    · change E.α (subModel_wr.decW gc) = _ at hF2
      rw [← hF2, hdg, E.hαg]
    · have hgi := treeB_gen ch36408_tree hi
      obtain ⟨hA1, hA2⟩ := hFA _ hgi
      obtain ⟨hB1, hB2⟩ := hFA _ hA1
      change E.α _ = _ at hA2 hB2
      refine nbeq_true (wr_model.inj _ (wr_model.mul_lt _ hB1 _ hgc) _
        (wr_model.mul_lt _ hgc _ hgi) ?_)
      rw [wr_model.dec_mul _ hB1 _ hgc, wr_model.dec_mul _ hgc _ hgi, ← hB2, ← hA2, E.hα2, hdg]
      group
  have hsq : gc = wrGL a 0 ∨ gc = wrGL a 1 := by
    obtain ⟨jj, hjj, hjg⟩ := hOK_mem wr_model (by norm_num) ch36408_h E.g hgt
    have hH := ch36408_h
    simp only [hOK, Bool.and_eq_true, allB_eq_true] at hH
    have hHl : hL (wrSD 4) jj < 8192 := Nat.le_of_ble_eq_true (hH.1.1 jj hjj).1
    have hcode : hL (wrSD 4) jj = gc := wr_model.inj _ hHl _ hgc (by rw [hjg, hdg])
    have hT2 := wrT2_get ha
    rw [wrT2At, t2At, Bool.and_eq_true, Bool.and_eq_true] at hT2
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
  have hΦt : Φ (dec2 E subModel_wr.decW 128) = CycExt.incl D t := cycHom_incl _ _ _ t
  have hk : ∀ k < 2, gc = wrGL a k → L2Facts (CycExt D) (CycExt.incl D t) := by
    intro k hk2 hgk
    by_cases hlt : wrFE a gc < 12
    · obtain ⟨he0, he1⟩ := wrFE_spec hlt
      generalize wrFE a gc = e at hlt he0 he1
      have hFAe : ∀ c < 8192, l16 (wrA (Nat.add (wrEP e 0) 2)) c < 8192 ∧
          E.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add (wrEP e 0) 2)) c) := by
        rw [he0]
        exact fun c hc => hFA c hc
      have hge : subModel_wr.decW (wrEP e 1) = E.g := by
        rw [he1]
        exact hdg
      have M3e : IsModel (⊤ : Subgroup (CycExt D)) 16384 (wrEM e)
          (fun c => Φ (dec2 E subModel_wr.decW c)) :=
        isModel_map (tm_model wr_model E hFAe (wrE_g_lt hlt) hge) Φ hΦ
      rw [← hΦt]
      refine wrE_l2 hlt M3e fun D2 hD2 _ => ?_
      have hφ : Function.Injective ((CycExt.incl D2).comp Φ) :=
        CycExt.incl_injective.comp hΦ.1
      have hrange : ∀ x : CycExt D2, x ∈ ((CycExt.incl D2).comp Φ).range ↔ x.d = false := by
        intro x
        constructor
        · rintro ⟨y, rfl⟩
          rfl
        · intro hx
          obtain ⟨k, d⟩ := x
          change d = false at hx
          subst hx
          obtain ⟨y, rfl⟩ := hΦ.2 k
          exact ⟨y, rfl⟩
      have hcN2 : (⟨1, true⟩ : CycExt D2) ∈
          normalizer (((CycExt.incl D2).comp Φ).range : Set (CycExt D2)) := by
        rw [mem_normalizer_iff]
        intro x
        change x ∈ ((CycExt.incl D2).comp Φ).range ↔
          (⟨1, true⟩ : CycExt D2) * x * (⟨1, true⟩ : CycExt D2)⁻¹ ∈ ((CycExt.incl D2).comp Φ).range
        rw [hrange, hrange, CycExt.d_mul, CycExt.d_mul, CycExt.d_inv]
        obtain ⟨k, d⟩ := x
        cases d <;> exact Iff.rfl
      have hc22 : (⟨1, true⟩ : CycExt D2) ^ 2 ∈ ((CycExt.incl D2).comp Φ).range := by
        rw [hrange, sq, CycExt.d_mul]
        rfl
      have hcK2 : (⟨1, true⟩ : CycExt D2) ∉ ((CycExt.incl D2).comp Φ).range := by
        rw [hrange]
        exact Bool.noConfusion
      have hs : Function.Surjective (cycHom hφ hcN2 hc22) := by
        rintro ⟨y, d⟩
        obtain ⟨y', rfl⟩ := hΦ.2 y
        cases d
        · exact ⟨CycExt.incl _ y', cycHom_incl _ _ _ y'⟩
        · refine ⟨⟨y', true⟩, ?_⟩
          rw [cycHom_mk]
          change (⟨Φ y', false⟩ * (⟨1, true⟩ : CycExt D2) : CycExt D2) = ⟨Φ y', true⟩
          rw [CycExt.mk_mul_mk]
          simp [CycExt.pw, CycExt.sq]
      have hE2 : (ExtData.ofConj hφ hcN2 hc22).α (dec2 E subModel_wr.decW (l16 (wrED e 5) 0)) =
          dec2 E subModel_wr.decW 128 := by
        apply hφ
        rw [map_ofConj_α]
        change (⟨1, true⟩ : CycExt D2) * CycExt.incl D2 (Φ (dec2 E subModel_wr.decW
          (l16 (wrED e 5) 0))) * (⟨1, true⟩ : CycExt D2)⁻¹ =
            CycExt.incl D2 (Φ (dec2 E subModel_wr.decW 128))
        rw [CycExt.conj_y, hD2]
      exact l3Facts_ofConj hφ hcN2 hc22 hcK2 hs (wrE_l3 E hlt hFAe hge _ hE2)
    · exfalso
      have hdp := allB_eq_true.1 (allB_eq_true.1 ch36408_dp a ha) k hk2
      rw [Bool.or_eq_true, ← hgk] at hdp
      have hdp0 : bit wrT2.b1 (Nat.add (Nat.mul 2 a) k) ≠ 1 := by
        rcases hdp with h | h
        · exact absurd (Nat.le_of_ble_eq_true h) hlt
        · intro h1
          rw [h1] at h
          exact absurd h (by decide)
      have hT2 := wrT2_get ha
      rw [wrT2At, t2At, Bool.and_eq_true, Bool.and_eq_true] at hT2
      have hgd : gDeep (wm wrSM wrAC) (wrSD 4) (wrA (Nat.add a 2)) wrT2.b0 wrT2.b1
          (Nat.add (Nat.mul 2 a) k) = true := by
        interval_cases k
        · exact hT2.1.2
        · exact hT2.2
      have hgl : l16 wrT2.b0 (Nat.add (Nat.mul 2 a) k) = gc := hgk.symm
      rw [gDeep, Bool.or_eq_true, Bool.or_eq_true, hgl] at hgd
      have hαt : E.α t = t := by
        rw [hEα, hα, hh, mul_inv_cancel_right]
      rcases hgd with (h1 | h1) | h1
      · have := Nat.eq_of_beq_eq_true h1
        omega
      · exact hdp0 (Nat.eq_of_beq_eq_true h1)
      · have hn := ninv2_eq wr_model E (t := 64) (by norm_num) ch36408_h (fun c hc => hFA c hc)
          hgc hdg hαt
        rw [ninvC_map (MulEquiv.ofBijective Φ hΦ), MulEquiv.ofBijective_apply] at hn
        change Nat.card {x : centralizer {Φ (dec2 E subModel_wr.decW 128)} // x ^ 2 = 1 ∧ x ≠ 1} =
          _ at hn
        rw [hΦt, hP.2] at hn
        rw [← hn] at h1
        exact absurd h1 (by decide)
  rcases hsq with h0 | h1
  · exact hk 0 (by norm_num) h0
  · exact hk 1 (by norm_num) h1

theorem towerFacts_wr : TowerFacts (Grp wrS) (t₀ wrS z0_mem_wrS) := by
  have h64 := subModel_wr.decW_64 mat_wr1 z0_mem_wrS
  refine ⟨l1Facts_wr, fun D hα hg hP => ?_⟩
  rw [← h64] at hα hg hP ⊢
  exact l2_wr D hα hg hP

end Certificates.KernelTower
