module

public import Certificates.Kernel.FzUT.BAssocGlue
public import Certificates.Kernel.FzUT.BH2

public section

namespace CFSG.KC.FzBMod

open Certificates.FzBU CFSG.OddStandard.SmallF3.FritzII

private theorem B {n m : Nat} (h : Nat.beq n m = true) : n = m := Nat.eq_of_beq_eq_true h

theorem ne_of_beq_false {n m : Nat} (h : Nat.beq n m = false) : n ≠ m := fun e => by
  rw [e, Nat.beq_refl] at h
  cases h

theorem beq_false_of_ne {n m : Nat} (h : n ≠ m) : Nat.beq n m = false := by
  cases hb : Nat.beq n m
  · rfl
  · exact absurd (B hb) h

def InC (c : Bool) (z x : Nat) : Prop := x < 1024 ∧ mulN c x z = mulN c z x

theorem inC_mul (c : Bool) {z x y : Nat} (hz : z < 1024) (hx : InC c z x) (hy : InC c z y) :
    InC c z (mulN c x y) := by
  refine ⟨mulN_lt c x y, ?_⟩
  rw [mulN_assoc c hx.1 hy.1 hz, hy.2, ← mulN_assoc c hx.1 hz hy.1, hx.2,
    mulN_assoc c hz hx.1 hy.1]

theorem inC_zero (c : Bool) {z : Nat} (hz : z < 1024) : InC c z 0 :=
  ⟨by norm_num, by rw [mulN_zero_left c hz, mulN_zero_right c hz]⟩

structure EmbN (c : Bool) (ψ : Nat → Nat) : Prop where
  u : ψ 832 = 128
  zero : ψ 0 = 0
  mem : ∀ x, InC c 832 x → InC c 128 (ψ x)
  mul : ∀ x y, InC c 832 x → InC c 832 y → ψ (mulN c x y) = mulN c (ψ x) (ψ y)
  inj : ∀ x y, InC c 832 x → InC c 832 y → ψ x = ψ y → x = y

theorem embN_of {c : Bool} {ψ : Nat → Nat} (h : FzbIsEmb c 832 ψ) : EmbN c ψ := by
  have cv : ∀ {x}, InC c 832 x → fzbMul c x 832 = fzbMul c 832 x := fun hx => by
    rw [fzbMul_eq c hx.1 (by norm_num), fzbMul_eq c (by norm_num) hx.1]
    exact hx.2
  refine ⟨h.map_u, h.map_one, fun x hx => ?_, fun x y hx hy => ?_, fun x y hx hy => h.inj x hx.1 y hy.1 (cv hx) (cv hy)⟩
  · have hl := h.lt x hx.1 (cv hx)
    refine ⟨hl, ?_⟩
    have := h.comm_t x hx.1 (cv hx)
    rwa [fzbMul_eq c hl (by norm_num), fzbMul_eq c (by norm_num) hl] at this
  · have := h.map_mul x hx.1 y hy.1 (cv hx) (cv hy)
    rwa [fzbMul_eq c hx.1 hy.1, fzbMul_eq c (h.lt x hx.1 (cv hx)) (h.lt y hy.1 (cv hy))] at this

theorem embN_zero_iff {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {b : Nat} (hb : InC c 832 b) :
    Nat.beq (ψ b) 0 = Nat.beq b 0 := by
  have h0 := inC_zero c (z := 832) (by norm_num)
  cases h1 : Nat.beq b 0
  · have hb0 : b ≠ 0 := ne_of_beq_false h1
    have : ψ b ≠ 0 := fun h => hb0 (E.inj b 0 hb h0 (by rw [h, E.zero]))
    exact beq_false_of_ne this
  · rw [B h1, E.zero]
    rfl

theorem powN_succ (c : Bool) (a k : Nat) : powN c a (k + 1) = mulN c a (powN c a k) := rfl

theorem powN_map {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {a : Nat} (ha : InC c 832 a) (k : Nat) :
    InC c 832 (powN c a k) ∧ ψ (powN c a k) = powN c (ψ a) k := by
  induction k with
  | zero => exact ⟨inC_zero c (by norm_num), E.zero⟩
  | succ k ih =>
    rw [powN_succ, powN_succ, E.mul a _ ha ih.1, ih.2]
    exact ⟨inC_mul c (by norm_num) ha ih.1, rfl⟩

theorem ordOK_map {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {a : Nat} (ha : InC c 832 a) (o : Nat) :
    ordOK c (ψ a) o = ordOK c a o := by
  unfold ordOK
  rw [← (powN_map E ha o).2, ← (powN_map E ha (Nat.shiftRight o 1)).2,
    embN_zero_iff E (powN_map E ha o).1, embN_zero_iff E (powN_map E ha _).1]

theorem beq_map {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {p q : Nat} (hp : InC c 832 p)
    (hq : InC c 832 q) : Nat.beq (ψ p) (ψ q) = Nat.beq p q := by
  cases h1 : Nat.beq p q
  · have hpq : p ≠ q := ne_of_beq_false h1
    have : ψ p ≠ ψ q := fun h => hpq (E.inj p q hp hq h)
    exact beq_false_of_ne this
  · rw [B h1]
    exact Nat.beq_refl _

theorem pairT_map {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {a b : Nat} (ha : InC c 832 a)
    (hb : InC c 832 b) (e : Bool) (o : Nat) : pairT c (ψ a) (ψ b) e o = pairT c a b e o := by
  unfold pairT
  have hab := inC_mul c (by norm_num) ha hb
  have hba := inC_mul c (by norm_num) hb ha
  rw [← E.mul a b ha hb, ← E.mul b a hb ha, beq_map E hab hba, ordOK_map E hab]

theorem pick_map (f : Nat → Nat) (a b d e i : Nat) :
    pick (f a) (f b) (f d) (f e) i = f (pick a b d e i) := by
  unfold pick
  simp only [nIf_eq]
  split_ifs <;> rfl

theorem pick_mem (P : Nat → Prop) {a b d e : Nat} (ha : P a) (hb : P b) (hd : P d) (he : P e)
    (i : Nat) : P (pick a b d e i) := by
  unfold pick
  simp only [nIf_eq]
  split_ifs <;> assumption

theorem evY_map {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {a b d e : Nat} (ha : InC c 832 a)
    (hb : InC c 832 b) (hd : InC c 832 d) (he : InC c 832 e) (w : List Nat) :
    InC c 832 (evY c a b d e w) ∧ evY c (ψ a) (ψ b) (ψ d) (ψ e) w = ψ (evY c a b d e w) := by
  induction w with
  | nil => exact ⟨inC_zero c (by norm_num), E.zero.symm⟩
  | cons i w ih =>
    change InC c 832 (mulN c (pick a b d e i) (evY c a b d e w)) ∧
      mulN c (pick (ψ a) (ψ b) (ψ d) (ψ e) i) (evY c (ψ a) (ψ b) (ψ d) (ψ e) w) =
        ψ (mulN c (pick a b d e i) (evY c a b d e w))
    have hp := pick_mem (InC c 832) ha hb hd he i
    rw [pick_map, ih.2, E.mul _ _ hp ih.1]
    exact ⟨inC_mul c (by norm_num) hp ih.1, rfl⟩

theorem embN_conj {c : Bool} {ψ : Nat → Nat} (E : EmbN c ψ) {h hi : Nat} (hh : h < 1024)
    (hhi : hi < 1024) (e1 : mulN c h hi = 0) (e2 : mulN c hi h = 0)
    (et : mulN c h 128 = mulN c 128 h) : EmbN c (fun x => mulN c (mulN c h (ψ x)) hi) := by
  have A := @mulN_assoc c
  have L := mulN_lt c
  have Z0 := @mulN_zero_left c
  have Z1 := @mulN_zero_right c
  have hiT : mulN c hi 128 = mulN c 128 hi := by
    calc mulN c hi 128 = mulN c (mulN c hi 128) (mulN c h hi) := by rw [e1, Z1 (L _ _)]
      _ = mulN c (mulN c hi (mulN c 128 h)) hi := by
          rw [← A (L _ _) hh hhi, A hhi (by norm_num) hh]
      _ = mulN c 128 hi := by
          rw [← et, ← A hhi hh (by norm_num), e2, Z0 (by norm_num)]
  have conjC : ∀ x, InC c 128 x → InC c 128 (mulN c (mulN c h x) hi) := fun x hx =>
    inC_mul c (by norm_num) (inC_mul c (by norm_num) ⟨hh, et⟩ hx) ⟨hhi, hiT⟩
  refine ⟨?_, ?_, fun x hx => conjC _ (E.mem x hx), fun x y hx hy => ?_, fun x y hx hy hxy => ?_⟩
  · rw [E.u, et, A (by norm_num) hh hhi, e1, Z1 (by norm_num)]
  · rw [E.zero, Z1 hh, e1]
  · have px := (E.mem x hx).1
    have py := (E.mem y hy).1
    rw [E.mul x y hx hy]
    symm
    rw [A (L _ _) hhi (L _ _), ← A hhi (L _ _) hhi, ← A hhi hh py, e2, Z0 py,
      ← A (L _ _) py hhi, A hh px py]
  · apply E.inj x y hx hy
    have px := (E.mem x hx).1
    have py := (E.mem y hy).1
    have cancel : ∀ p < 1024, mulN c (mulN c hi (mulN c (mulN c h p) hi)) h = p := fun p hp => by
      rw [← A hhi (L _ _) hhi, ← A hhi hh hp, e2, Z0 hp, A hp hhi hh, e2, Z1 hp]
    rw [← cancel _ px, hxy, cancel _ py]

theorem h2srch (c : Bool) : allL h2R1 (h2Srch c (h2D c) h2SL) = true := by
  cases c
  · exact ch441796_h2srchII
  · exact ch441796_h2srchI

theorem fzbH2_of (c : Bool) : ∀ ψ, FzbIsEmb c 832 ψ → fzbW0 (ψ 1) ∧ fzbW0 (ψ 128) := by
  intro ψ hψ
  have E := embN_of hψ
  have A := @mulN_assoc c
  have L := mulN_lt c
  set D := h2D c with hD
  have hC := ch441796_h2consts c
  simp only [h2Consts, Bool.and_eq_true] at hC
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg1l, hg2l⟩, hg1c⟩, hg2c⟩, htc⟩, ho1⟩, ho2⟩, ho3⟩, hp01⟩, hp02⟩, hp03⟩,
    hp12⟩, hp13⟩, hp23⟩, hrel⟩, hw1⟩ := hC
  have hX1 : InC c 832 D.g1 := ⟨by simpa [Nat.blt_eq] using hg1l, B hg1c⟩
  have hX2 : InC c 832 D.g2 := ⟨by simpa [Nat.blt_eq] using hg2l, B hg2c⟩
  have hXt : InC c 832 128 := ⟨by norm_num, B htc⟩
  have hXu : InC c 832 832 := ⟨by norm_num, rfl⟩
  have hy1 := E.mem _ hX1
  have hSL : ∀ v, InC c 128 v → v ∈ h2SL := fun v hv => by
    have h := (allN_iff 1024 _).mp (ch441796_h2sl c) v hv.1
    simp only [h2SLOK, bIf_eq, hv.2, Nat.beq_refl, if_true] at h
    exact (memL_iff _ _).mp h
  have PT : ∀ {φ : Nat → Nat}, EmbN c φ → ∀ {a b : Nat}, InC c 832 a → InC c 832 b → ∀ e o,
      pairT c a b e o = true → pairT c (φ a) (φ b) e o = true := fun E a b ha hb e o h => by
    rw [pairT_map E ha hb]
    exact h
  have PT0 : ∀ {φ : Nat → Nat}, EmbN c φ → ∀ {b : Nat}, InC c 832 b → ∀ o,
      pairT c 832 b true o = true → pairT c 128 (φ b) true o = true := fun E b hb o h => by
    have := PT E hXu hb true o h
    rwa [E.u] at this
  have OK : ∀ {φ : Nat → Nat}, EmbN c φ → ∀ {a : Nat}, InC c 832 a → ∀ o,
      ordOK c a o = true → ordOK c (φ a) o = true := fun E a ha o h => by
    rw [ordOK_map E ha]
    exact h
  have hL1 : h2L1 c D (ψ D.g1) = true := by
    unfold h2L1
    rw [OK E hX1 _ ho1, PT0 E hX1 _ hp01]
  have hcov : Bool.rec (motive := fun _ => Bool) true
      (anyL h2Rec (fun rec => Nat.beq (fld(rec, 0, 1023)) (ψ D.g1))) (h2L1 c D (ψ D.g1)) = true :=
    (allL_iff _ _).mp (ch441796_h2cover c) _ (hSL _ hy1)
  rw [hL1] at hcov
  obtain ⟨rec, hrec, hrec0'⟩ := (anyL_iff _ _).mp hcov
  have hrec0 : Nat.beq (fld(rec, 0, 1023)) (ψ D.g1) = true := hrec0'
  have hR := (allL_iff _ _).mp (ch441796_h2rec c) rec hrec
  unfold h2RecOK at hR
  rw [letN_eq, letN_eq] at hR
  obtain ⟨r1, hR⟩ := bAnd_true hR
  obtain ⟨r2, hR⟩ := bAnd_true hR
  obtain ⟨r3, hR⟩ := bAnd_true hR
  obtain ⟨r4, hR⟩ := bAnd_true hR
  obtain ⟨r5, r6⟩ := bAnd_true hR
  set h := fld(rec, 10, 1023) with hh
  set hi := fld(rec, 20, 1023) with hhi
  have hlt : h < 1024 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hilt : hi < 1024 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have E' := embN_conj E hlt hilt (B r1) (B r2) (B r3)
  set φ := fun x => mulN c (mulN c h (ψ x)) hi with hφ
  have hr : φ D.g1 ∈ h2R1 := by
    have e : φ D.g1 = fld(rec, 30, 1023) := by
      rw [← B r4, B hrec0]
    rw [e]
    exact (memL_iff _ _).mp r5
  have hS := (allL_iff _ _).mp (h2srch c) _ hr
  unfold h2Srch at hS
  have hS2 := (allL_iff _ _).mp hS _ (hSL _ (E'.mem _ hX2))
  have hL2 : h2L2 c D (φ D.g1) (φ D.g2) = true := by
    unfold h2L2
    rw [OK E' hX2 _ ho2, PT0 E' hX2 _ hp02, PT E' hX1 hX2 _ _ hp12]
  rw [bIf_eq, if_pos hL2] at hS2
  have hS3 := (allL_iff _ _).mp hS2 _ (hSL _ (E'.mem _ hXt))
  have hL3 : h2L3 c D (φ D.g1) (φ D.g2) (φ 128) = true := by
    unfold h2L3
    rw [OK E' hXt _ ho3, PT0 E' hXt _ hp03, PT E' hX1 hXt _ _ hp13, PT E' hX2 hXt _ _ hp23]
  rw [bIf_eq, if_pos hL3] at hS3
  unfold h2Leaf at hS3
  have ev := fun w => evY_map E' hXu hX1 hX2 hXt w
  rw [E'.u] at ev
  have hrel' : Nat.beq (evY c 128 (φ D.g1) (φ D.g2) (φ 128) D.ra)
      (evY c 128 (φ D.g1) (φ D.g2) (φ 128) D.rb) = true := by
    rw [(ev D.ra).2, (ev D.rb).2, B hrel]
    exact Nat.beq_refl _
  rw [bIf_eq, if_pos hrel'] at hS3
  obtain ⟨hz, ht⟩ := bAnd_true hS3
  rw [(ev D.w1).2, B hw1] at hz
  have back : ∀ x, InC c 832 x → fzbW0 (φ x) → fzbW0 (ψ x) := fun x hx hW => by
    obtain ⟨i, hi8, hiE⟩ := (fzbW0_iff _).mp hW
    have hw := (allN_iff 8 _).mp r6 i hi8
    rw [hiE] at hw
    have px := (E.mem x hx).1
    have e : mulN c (mulN c hi (φ x)) h = ψ x := by
      simp only [hφ]
      rw [← A hilt (L _ _) hilt, ← A hilt hlt px, B r2, mulN_zero_left c px, A px hilt hlt,
        B r2, mulN_zero_right c px]
    rw [← e]
    exact (w0N_iff _).mp hw
  exact ⟨back 1 (by
      have := (ev D.w1).1
      rwa [B hw1] at this) ((w0N_iff _).mp hz),
    back 128 hXt ((w0N_iff _).mp ht)⟩

end CFSG.KC.FzBMod
