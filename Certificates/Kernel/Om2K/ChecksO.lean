module

public import Certificates.Kernel.Om2K.OrbDefs
public meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Kernel.Om2K.Defs
import CFSG.Certificates.Kernel.SetOrbSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KC.SetOrb CFSG.KC.BfsPin

theorem kDist : distinctK 6300 (fun i => keyK 240 9 48 (Orb.C i)) Orb.S = true := by quickRfl

theorem kF0 : Nat.beq (eqMaskK 480 9 (EL.G 0) (cAK 2)) (Orb.M 0) = true := by quickRfl

theorem kN : Orb.N = 6300 := rfl

theorem kCov : allN 6300 covK = true := by quickRfl

theorem oBandI {a b : Bool} (ha : a = true) (hb : b = true) : bAnd(a, b) = true := by
  subst ha
  exact hb

@[expose] noncomputable def tr0OK (i : Nat) : Bool :=
  closK 9 48 8 Tr.c0.N TG.G Orb.C Orb.M Tr.c0.X Tr.c0.E i

@[expose] noncomputable def tr0OKc (c : Nat) : Bool :=
  allN 100 fun d => tr0OK (Nat.add (Nat.mul 100 c) d)

#kc_each CertificateChecks.KernelOm2.tr0OKc 0 63

theorem kTr0N : Tr.c0.N = 6300 := rfl

theorem tr0OKc_all : ∀ c < 63, tr0OKc c = true := by
  intro c hc
  interval_cases c
  exacts [tr0OKc0, tr0OKc1, tr0OKc2, tr0OKc3, tr0OKc4, tr0OKc5, tr0OKc6, tr0OKc7, tr0OKc8,
    tr0OKc9, tr0OKc10, tr0OKc11, tr0OKc12, tr0OKc13, tr0OKc14, tr0OKc15, tr0OKc16, tr0OKc17,
    tr0OKc18, tr0OKc19, tr0OKc20, tr0OKc21, tr0OKc22, tr0OKc23, tr0OKc24, tr0OKc25, tr0OKc26,
    tr0OKc27, tr0OKc28, tr0OKc29, tr0OKc30, tr0OKc31, tr0OKc32, tr0OKc33, tr0OKc34, tr0OKc35,
    tr0OKc36, tr0OKc37, tr0OKc38, tr0OKc39, tr0OKc40, tr0OKc41, tr0OKc42, tr0OKc43, tr0OKc44,
    tr0OKc45, tr0OKc46, tr0OKc47, tr0OKc48, tr0OKc49, tr0OKc50, tr0OKc51, tr0OKc52, tr0OKc53,
    tr0OKc54, tr0OKc55, tr0OKc56, tr0OKc57, tr0OKc58, tr0OKc59, tr0OKc60, tr0OKc61, tr0OKc62]

theorem tr0OK_all {i : Nat} (hi : i < Tr.c0.N) :
    closK 9 48 8 Tr.c0.N TG.G Orb.C Orb.M Tr.c0.X Tr.c0.E i = true := by
  rw [kTr0N] at hi
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (tr0OKc_all (i / 100) (by omega)) (i % 100)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 100 (i / 100)) (i % 100) = i := Nat.div_add_mod i 100
  rw [e] at h
  exact h

@[expose] noncomputable def oTIx (k x : Nat) : Nat :=
  Tr.c0.X (pg (nat_lit 16) (mask (nat_lit 16)) (Tr.c0.E (Tr.c0.Y x)) k)

@[expose] noncomputable def oClosT (N : Nat) (X E : Nat → Nat) (i : Nat) : Bool :=
  allN 8 fun k => strictB (pg (nat_lit 16) (mask (nat_lit 16)) (E i) k) fun j =>
    bAnd(Nat.blt j N, Nat.beq (X j) (oTIx k (X i)))

@[expose] noncomputable def oTreeT (ng R : Nat) (X D : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (Nat.mod (D i) (nat_lit 65536)) fun p => strictB (Nat.div (D i) (nat_lit 65536)) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l ng,
        bIf(Nat.blt l (nat_lit 8), Nat.beq (X i) (oTIx l (X p)),
          Nat.beq (imgK 9 48 R (Orb.C (X p))) (Orb.M (X i))))))

@[expose] noncomputable def oSubT (N : Nat) (X Y E D : Nat → Nat) (R : Nat) : Bool :=
  bAnd(allN N (oClosT N X E),
  bAnd(allN N (oTreeT 8 0 X D),
  bAnd(allN N (fun i => bAnd(invK X Y i, Nat.blt (X i) 6300)),
    Nat.beq (imgK 9 48 R (Orb.C 0)) (Orb.M (X 0)))))

@[expose] noncomputable def oTransS (N : Nat) (X Y D : Nat → Nat) (R : Nat) : Bool :=
  bAnd(Nat.ble N 6300,
  bAnd(allN N (fun i => bAnd(invK X Y i, Nat.blt (X i) 6300)),
  bAnd(allN N (oTreeT 9 R X D),
  bAnd(allN 6300 (fun y => bAnd(Nat.blt (Y y) N, Nat.beq (X (Y y)) y)), Nat.beq (X 0) 0))))

noncomputable def oDig : List Nat → Nat
  | [] => 0
  | a :: L => a + 65536 * oDig L

noncomputable def oEP (X Y g : Nat → Nat) (i : Nat) : Nat :=
  oDig ((List.range 8).map (fun k => Y (oTIx k (X i))) ++ [g i])

theorem tgR_lt (R : Nat) {k : Nat} (hk : k < 8) : tgR R k = TG.G k := by
  unfold tgR
  rw [Nat.blt_eq.mpr hk]

theorem kTrS0 : oTransS Tr.c0.N Tr.c0.X Tr.c0.Y Tr.c0.D (WS.G 0) = true := by quickRfl

theorem oTransS_X {N R : Nat} {X Y D : Nat → Nat} (h : oTransS N X Y D R = true) {i : Nat}
    (hi : i < N) : X i < 6300 := by
  obtain ⟨-, h⟩ := band h
  exact Nat.blt_eq.mp (band (CFSG.KS.Raw.Orb.allN_iff.1 (band h).1 i hi)).2

theorem oTransS_Y {N R : Nat} {X Y D : Nat → Nat} (h : oTransS N X Y D R = true) {y : Nat}
    (hy : y < 6300) : Y y < N ∧ X (Y y) = y := by
  obtain ⟨-, h⟩ := band h
  obtain ⟨-, h⟩ := band h
  obtain ⟨-, h⟩ := band h
  obtain ⟨a, b⟩ := band (CFSG.KS.Raw.Orb.allN_iff.1 (band h).1 y hy)
  exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩

theorem img_tIx {x k : Nat} (hx : x < 6300) (hk : k < 8) :
    imgK 9 48 (TG.G k) (Orb.C x) = Orb.M (oTIx k x) := by
  obtain ⟨h1, h2⟩ := oTransS_Y kTrS0 hx
  have hc := CFSG.KS.Raw.Orb.allN_iff.1 (tr0OK_all h1) k hk
  rw [strictB_eq] at hc
  have e := Nat.eq_of_beq_eq_true (band hc).2
  rw [h2] at e
  exact e

theorem closK_T {N : Nat} {G X E : Nat → Nat} {i k : Nat} (hG : G k = TG.G k)
    (h : oClosT N X E i = true) (hx : X i < 6300) (hk : k < 8) :
    (strictB (pg (nat_lit 16) (mask (nat_lit 16)) (E i) k) fun j =>
      bAnd(Nat.blt j N, Nat.beq (imgK 9 48 (G k) (Orb.C (X i))) (Orb.M (X j)))) = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  rw [strictB_eq] at h ⊢
  obtain ⟨h1, h2⟩ := band h
  rw [hG, img_tIx hx hk, ← Nat.eq_of_beq_eq_true h2]
  exact oBandI h1 (Nat.beq_refl _)

theorem treeK_T {ng R N i : Nat} {G X D : Nat → Nat} (hG : ∀ k < 8, G k = TG.G k)
    (hR : 8 < ng → G 8 = R) (hng : ng ≤ 9) (hX : ∀ i < N, X i < 6300) (hi : i < N)
    (h : oTreeT ng R X D i = true) : treeK 9 48 ng G Orb.C Orb.M X D i = true := by
  unfold oTreeT at h
  unfold treeK
  cases e : Nat.beq i 0
  · rw [e] at h
    change (strictB (Nat.mod (D i) 65536) fun p => strictB (Nat.div (D i) 65536) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l ng,
        bIf(Nat.blt l 8, Nat.beq (X i) (oTIx l (X p)),
          Nat.beq (imgK 9 48 R (Orb.C (X p))) (Orb.M (X i)))))) = true at h
    change (strictB (Nat.mod (D i) 65536) fun p => strictB (Nat.div (D i) 65536) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l ng,
        Nat.beq (imgK 9 48 (G l) (Orb.C (X p))) (Orb.M (X i))))) = true
    rw [strictB_eq, strictB_eq] at h ⊢
    generalize Nat.mod (D i) 65536 = p at h ⊢
    generalize Nat.div (D i) 65536 = l at h ⊢
    obtain ⟨h1, h2⟩ := band h
    obtain ⟨h2, h3⟩ := band h2
    have hp : X p < 6300 := hX p (by have := Nat.blt_eq.mp h1; omega)
    refine oBandI h1 (oBandI h2 ?_)
    cases e2 : Nat.blt l 8
    · rw [e2] at h3
      have hl8 : l = 8 := by
        have := Nat.blt_eq.mp h2
        have : ¬ l < 8 := fun h' => by rw [Nat.blt_eq.mpr h'] at e2; exact Bool.noConfusion e2
        omega
      subst hl8
      rw [hR (Nat.blt_eq.mp h2)]
      exact h3
    · rw [e2] at h3
      have hl := Nat.blt_eq.mp e2
      rw [hG l hl, img_tIx hp hl, ← Nat.eq_of_beq_eq_true h3]
      exact Nat.beq_refl _
  · rfl

theorem subOK_of_T {N R : Nat} {X Y E D : Nat → Nat} (h : oSubT N X Y E D R = true) :
    subOK N X Y E D R = true := by
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h34⟩ := band h2
  have hX : ∀ i < N, X i < 6300 := fun i hi =>
    Nat.blt_eq.mp (band (CFSG.KS.Raw.Orb.allN_iff.1 (band h34).1 i hi)).2
  refine oBandI (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => ?_)
    (oBandI (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => ?_) h34)
  · exact CFSG.KS.Raw.Orb.allN_iff.2 fun k hk =>
      closK_T rfl (CFSG.KS.Raw.Orb.allN_iff.1 h1 i hi) (hX i hi) hk
  · exact treeK_T (fun _ _ => rfl) (fun h => absurd h (by omega)) (by omega) hX hi
      (CFSG.KS.Raw.Orb.allN_iff.1 h2 i hi)

theorem oPg_div (P k : Nat) : pg 16 (mask 16) P k = P / 65536 ^ k % 65536 := by
  change (P >>> (16 * k)) &&& (2 ^ 16 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  norm_num

theorem oDig_get : ∀ (L : List Nat) (k : Nat), (∀ a ∈ L, a < 65536) →
    oDig L / 65536 ^ k % 65536 = L.getD k 0
  | [], k, _ => by simp [oDig]
  | a :: L, 0, h => by
    have ha := h a (by simp)
    simp only [oDig, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, List.getD_cons_zero]
    exact Nat.mod_eq_of_lt ha
  | a :: L, k + 1, h => by
    have ha := h a (by simp)
    have e : (a + 65536 * oDig L) / 65536 = oDig L := by
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [oDig, pow_succ', ← Nat.div_div_eq_div_mul, e, List.getD_cons_succ]
    exact oDig_get L k fun b hb => h b (by simp [hb])

theorem tIx_lt {x k : Nat} (hx : x < 6300) (hk : k < 8) : oTIx k x < 6300 := by
  have hc := CFSG.KS.Raw.Orb.allN_iff.1 (tr0OK_all (oTransS_Y kTrS0 hx).1) k hk
  rw [strictB_eq] at hc
  obtain ⟨hj, -⟩ := band hc
  unfold oTIx
  exact oTransS_X kTrS0 (Nat.blt_eq.mp hj)

theorem oEP_get {X Y g : Nat → Nat} {i k : Nat} (hY : ∀ k < 8, Y (oTIx k (X i)) < 65536)
    (hg : g i < 65536) :
    pg 16 (mask 16) (oEP X Y g i) k =
      ((List.range 8).map (fun k => Y (oTIx k (X i))) ++ [g i]).getD k 0 := by
  unfold oEP
  rw [oPg_div, oDig_get]
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
    exact hY k (List.mem_range.1 hk)
  · rw [List.mem_singleton.1 ha]
    exact hg

theorem transOK_of_S {N R : Nat} {X Y D g : Nat → Nat} (h : oTransS N X Y D R = true)
    (hg : ∀ i < N, g i < N ∧ imgK 9 48 R (Orb.C (X i)) = Orb.M (X (g i))) :
    transOK N X Y (oEP X Y g) D R = true := by
  obtain ⟨hN, h⟩ := band h
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h4⟩ := band h
  have hN' : N ≤ 6300 := Nat.le_of_ble_eq_true hN
  have hX : ∀ i < N, X i < 6300 := fun i hi =>
    Nat.blt_eq.mp (band (CFSG.KS.Raw.Orb.allN_iff.1 h1 i hi)).2
  have hS : ∀ y < 6300, Y y < N ∧ X (Y y) = y := fun y hy => by
    obtain ⟨a, b⟩ := band (CFSG.KS.Raw.Orb.allN_iff.1 h3 y hy)
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
  unfold transOK
  refine oBandI (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => ?_)
    (oBandI (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => ?_)
    (oBandI (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => CFSG.KS.Raw.Orb.allN_iff.1 h1 i hi) h4))
  · have hY : ∀ k < 8, Y (oTIx k (X i)) < 65536 := fun k hk => by
      have := (hS _ (tIx_lt (hX i hi) hk)).1
      omega
    obtain ⟨hgN, hgI⟩ := hg i hi
    refine CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => ?_
    rw [strictB_eq, oEP_get hY (by omega)]
    by_cases h8 : k < 8
    · have e : ((List.range 8).map (fun k => Y (oTIx k (X i))) ++ [g i]).getD k 0 =
          Y (oTIx k (X i)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h8)]
        simp [h8]
      rw [e]
      obtain ⟨hlt, hxy⟩ := hS _ (tIx_lt (hX i hi) h8)
      rw [hxy, tgR_lt R h8, img_tIx (hX i hi) h8]
      exact oBandI (Nat.blt_eq.mpr hlt) (Nat.beq_refl _)
    · have e8 : k = 8 := by omega
      subst e8
      have e : ((List.range 8).map (fun k => Y (oTIx k (X i))) ++ [g i]).getD 8 0 = g i := by
        simp
      rw [e]
      change bAnd(Nat.blt (g i) N, Nat.beq (imgK 9 48 R (Orb.C (X i))) (Orb.M (X (g i)))) = true
      rw [hgI]
      exact oBandI (Nat.blt_eq.mpr hgN) (Nat.beq_refl _)
  · exact treeK_T (fun _ hk => tgR_lt R hk) (fun _ => rfl) (le_refl _) hX hi
      (CFSG.KS.Raw.Orb.allN_iff.1 h2 i hi)

theorem kSubT0 : oSubT Sub.c0.N Sub.c0.X Sub.c0.Y Sub.c0.E Sub.c0.D (WS.G 0) = true := by quickRfl
theorem kSubT1 : oSubT Sub.c1.N Sub.c1.X Sub.c1.Y Sub.c1.E Sub.c1.D (WS.G 1) = true := by quickRfl
theorem kSubT2 : oSubT Sub.c2.N Sub.c2.X Sub.c2.Y Sub.c2.E Sub.c2.D (WS.G 2) = true := by quickRfl
theorem kSubT3 : oSubT Sub.c3.N Sub.c3.X Sub.c3.Y Sub.c3.E Sub.c3.D (WS.G 3) = true := by quickRfl
theorem kSubT4 : oSubT Sub.c4.N Sub.c4.X Sub.c4.Y Sub.c4.E Sub.c4.D (WS.G 4) = true := by quickRfl
theorem kSubT5 : oSubT Sub.c5.N Sub.c5.X Sub.c5.Y Sub.c5.E Sub.c5.D (WS.G 5) = true := by quickRfl
theorem kSubT6 : oSubT Sub.c6.N Sub.c6.X Sub.c6.Y Sub.c6.E Sub.c6.D (WS.G 6) = true := by quickRfl
theorem kSubT7 : oSubT Sub.c7.N Sub.c7.X Sub.c7.Y Sub.c7.E Sub.c7.D (WS.G 7) = true := by quickRfl
theorem kSubT8 : oSubT Sub.c8.N Sub.c8.X Sub.c8.Y Sub.c8.E Sub.c8.D (WS.G 8) = true := by quickRfl
theorem kSubT9 : oSubT Sub.c9.N Sub.c9.X Sub.c9.Y Sub.c9.E Sub.c9.D (WS.G 9) = true := by quickRfl
theorem kSubT10 : oSubT Sub.c10.N Sub.c10.X Sub.c10.Y Sub.c10.E Sub.c10.D (WS.G 10) = true := by
  quickRfl
theorem kSubT11 : oSubT Sub.c11.N Sub.c11.X Sub.c11.Y Sub.c11.E Sub.c11.D (WS.G 11) = true := by
  quickRfl

theorem kSub0 : subOK Sub.c0.N Sub.c0.X Sub.c0.Y Sub.c0.E Sub.c0.D (WS.G 0) = true :=
  subOK_of_T kSubT0
theorem kSub1 : subOK Sub.c1.N Sub.c1.X Sub.c1.Y Sub.c1.E Sub.c1.D (WS.G 1) = true :=
  subOK_of_T kSubT1
theorem kSub2 : subOK Sub.c2.N Sub.c2.X Sub.c2.Y Sub.c2.E Sub.c2.D (WS.G 2) = true :=
  subOK_of_T kSubT2
theorem kSub3 : subOK Sub.c3.N Sub.c3.X Sub.c3.Y Sub.c3.E Sub.c3.D (WS.G 3) = true :=
  subOK_of_T kSubT3
theorem kSub4 : subOK Sub.c4.N Sub.c4.X Sub.c4.Y Sub.c4.E Sub.c4.D (WS.G 4) = true :=
  subOK_of_T kSubT4
theorem kSub5 : subOK Sub.c5.N Sub.c5.X Sub.c5.Y Sub.c5.E Sub.c5.D (WS.G 5) = true :=
  subOK_of_T kSubT5
theorem kSub6 : subOK Sub.c6.N Sub.c6.X Sub.c6.Y Sub.c6.E Sub.c6.D (WS.G 6) = true :=
  subOK_of_T kSubT6
theorem kSub7 : subOK Sub.c7.N Sub.c7.X Sub.c7.Y Sub.c7.E Sub.c7.D (WS.G 7) = true :=
  subOK_of_T kSubT7
theorem kSub8 : subOK Sub.c8.N Sub.c8.X Sub.c8.Y Sub.c8.E Sub.c8.D (WS.G 8) = true :=
  subOK_of_T kSubT8
theorem kSub9 : subOK Sub.c9.N Sub.c9.X Sub.c9.Y Sub.c9.E Sub.c9.D (WS.G 9) = true :=
  subOK_of_T kSubT9
theorem kSub10 : subOK Sub.c10.N Sub.c10.X Sub.c10.Y Sub.c10.E Sub.c10.D (WS.G 10) = true :=
  subOK_of_T kSubT10
theorem kSub11 : subOK Sub.c11.N Sub.c11.X Sub.c11.Y Sub.c11.E Sub.c11.D (WS.G 11) = true :=
  subOK_of_T kSubT11

theorem kTrS1 : oTransS Tr.c1.N Tr.c1.X Tr.c1.Y Tr.c1.D (WS.G 1) = true := by quickRfl
theorem kTrS2 : oTransS Tr.c2.N Tr.c2.X Tr.c2.Y Tr.c2.D (WS.G 2) = true := by quickRfl
theorem kTrS3 : oTransS Tr.c3.N Tr.c3.X Tr.c3.Y Tr.c3.D (WS.G 3) = true := by quickRfl
theorem kTrS4 : oTransS Tr.c4.N Tr.c4.X Tr.c4.Y Tr.c4.D (WS.G 4) = true := by quickRfl
theorem kTrS5 : oTransS Tr.c5.N Tr.c5.X Tr.c5.Y Tr.c5.D (WS.G 5) = true := by quickRfl
theorem kTrS6 : oTransS Tr.c6.N Tr.c6.X Tr.c6.Y Tr.c6.D (WS.G 6) = true := by quickRfl
theorem kTrS7 : oTransS Tr.c7.N Tr.c7.X Tr.c7.Y Tr.c7.D (WS.G 7) = true := by quickRfl
theorem kTrS8 : oTransS Tr.c8.N Tr.c8.X Tr.c8.Y Tr.c8.D (WS.G 8) = true := by quickRfl
theorem kTrS9 : oTransS Tr.c9.N Tr.c9.X Tr.c9.Y Tr.c9.D (WS.G 9) = true := by quickRfl
theorem kTrS10 : oTransS Tr.c10.N Tr.c10.X Tr.c10.Y Tr.c10.D (WS.G 10) = true := by quickRfl
theorem kTrS11 : oTransS Tr.c11.N Tr.c11.X Tr.c11.Y Tr.c11.D (WS.G 11) = true := by quickRfl

end CertificateChecks.KernelOm2

#kc_each CertificateChecks.KernelOm2.orbOKc 0 63

end
