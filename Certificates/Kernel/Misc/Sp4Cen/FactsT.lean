module

import CFSG.Certificates.Kernel.LocalQTPermSound
public import Certificates.Kernel.Misc.Sp4Cen.FactsS

public section

namespace CertificateChecks.KernelMisc.Sp4Cen

open Matrix CFSG.KD.Sp4Cen CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 CFSG.KC.Misc.Clos
  CFSG.KC.Misc.Sp4Cen
open Certificates.GL4 (GL4 sg)
open Certificates.A5GL42 (Mat4 ofCode)

theorem enc_lt (g : GL4) : enc4 g < 65536 := code4_lt _

theorem enc_mul (g h : GL4) : enc4 (g * h) = mul4F (enc4 g) (enc4 h) := gl4_enc.enc_mul g h

theorem inv_rec {x : GL4} (hx : x * x = 1) : ∃ k < 316, xOf RI k = enc4 x := by
  have h := (invK_sound sp4_inv_ok).2 (enc4 x) (enc_lt x)
  exact h.1 (by rw [← enc_mul, hx, gl4_enc.enc_one])

theorem ri_at {k : ℕ} (hk : k < 316) : riAt RI R0 R1 REPS0 REPS1 k = true :=
  (CFSG.KC.LQT.P.allN_iff _ _).1 sp4_ri_ok k hk

theorem conj_r {x : GL4} (hx : x * x = 1) (h1 : x ≠ 1) :
    ∃ g : GL4, enc4 (g * x * g⁻¹) = R0 ∨ enc4 (g * x * g⁻¹) = R1 := by
  obtain ⟨k, hk, e⟩ := inv_rec hx
  have h := ri_at hk
  rw [riAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, andB_iff, orB_iff] at h
  have e' : f16 (RI k) 0 = enc4 x := e
  rw [e'] at h
  rcases h.1 with h0 | h0
  · exact absurd (enc4_eq_id4.1 (Nat.eq_of_beq_eq_true h0)) h1
  · rw [andB_iff, CFSG.KC.LQT.P.letB_eq, orB_iff] at h0
    obtain ⟨g, hg, hgi⟩ := invW_sound (f16_lt _ _) (f16_lt _ _) h0.1
    refine ⟨g, ?_⟩
    rw [← conjF_enc, hg, hgi]
    rcases h0.2 with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · exact Or.inr (Nat.eq_of_beq_eq_true h)

theorem a2OK_sound {r : ℕ} {reps : List ℕ} {c ci : ℕ} {y b : GL4} (hr : enc4 b = r)
    (h : a2OK r reps (enc4 y) c ci = true) (hc : c < 65536) (hci : ci < 65536)
    (h3 : (b * y) ^ 3 = 1) (h1 : b * y ≠ 1) :
    ∃ u : GL4, u * b = b * u ∧ enc4 (u * y * u⁻¹) ∈ reps := by
  rw [a2OK, impB_iff] at h
  have hb3 : relB r (enc4 y) 3 = true := by
    rw [← hr]
    exact (relB_iff b y 3).2 h3
  have hb1 : notB (Nat.beq (mul4F r (enc4 y)) id4) = true := by
    rw [notB_iff]
    intro e
    exact h1 (enc4_eq_id4.1 (by rw [enc_mul, hr]; exact Nat.eq_of_beq_eq_true e))
  have hh := h (andB_iff.2 ⟨hb3, hb1⟩)
  rw [andB_iff, andB_iff] at hh
  obtain ⟨u, hu, hui⟩ := invW_sound hc hci hh.1
  refine ⟨u, gl4_enc.inj ?_, ?_⟩
  · rw [enc_mul, enc_mul, hu, hr]
    exact Nat.eq_of_beq_eq_true hh.2.1
  · rw [← conjF_enc, hu, hui]
    obtain ⟨d, hd, e⟩ := (anyL_iff _ _).1 hh.2.2
    rwa [← Nat.eq_of_beq_eq_true e]

theorem conj_rep {b y : GL4} (hb : enc4 b = R0 ∨ enc4 b = R1) (hy : y * y = 1)
    (h3 : (b * y) ^ 3 = 1) (h1 : b * y ≠ 1) :
    ∃ u : GL4, u * b = b * u ∧ ((enc4 b = R0 ∧ enc4 (u * y * u⁻¹) ∈ REPS0) ∨
      (enc4 b = R1 ∧ enc4 (u * y * u⁻¹) ∈ REPS1)) := by
  obtain ⟨k, hk, e⟩ := inv_rec hy
  have h := ri_at hk
  rw [riAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, andB_iff, andB_iff] at h
  have e' : f16 (RI k) 0 = enc4 y := e
  rw [e'] at h
  rcases hb with hb | hb
  · obtain ⟨u, hu1, hu2⟩ := a2OK_sound hb h.2.1 (f16_lt _ _) (f16_lt _ _) h3 h1
    exact ⟨u, hu1, Or.inl ⟨hb, hu2⟩⟩
  · obtain ⟨u, hu1, hu2⟩ := a2OK_sound hb h.2.2 (f16_lt _ _) (f16_lt _ _) h3 h1
    exact ⟨u, hu1, Or.inr ⟨hb, hu2⟩⟩

theorem witness : ∃ F X : GL4, orderOf F = 5 ∧ orderOf X = 3 ∧ F * X = X * F := by
  have h := sp4_wit_ok
  rw [witK, andB_iff, andB_iff, andB_iff, andB_iff] at h
  obtain ⟨F, hF, -⟩ := invW_sound (by decide) (by decide) h.1.1
  obtain ⟨X, hX, -⟩ := invW_sound (by decide) (by decide) h.1.2
  rw [← hF] at h
  rw [← hX] at h
  have h5 := (ordDiv_iff F 5).1 h.2.1.1
  have h3 := (ordDiv_iff X 3).1 h.2.1.2
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨F, X, orderOf_eq_prime h5.2 h5.1, orderOf_eq_prime h3.2 h3.1, gl4_enc.inj ?_⟩
  rw [enc_mul, enc_mul]
  exact Nat.eq_of_beq_eq_true h.2.2

theorem f16_testBit (r i j : ℕ) : (f16 r i).testBit j = (decide (j < 16) && r.testBit (16 * i + j)) := by
  change ((r >>> (16 * i)) &&& 65535).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, show (65535 : ℕ) = 2 ^ 16 - 1 from rfl,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem tup5_f16 {a b c d e : ℕ} (ha : a < 65536) (hb : b < 65536) (hc : c < 65536)
    (hd : d < 65536) (he : e < 65536) :
    f16 (tup5 a b c d e) 0 = a ∧ f16 (tup5 a b c d e) 1 = b ∧ f16 (tup5 a b c d e) 2 = c ∧
      f16 (tup5 a b c d e) 3 = d ∧ f16 (tup5 a b c d e) 4 = e := by
  have ht : tup5 a b c d e = a ||| b <<< 16 ||| (c <<< 32 ||| (d <<< 48 ||| e <<< 64)) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine Nat.eq_of_testBit_eq fun j => ?_ <;>
    rw [f16_testBit, ht] <;> by_cases hj : j < 16
  all_goals first
    | (have f : ¬ 16 ≤ j ∧ ¬ 32 ≤ j ∧ ¬ 48 ≤ j ∧ ¬ 64 ≤ j ∧ ¬ 32 ≤ 16 + j ∧ ¬ 48 ≤ 16 + j ∧
          ¬ 64 ≤ 16 + j ∧ ¬ 48 ≤ 32 + j ∧ ¬ 64 ≤ 32 + j ∧ ¬ 64 ≤ 48 + j ∧ 16 ≤ 16 + j ∧
          16 ≤ 32 + j ∧ 32 ≤ 32 + j ∧ 16 ≤ 48 + j ∧ 32 ≤ 48 + j ∧ 48 ≤ 48 + j ∧ 16 ≤ 64 + j ∧
          32 ≤ 64 + j ∧ 48 ≤ 64 + j ∧ 64 ≤ 64 + j := by omega
       obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16', f17, f18,
         f19, f20⟩ := f
       simp (disch := omega) [hj, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
         f16', f17, f18, f19, f20, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ge16])
    | (simp (disch := omega) [hj, testBit_ge16])

theorem srch_sound {r a2 a3 a4 a5 : GL4}
    (hr : (enc4 r = R0 ∧ enc4 a2 ∈ REPS0) ∨ (enc4 r = R1 ∧ enc4 a2 ∈ REPS1))
    (h3 : a3 * a3 = 1) (h4 : a4 * a4 = 1) (h5 : a5 * a5 = 1)
    (r3 : (r * a3) ^ 2 = 1) (e23 : (a2 * a3) ^ 3 = 1)
    (r4 : (r * a4) ^ 2 = 1) (e24 : (a2 * a4) ^ 2 = 1) (e34 : (a3 * a4) ^ 3 = 1)
    (r5 : (r * a5) ^ 2 = 1) (e25 : (a2 * a5) ^ 2 = 1) (e35 : (a3 * a5) ^ 2 = 1)
    (e45 : (a4 * a5) ^ 3 = 1) :
    ∃ m < 12, LF m = tup5 (enc4 r) (enc4 a2) (enc4 a3) (enc4 a4) (enc4 a5) := by
  have hs : srchK RI LF 12 (enc4 r) (enc4 a2) = true := by
    rcases hr with ⟨hr, h2⟩ | ⟨hr, h2⟩
    · rw [hr]
      exact (allL_iff _ _).1 sp4_srch0_ok _ h2
    · rw [hr]
      exact (allL_iff _ _).1 sp4_srch1_ok _ h2
  obtain ⟨k3, hk3, x3⟩ := inv_rec h3
  obtain ⟨k4, hk4, x4⟩ := inv_rec h4
  obtain ⟨k5, hk5, x5⟩ := inv_rec h5
  rw [srchK] at hs
  have s3 := (CFSG.KC.LQT.P.allN_iff _ _).1 hs k3 hk3
  rw [CFSG.KC.LQT.P.letB_eq, x3, impB_iff] at s3
  have s4 := (CFSG.KC.LQT.P.allN_iff _ _).1
    (s3 (andB_iff.2 ⟨(relB_iff _ _ _).2 r3, (relB_iff _ _ _).2 e23⟩)) k4 hk4
  rw [CFSG.KC.LQT.P.letB_eq, x4, impB_iff] at s4
  have s5 := (CFSG.KC.LQT.P.allN_iff _ _).1 (s4 (andB_iff.2 ⟨(relB_iff _ _ _).2 r4,
    andB_iff.2 ⟨(relB_iff _ _ _).2 e24, (relB_iff _ _ _).2 e34⟩⟩)) k5 hk5
  rw [CFSG.KC.LQT.P.letB_eq, x5, impB_iff] at s5
  have hl := s5 (andB_iff.2 ⟨(relB_iff _ _ _).2 r5, andB_iff.2 ⟨(relB_iff _ _ _).2 e25,
    andB_iff.2 ⟨(relB_iff _ _ _).2 e35, (relB_iff _ _ _).2 e45⟩⟩⟩)
  obtain ⟨m, hm, e⟩ := (CFSG.KC.LQT.P.anyN_iff _ _).1 hl
  exact ⟨m, hm, Nat.eq_of_beq_eq_true e⟩

theorem leaf_sound {m : ℕ} (hm : m < 12) (t : Fin 5 → GL4)
    (ht : LF m = tup5 (enc4 (t 0)) (enc4 (t 1)) (enc4 (t 2)) (enc4 (t 3)) (enc4 (t 4))) :
    ∃ w : GL4, (∀ i, w * t i * w⁻¹ ∈ SB) ∧
      SB ≤ Subgroup.closure (Set.range fun i => w * t i * w⁻¹) := by
  have h := (CFSG.KC.LQT.P.allN_iff _ _).1 sp4_leaf_ok m hm
  rw [leafAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, andB_iff,
    andB_iff, andB_iff] at h
  obtain ⟨w, hw, hwi⟩ := invW_sound (f16_lt _ _) (f16_lt _ _) h.1
  have hf := tup5_f16 (enc_lt (t 0)) (enc_lt (t 1)) (enc_lt (t 2)) (enc_lt (t 3)) (enc_lt (t 4))
  have hti : ∀ i : Fin 5, f16 (LF m) i = enc4 (t i) := by
    intro i
    rw [ht]
    fin_cases i
    · exact hf.1
    · exact hf.2.1
    · exact hf.2.2.1
    · exact hf.2.2.2.1
    · exact hf.2.2.2.2
  have hconj : ∀ i : Fin 5, conjF (f16 (LC m) 0) (f16 (LF m) i) (f16 (LC m) 1) =
      enc4 (w * t i * w⁻¹) := by
    intro i
    rw [hti, ← hw, ← hwi, conjF_enc]
  refine ⟨w, fun i => ?_, ?_⟩
  · rw [sb_eq_stab]
    refine mem_stabW_of_enc rfl ?_
    have := (CFSG.KC.LQT.P.allN_iff _ _).1 h.2.1 i i.2
    rw [hconj] at this
    exact Nat.eq_of_beq_eq_true this
  · set H := Subgroup.closure (Set.range fun i => w * t i * w⁻¹) with hH
    have hL : ∀ i, ∃ g ∈ H, enc4 g = letF (f16 (LC m) 0) (f16 (LC m) 1) (LF m) i := by
      intro i
      unfold letF
      cases hb : Nat.blt i 5
      · exact ⟨1, H.one_mem, gl4_enc.enc_one⟩
      · have hi : i < 5 := Nat.blt_eq.mp hb
        refine ⟨w * t ⟨i, hi⟩ * w⁻¹, Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩, ?_⟩
        exact (hconj ⟨i, hi⟩).symm
    have hgen : ∀ c ∈ [S0, S1], (∃ g ∈ H, enc4 g = c) := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [← Nat.eq_of_beq_eq_true h.2.2.1]
        exact wordE_mem hL _ _ _ ⟨1, H.one_mem, gl4_enc.enc_one⟩
      · rw [← Nat.eq_of_beq_eq_true h.2.2.2]
        exact wordE_mem hL _ _ _ ⟨1, H.one_mem, gl4_enc.enc_one⟩
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hl' : ∀ c ∈ [S0, S1], c < 65536 := fun c hc' => by
      obtain ⟨u, hu⟩ := exists_of_invOK (gens_inv c hc')
      rw [← hu]
      exact code4_lt _
    obtain ⟨g', hg', e⟩ := hgen _ ((mem_pset_iff hl').1 hg)
    rw [← gl4_enc.inj e]
    exact hg'

theorem conj_rel (c x y : GL4) {n : ℕ} (h : (x * y) ^ n = 1) :
    (c * x * c⁻¹ * (c * y * c⁻¹)) ^ n = 1 := by
  have e : c * x * c⁻¹ * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by group
  rw [e, conj_pow, h]
  group

theorem conj_sq (c x : GL4) (h : x * x = 1) : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
  have e : c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
  rw [e, h]
  group

theorem tuple_conj (a : Fin 5 → GL4) (hsq : ∀ i, a i * a i = 1)
    (h01 : (a 0 * a 1) ^ 3 = 1) (h12 : (a 1 * a 2) ^ 3 = 1) (h23 : (a 2 * a 3) ^ 3 = 1)
    (h34 : (a 3 * a 4) ^ 3 = 1) (h02 : (a 0 * a 2) ^ 2 = 1) (h03 : (a 0 * a 3) ^ 2 = 1)
    (h04 : (a 0 * a 4) ^ 2 = 1) (h13 : (a 1 * a 3) ^ 2 = 1) (h14 : (a 1 * a 4) ^ 2 = 1)
    (h24 : (a 2 * a 4) ^ 2 = 1) (hne : a 0 * a 1 ≠ 1) :
    ∃ c : GL4, Subgroup.closure (Set.range a) = SB.map (MulAut.conj c).toMonoidHom := by
  have ha0 : a 0 ≠ 1 := by
    intro h
    apply hne
    rw [h, one_mul] at h01 ⊢
    rw [pow_succ, pow_two, hsq 1, one_mul] at h01
    exact h01
  obtain ⟨g, hg⟩ := conj_r (hsq 0) ha0
  have hb1 : (g * a 0 * g⁻¹ * (g * a 1 * g⁻¹)) ^ 3 = 1 := conj_rel g _ _ h01
  have hb1' : g * a 0 * g⁻¹ * (g * a 1 * g⁻¹) ≠ 1 := by
    intro h
    apply hne
    have e : g * a 0 * g⁻¹ * (g * a 1 * g⁻¹) = g * (a 0 * a 1) * g⁻¹ := by group
    rw [e] at h
    calc a 0 * a 1 = g⁻¹ * (g * (a 0 * a 1) * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨u, hu, hrep⟩ := conj_rep hg (conj_sq g _ (hsq 1)) hb1 hb1'
  set c := u * g with hc
  set d : Fin 5 → GL4 := fun i => c * a i * c⁻¹ with hd
  have hd0 : d 0 = g * a 0 * g⁻¹ := by
    have e : d 0 = u * (g * a 0 * g⁻¹) * u⁻¹ := by
      simp only [hd, hc]
      group
    rw [e, hu]
    group
  have hd1 : d 1 = u * (g * a 1 * g⁻¹) * u⁻¹ := by
    simp only [hd, hc]
    group
  have hr : (enc4 (d 0) = R0 ∧ enc4 (d 1) ∈ REPS0) ∨ (enc4 (d 0) = R1 ∧ enc4 (d 1) ∈ REPS1) := by
    rw [hd0, hd1]
    exact hrep
  have hs := fun i => conj_sq c (a i) (hsq i)
  obtain ⟨m, hm, ht⟩ := srch_sound hr (hs 2) (hs 3) (hs 4) (conj_rel c _ _ h02)
    (conj_rel c _ _ h12) (conj_rel c _ _ h03) (conj_rel c _ _ h13) (conj_rel c _ _ h23)
    (conj_rel c _ _ h04) (conj_rel c _ _ h14) (conj_rel c _ _ h24) (conj_rel c _ _ h34)
  obtain ⟨w, hwS, hSw⟩ := leaf_sound hm d ht
  have hcl : Subgroup.closure (Set.range fun i => w * d i * w⁻¹) = SB :=
    le_antisymm ((Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hwS i)) hSw
  have hmap : (Subgroup.closure (Set.range a)).map (MulAut.conj (w * c)).toMonoidHom = SB := by
    have hfun : ((MulAut.conj (w * c)).toMonoidHom ∘ a) = fun i => w * d i * w⁻¹ := by
      funext i
      simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hd]
      group
    rw [MonoidHom.map_closure, ← Set.range_comp, hfun, hcl]
  refine ⟨(w * c)⁻¹, ?_⟩
  rw [← hmap, Subgroup.map_map]
  have hid : ((MulAut.conj (w * c)⁻¹).toMonoidHom.comp (MulAut.conj (w * c)).toMonoidHom) =
      MonoidHom.id GL4 := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [hid, Subgroup.map_id]

end CertificateChecks.KernelMisc.Sp4Cen

end
