module

public import Certificates.Kernel.Misc.GL4.A5K
public import Certificates.Kernel.Misc.GL4.ClsK
public import Certificates.Kernel.Misc.GL4.EAFacts
public import CFSG.Certificates.Kernel.Misc.GL4F3Sound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.GL4A5

open Matrix CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 Certificates.A5GL42
open Certificates.GL4 (GL4)
open CertificateChecks.KernelMisc.GL4EA (EA eaAt_ok ea_exact)
open CertificateChecks.KernelMisc.GL4Cls (clAt clS clA0 clX clY invWit pairWit CW CB)

theorem vecOfCode_zero : vecOfCode 0 = 0 := by
  funext i
  simp [vecOfCode]

theorem mem_subspaces_of {W : Finset Vec4} {s : List ℕ} (hs : s ∈ subspaceCodes)
    (h1 : ∀ x ∈ s, vecOfCode x ∈ W) (h2 : ∀ u < 16, vecOfCode u ∈ W → u ∈ s) : W ∈ subspaces := by
  unfold subspaces
  rw [List.mem_toFinset, List.mem_map]
  refine ⟨s, hs, Finset.ext fun v => ?_⟩
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro hv
    obtain ⟨u, hu, rfl⟩ := vec_surj v
    exact ⟨u, h2 u hu hv, rfl⟩

theorem subspace_eq {W : Finset Vec4} (hW : W ∈ subspaces) :
    ∃ s ∈ subspaceCodes, (s.map vecOfCode).toFinset = W := by
  unfold subspaces at hW
  rw [List.mem_toFinset, List.mem_map] at hW
  exact hW

theorem subspaces_complete : SubspacesComplete := by
  intro W h0 hadd
  obtain ⟨s0, -, hlt, hext⟩ := subC
  let cnt : List ℕ → ℕ := fun s => ((Finset.range 16).filter fun u => vecOfCode u ∈ W ∧ u ∉ s).card
  suffices key : ∀ n, ∀ s ∈ subspaceCodes, (∀ x ∈ s, vecOfCode x ∈ W) → cnt s ≤ n →
      W ∈ subspaces by
    refine key 16 [0] s0 (by simp [vecOfCode_zero, h0]) ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  intro n
  induction n with
  | zero =>
    intro s hs hsW hc
    refine mem_subspaces_of hs hsW fun u hu huW => ?_
    by_contra hn
    have : 0 < cnt s := Finset.card_pos.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_range.2 hu, huW, hn⟩⟩
    omega
  | succ n ih =>
    intro s hs hsW hc
    by_cases hall : ∀ u < 16, vecOfCode u ∈ W → u ∈ s
    · exact mem_subspaces_of hs hsW hall
    push Not at hall
    obtain ⟨u, hu, huW, hus⟩ := hall
    have hs' := hext s hs u hu hus
    refine ih _ hs' (fun x hx => ?_) ?_
    · rw [List.mem_filter, decide_eq_true_eq] at hx
      rcases hx.2 with hx' | hx'
      · exact hsW x hx'
      · have hxu := (hlt s hs).2 _ hx'
        have e : vecOfCode x = vecOfCode (x ^^^ u) + vecOfCode u := by
          rw [← xorC _ hxu u hu, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [e]
        exact hadd _ (hsW _ hx') _ huW
    · have hsub : ((Finset.range 16).filter fun v => vecOfCode v ∈ W ∧
          v ∉ (List.range 16).filter (fun x => decide (x ∈ s ∨ (x ^^^ u) ∈ s))) ⊂
          ((Finset.range 16).filter fun v => vecOfCode v ∈ W ∧ v ∉ s) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨u, Finset.mem_filter.2 ⟨Finset.mem_range.2 hu, huW, hus⟩, fun h => ?_⟩
          refine (Finset.mem_filter.1 h).2.2 (List.mem_filter.2 ⟨List.mem_range.2 hu, ?_⟩)
          rw [decide_eq_true_eq, Nat.xor_self]
          exact Or.inr (hlt s hs).1
        · intro v hv
          rw [Finset.mem_filter] at hv ⊢
          refine ⟨hv.1, hv.2.1, fun h => hv.2.2 (List.mem_filter.2 ⟨?_, ?_⟩)⟩
          · exact List.mem_range.2 (Finset.mem_range.1 hv.1)
          · rw [decide_eq_true_eq]
            exact Or.inl h
      have := Finset.card_lt_card hsub
      simp only [cnt] at hc ⊢
      omega

theorem stab_of {c : ℕ} {s : List ℕ} {W : Finset Vec4} (hlt : ∀ x ∈ s, x < 16)
    (hW : (s.map vecOfCode).toFinset = W) (h : ∀ w ∈ W, ofCode c *ᵥ w ∈ W) : StabC c s := by
  intro x hx
  have hm : vecOfCode x ∈ W := by
    rw [← hW, List.mem_toFinset]
    exact List.mem_map_of_mem hx
  have h' := h _ hm
  rw [← hW, List.mem_toFinset, List.mem_map] at h'
  obtain ⟨y, hy, e⟩ := h'
  refine ⟨y, hy, ofCode_inj (mul4F_lt _ _) (colC_lt y (hlt y hy)) ?_⟩
  rw [mul4F_ofCode, colC_ofCode x (hlt x hx), mul_colM, colC_ofCode y (hlt y hy), e]

theorem mem_H {l : List ℕ} {x : Mat4} : x ∈ (l.map ofCode).toFinset ↔ ∃ c ∈ l, ofCode c = x := by
  rw [List.mem_toFinset, List.mem_map]

theorem groupFacts_of {l : List ℕ} {a b : ℕ} (hc : GrpC l a b) :
    GroupFacts (l.map ofCode).toFinset := by
  obtain ⟨hlt, hnd, hlen, h1, ha, hb, hmul, hinv, h4, hsub⟩ := hc
  refine ⟨mem_H.2 ⟨id4, h1, ofCode_id4⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨c, hc, rfl⟩ := mem_H.1 hx
    obtain ⟨d, hd, rfl⟩ := mem_H.1 hy
    exact mem_H.2 ⟨_, hmul c hc d hd, mul4F_ofCode _ _⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_H.1 hx
    obtain ⟨d, hd, e⟩ := hinv c hc
    exact ⟨ofCode d, mem_H.2 ⟨d, hd, rfl⟩, by rw [← mul4F_ofCode, e, ofCode_id4]⟩
  · rw [List.toFinset_card_of_nodup, List.length_map, hlen]
    exact hnd.map_on fun x hx y hy e => ofCode_inj (hlt x hx) (hlt y hy) e
  · intro x hx e
    obtain ⟨c, hc, rfl⟩ := mem_H.1 hx
    simp only [← mul4F_ofCode] at e ⊢
    rw [(ofCode_eq_one (mul4F_lt _ _)).1 e |> h4 c hc, ofCode_id4]
  · have s0 := subC.1
    have s16 := subC.2.1
    have slt := subC.2.2.1
    ext W
    simp only [invSubspaces, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hW, hinvW⟩
      obtain ⟨s, hs, hsW⟩ := subspace_eq hW
      have hsl := (slt s hs).2
      rcases hsub s hs (stab_of hsl hsW (hinvW _ (mem_H.2 ⟨a, ha, rfl⟩)))
          (stab_of hsl hsW (hinvW _ (mem_H.2 ⟨b, hb, rfl⟩))) with rfl | rfl
      · left
        rw [← hsW]
        simp [vecOfCode_zero]
      · right
        rw [← hsW, Finset.eq_univ_iff_forall]
        intro v
        obtain ⟨u, hu, rfl⟩ := vec_surj v
        rw [List.mem_toFinset]
        exact List.mem_map_of_mem (List.mem_range.2 hu)
    · rintro (rfl | rfl)
      · refine ⟨mem_subspaces_of s0 (by simp [vecOfCode_zero]) fun u hu hv => ?_, ?_⟩
        · rw [Finset.mem_singleton] at hv
          rw [vec_inj u hu 0 (by norm_num) (hv.trans vecOfCode_zero.symm)]
          exact List.mem_singleton_self 0
        · intro h _ w hw
          rw [Finset.mem_singleton] at hw ⊢
          rw [hw, Matrix.mulVec_zero]
      · exact ⟨mem_subspaces_of s16 (fun _ _ => Finset.mem_univ _)
          (fun u hu _ => List.mem_range.2 hu), fun _ _ _ _ => Finset.mem_univ _⟩

theorem HN_eq : HN = (codesN.map ofCode).toFinset := by rw [HN]

theorem HO_eq : HO = (codesO.map ofCode).toFinset := by rw [HO]

theorem groupN : GroupFacts HN := HN_eq ▸ groupFacts_of grpN

theorem groupO : GroupFacts HO := HO_eq ▸ groupFacts_of grpO

theorem gens : aN ∈ HN ∧ bN ∈ HN ∧ aO ∈ HO ∧ bO ∈ HO := by
  obtain ⟨e1, e2, e3, e4⟩ := gensC
  rw [HN_eq, HO_eq]
  exact ⟨mem_H.2 ⟨_, grpN.2.2.2.2.1, e1⟩, mem_H.2 ⟨_, grpN.2.2.2.2.2.1, e2⟩,
    mem_H.2 ⟨_, grpO.2.2.2.2.1, e3⟩, mem_H.2 ⟨_, grpO.2.2.2.2.2.1, e4⟩⟩

theorem clAt_ok (k : ℕ) (hk : k < 20160) : clAt k = true := by
  have h := CertificateChecks.KernelMisc.GL4Cls.CLK.all (k / 5040)
    (Nat.lt_of_lt_of_le (by omega : k / 5040 < 4) (by decide))
  exact (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 h k (Nat.mul_div_le k 5040) (by
    change k < 5040 * (k / 5040) + 5040
    omega)

theorem det_eq_one (g : GL4) : (g : Mat4).det = 1 := by
  have h := Matrix.isUnits_det_units g
  generalize (g : Mat4).det = x at h
  fin_cases x
  · exact absurd h not_isUnit_zero
  · rfl

theorem classify : Classify := by
  intro a b ha2 ha1 hb3 hab5
  have hb : b * b ^ 2 = 1 := by
    rw [← pow_succ']
    exact hb3
  let ga : GL4 := ⟨a, a, ha2, ha2⟩
  let gb : GL4 := ⟨b, b ^ 2, hb, mul_eq_one_comm.mp hb⟩
  have hga : (ga : Mat4) = a := rfl
  have hgb : (gb : Mat4) = b := rfl
  obtain ⟨k, hk, hkc⟩ := ea_exact.2.1 ga (Subgroup.mem_top _)
  have h := clAt_ok k hk
  unfold clAt at h
  rw [letB_eq, letB_eq, ← hkc] at h
  have hc1 : andB (Nat.beq (mul4F (enc4 ga) (enc4 ga)) id4) (notB (Nat.beq (enc4 ga) id4)) =
      true := by
    refine andB_iff.2 ⟨beq_iff.2 ((ofCode_eq_one (mul4F_lt _ _)).1 ?_), notB_iff.2 fun e => ?_⟩
    · rw [mul4F_ofCode, ofCode_enc4, hga, ha2]
    · exact ha1 (by rw [← hga, ← ofCode_enc4, beq_iff.1 e, ofCode_id4])
  have hw := impB_iff.1 (andB_iff.1 h).1 hc1
  unfold invWit at hw
  rw [letB_eq, letB_eq] at hw
  obtain ⟨hj, hw⟩ := andB_iff.1 hw
  obtain ⟨hi, hw⟩ := andB_iff.1 hw
  obtain ⟨g, -, hg⟩ := ea_exact.1 _ (Nat.blt_eq.mp hj)
  rw [← hg] at hw
  generalize Nat.shiftRight (CW k) 15 = i at hi hw
  have e1 : (g : Mat4) * a = ofCode (clA0 i) * g := by
    have := congrArg ofCode (beq_iff.1 hw)
    rwa [mul4F_ofCode, mul4F_ofCode, ofCode_enc4, ofCode_enc4, hga] at this
  have eA : ofCode (clA0 i) = ((g * ga * g⁻¹ : GL4) : Mat4) := by
    rw [Units.val_mul, Units.val_mul, hga, e1, mul_assoc, Units.mul_inv, mul_one]
  let b' : GL4 := g * gb * g⁻¹
  obtain ⟨k2, hk2, hk2c⟩ := ea_exact.2.1 b' (Subgroup.mem_top _)
  have h2 := clAt_ok k2 hk2
  unfold clAt at h2
  rw [letB_eq, letB_eq, ← hk2c] at h2
  have hgb3 : gb ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hgb, hb3, Units.val_one])
  have hgab5 : (ga * gb) ^ 5 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mul, hga, hgb, hab5, Units.val_one])
  have hc2 : Nat.beq (mul4F (mul4F (enc4 b') (enc4 b')) (enc4 b')) id4 = true := by
    refine beq_iff.2 ((ofCode_eq_one (mul4F_lt _ _)).1 ?_)
    rw [mul4F_ofCode, mul4F_ofCode, ofCode_enc4, ← Units.val_mul, ← Units.val_mul, ← Units.val_one]
    refine congrArg Units.val ?_
    rw [← pow_three', conj_pow, hgb3, mul_one, mul_inv_cancel]
  have h3 := (allN_iff _ _).1 (impB_iff.1 (andB_iff.1 h2).2 hc2) i (Nat.blt_eq.mp hi)
  have hc3 : Nat.beq (pow4F (mul4F (clA0 i) (enc4 b')) 5) id4 = true := by
    refine beq_iff.2 ((ofCode_eq_one (pow4F_lt _ _)).1 ?_)
    rw [ofCode_pow4F, mul4F_ofCode, eA, ofCode_enc4, ← Units.val_mul, ← Units.val_pow_eq_pow_val,
      ← Units.val_one]
    refine congrArg Units.val ?_
    have e : g * ga * g⁻¹ * b' = g * (ga * gb) * g⁻¹ := by
      simp only [b']
      group
    rw [e, conj_pow, hgab5, mul_one, mul_inv_cancel]
  have hp := impB_iff.1 h3 hc3
  unfold pairWit at hp
  rw [letB_eq, letB_eq] at hp
  obtain ⟨hh, hp⟩ := andB_iff.1 hp
  obtain ⟨hf, hp⟩ := andB_iff.1 hp
  obtain ⟨e2, e3⟩ := andB_iff.1 hp
  obtain ⟨g2, -, hg2⟩ := ea_exact.1 _ (Nat.blt_eq.mp hh)
  rw [← hg2] at e2 e3
  generalize Nat.shiftRight (CB (Nat.add (Nat.mul 2 k2) i)) 15 = f at hf e2 e3
  have E2 : (g2 : Mat4) * ofCode (clA0 i) = ofCode (clX f) * g2 := by
    have := congrArg ofCode (beq_iff.1 e2)
    rwa [mul4F_ofCode, mul4F_ofCode, ofCode_enc4] at this
  have E3 : (g2 : Mat4) * b' = ofCode (clY f) * g2 := by
    have := congrArg ofCode (beq_iff.1 e3)
    rwa [mul4F_ofCode, mul4F_ofCode, ofCode_enc4, ofCode_enc4] at this
  have hb' : (g : Mat4) * b = (b' : Mat4) * g := by
    rw [← hgb, ← Units.val_mul, ← Units.val_mul]
    refine congrArg Units.val ?_
    simp only [b']
    group
  have k1 : ((g2 * g : GL4) : Mat4) * a = ofCode (clX f) * (g2 * g : GL4) := by
    rw [Units.val_mul, mul_assoc, e1, ← mul_assoc, E2, mul_assoc]
  have k2' : ((g2 * g : GL4) : Mat4) * b = ofCode (clY f) * (g2 * g : GL4) := by
    rw [Units.val_mul, mul_assoc, hb', ← mul_assoc, E3, mul_assoc]
  refine ⟨((g2 * g : GL4) : Mat4), det_eq_one _, ?_⟩
  have hf2 := Nat.blt_eq.mp hf
  obtain ⟨c1, c2, c3, c4⟩ := gensC
  interval_cases f
  · exact Or.inl ⟨k1.trans (by rw [← c1]; rfl), k2'.trans (by rw [← c2]; rfl)⟩
  · exact Or.inr ⟨k1.trans (by rw [← c3]; rfl), k2'.trans (by rw [← c4]; rfl)⟩

end CertificateChecks.KernelMisc.GL4A5

end
