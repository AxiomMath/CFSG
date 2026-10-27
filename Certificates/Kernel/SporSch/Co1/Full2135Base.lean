
module

public import Certificates.Kernel.SporSch.Co1.FullK
public import Certificates.Kernel.SporSch.Co1.OrbX2
public import CFSG.Certificates.Kernel.SporSch.Co1FullSound
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace CertificateChecks.KernelSporSch.Co1Full2135

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
open CFSG.Sporadic.SmallF2.Native (transposeRows)
open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CertificateChecks.KernelSporSch.Co1Full CertificateChecks.KernelSporSch.Co1Orbs
open CertificateChecks.KernelSporSch.Co1Packed CertificateChecks.KernelSporSch.Co1Stab2148

local notation "Mt" g => ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem pts_ptK {i : Nat} (hi : i < 98280) : (Native.fullOrb 2).pts[i]! = ptK F2.T i := by
  rw [full2]
  exact (vorbK_sound F2.hr (by decide) (by decide) (by decide) F2.hc0 F2.hcN F2.hb F2.hp).2.2.1 i hi

theorem X_inv {g : GL24} (hg : g ∈ GA) {x : Vec24} (hx : x ∈ XS) :
    (Mt g) *ᵥ x ∈ XS := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, GA.mul_mem hg hh, by rw [Units.val_mul, ← mulVec_mulVec]⟩

abbrev fib (w : Vec24) : Set Vec24 := {x | x ∈ XS ∧ x + w ∈ XS}

theorem fib_eq {w : Nat} (hw : w < 2 ^ 24) :
    fib (toVecD 24 w) = (fun i => toVecD 24 ((Native.fullOrb 2).pts[i]!)) ''
      (((Finset.range 98280).filter fun k =>
        memK F2.T F2.S 98280 (Nat.xor (ptK F2.T k) w) = true : Finset ℕ) : Set ℕ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, Set.mem_image]
  constructor
  · rintro ⟨hx, hxw⟩
    have hx' := hx
    rw [X_eq] at hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    refine ⟨i, ⟨hi, ?_⟩, rfl⟩
    rw [← toVecD_xor, memX (Nat.xor_lt_two_pow (pts_lt hi) hw)] at hxw
    rwa [← pts_ptK hi]
  · rintro ⟨i, ⟨hi, hm⟩, rfl⟩
    refine ⟨by rw [X_eq]; exact ⟨i, hi, rfl⟩, ?_⟩
    rw [← toVecD_xor, memX (Nat.xor_lt_two_pow (pts_lt hi) hw), pts_ptK hi]
    exact hm

theorem ncard_fib {w N NS L : Nat} {C : Nat → Nat}
    (hw : w < 2 ^ 24) (hL : 98280 ≤ NS * L) (hc0 : C 0 = 0) (hcN : C NS = N)
    (h : ∀ s < NS, cntSl F2.T F2.S 98280 w (s * L) L (C s) (C (s + 1)) = true) :
    (fib (toVecD 24 w)).ncard = N := by
  rw [fib_eq hw, Set.InjOn.ncard_image, Set.ncard_coe_finset, cntSl_sound hL hc0 hcN h]
  intro i hi j hj hij
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
  exact enumSet_inj enum2 hi.1 hj.1 hij

noncomputable abbrev Um : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 (unpack 24 24 QU)

noncomputable abbrev Bm : Matrix (Fin 24) (Fin 24) (ZMod 2) := Um + Umᵀ

noncomputable abbrev q (v : Vec24) : ZMod 2 := qForm (toVecD 24 QA) Um v

theorem q_add (x y : Vec24) : q (x + y) = q x + q y + x ⬝ᵥ (Bm *ᵥ y) := by
  have h1 : y ⬝ᵥ (Um *ᵥ x) = x ⬝ᵥ (Umᵀ *ᵥ y) := by
    rw [dotProduct_mulVec, dotProduct_comm, mulVec_transpose]
  simp only [q, qForm, dotProduct_add, add_dotProduct, mulVec_add, Bm, add_mulVec, h1]
  ring

theorem q_zero : q 0 = 0 := by simp [q, qForm]

theorem q_val (c : Nat) : q (toVecD 24 c) = ((quadK QA QU c : ℕ) : ZMod 2) := quadK_sound _ _ _

theorem zmod2 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem single_eq (i : Fin 24) : toVecD 24 (Nat.shiftLeft 1 i) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, show Nat.shiftLeft 1 i.val = 2 ^ i.val from Nat.one_shiftLeft _,
    Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h', Ne.symm h]

theorem form_inv {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hB : Mᵀ * Bm * M = Bm)
    (he : ∀ i, q (M *ᵥ Pi.single i 1) = q (Pi.single i 1)) (v : Vec24) : q (M *ᵥ v) = q v := by
  have hpol : ∀ x y : Vec24, (M *ᵥ x) ⬝ᵥ (Bm *ᵥ (M *ᵥ y)) = x ⬝ᵥ (Bm *ᵥ y) := by
    intro x y
    have e : ∀ z, x ⬝ᵥ (Mᵀ *ᵥ z) = (M *ᵥ x) ⬝ᵥ z := fun z => by
      rw [dotProduct_mulVec, vecMul_transpose]
    calc (M *ᵥ x) ⬝ᵥ (Bm *ᵥ (M *ᵥ y)) = x ⬝ᵥ (Mᵀ *ᵥ (Bm *ᵥ (M *ᵥ y))) := (e _).symm
      _ = x ⬝ᵥ ((Mᵀ * Bm * M) *ᵥ y) := by rw [mulVec_mulVec, mulVec_mulVec]
      _ = x ⬝ᵥ (Bm *ᵥ y) := by rw [hB]
  let D : Vec24 →+ ZMod 2 := AddMonoidHom.mk' (fun x => q (M *ᵥ x) - q x) (by
    intro x y
    change q (M *ᵥ (x + y)) - q (x + y) = (q (M *ᵥ x) - q x) + (q (M *ᵥ y) - q y)
    rw [mulVec_add, q_add, q_add, hpol]
    ring)
  have hs : ∀ i (c : ZMod 2), D (Pi.single i c) = 0 := by
    intro i c
    rcases zmod2 c with rfl | rfl
    · rw [Pi.single_zero, map_zero]
    · change q (M *ᵥ Pi.single i 1) - q (Pi.single i 1) = 0
      rw [he i, sub_self]
  have hD : D v = 0 := by
    rw [← Finset.univ_sum_single v, map_sum]
    exact Finset.sum_eq_zero fun i _ => hs i (v i)
  exact sub_eq_zero.mp hD

theorem B_eq : rowsMatrix 24 (unpack 24 24 (Nat.xor QU (trK QU))) = Bm := by
  rw [xorM_sound, trM_sound]

theorem gen_inv {P : Nat}
    (hB : Nat.beq (CFSG.KC.Co1B.mulWK (trK P) (CFSG.KC.Co1B.mulWK (Nat.xor QU (trK QU)) P))
      (Nat.xor QU (trK QU)) = true)
    (hQ : CFSG.KC.Enum.allN 24 (fun i => Nat.beq (quadK QA QU (actK P (Nat.shiftLeft 1 i)))
      (quadK QA QU (Nat.shiftLeft 1 i))) = true) (v : Vec24) :
    q (rowsMatrix 24 (unpack 24 24 P) *ᵥ v) = q v := by
  refine form_inv ?_ (fun i => ?_) v
  · have h := congrArg (fun X => rowsMatrix 24 (unpack 24 24 X)) (Nat.eq_of_beq_eq_true hB)
    simp only [mulWM_eq, trM_sound, B_eq] at h
    rw [Matrix.mul_assoc]
    exact h
  · have h := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hQ i i.2)
    rw [← single_eq, actK_sound, q_val, q_val, h]

theorem mA1 : (Mt A₁) = rowsMatrix 24 (unpack 24 24 PA) := by
  have h : MRep Native.aR A₁ := rep_A₁
  unfold MRep at h
  rw [Co1ThreeLocal.aR_eq, uA] at h
  exact h.symm

theorem mA2 : (Mt A₂) = rowsMatrix 24 (unpack 24 24 PB) := by
  have h : MRep Native.bR A₂ := rep_A₂
  unfold MRep at h
  rw [Co1ThreeLocal.bR_eq, uB] at h
  exact h.symm

theorem q_GA {g : GL24} (hg : g ∈ GA) (v : Vec24) :
    q ((Mt g) *ᵥ v) = q v := by
  have hT : ∀ c : ZMod 2, ∀ w ∈ {u : Vec24 | q u = c}, (Mt g) *ᵥ w ∈ {u : Vec24 | q u = c} := by
    intro c
    refine closure_mapsTo (P := A₁) (Q := A₂) (Set.toFinite _) ?_ ?_ hg
    · intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      rw [mA1, gen_inv kB1 kQ1, hw]
    · intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      rw [mA2, gen_inv kB2 kQ2, hw]
  exact hT (q v) v rfl

theorem q_orbit {v w : Vec24} (h : w ∈ kOrbit GA v) : q w = q v := by
  obtain ⟨g, hg, rfl⟩ := h
  exact q_GA hg v

theorem add_self (x : Vec24) : x + x = 0 := by
  funext i
  have : ∀ c : ZMod 2, c + c = 0 := by decide
  exact this (x i)

theorem inv_left (g : GL24) (x : Vec24) : (Mt g⁻¹) *ᵥ ((Mt g) *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem inv_right (g : GL24) (x : Vec24) : (Mt g) *ᵥ ((Mt g⁻¹) *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

open Classical in
theorem ncard_eq (S : Set Vec24) : S.ncard = (Finset.univ.filter (· ∈ S)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

theorem orb_inv {G : Subgroup GL24} {g : GL24} (hg : g ∈ G) {y x : Vec24} (hx : x ∈ kOrbit G y) :
    (Mt g) *ᵥ x ∈ kOrbit G y := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, G.mul_mem hg hh, by rw [Units.val_mul, ← mulVec_mulVec]⟩

open Classical in
theorem count_bound_gen {G H : Subgroup GL24} {x₀ v : Vec24} (hH : H ≤ G)
    (hfix : ∀ h ∈ H, (Mt h) *ᵥ x₀ = x₀) (hv : v ∈ kOrbit G x₀) :
    (kOrbit G x₀).ncard * (kOrbit H v).ncard ≤
      {x | x ∈ kOrbit G x₀ ∧ x + (x₀ + v) ∈ kOrbit G x₀}.ncard * (kOrbit G (x₀ + v)).ncard := by
  set Y := kOrbit G x₀ with hY
  set w := x₀ + v with hw
  set O := kOrbit G w with hO
  set XF := Finset.univ.filter (· ∈ Y)
  set OF := Finset.univ.filter (· ∈ O)
  set HF := Finset.univ.filter (· ∈ kOrbit H v)
  set N := (XF.filter fun x => x + w ∈ Y).card
  have hN : {x | x ∈ Y ∧ x + w ∈ Y}.ncard = N := by
    rw [ncard_eq]
    congr 1
    ext x
    simp [XF]
  have hstep : ∀ x ∈ XF, (XF.filter fun y => x + y ∈ O).card =
      (OF.filter fun s => x + s ∈ Y).card := by
    intro x _
    refine Finset.card_nbij' (fun y => x + y) (fun s => x + s) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, XF, OF] at hy ⊢
      rw [← add_assoc, add_self, zero_add]
      exact ⟨hy.2, hy.1⟩
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, XF, OF] at hs ⊢
      rw [← add_assoc, add_self, zero_add]
      exact ⟨hs.2, hs.1⟩
    · intro y _
      simp only
      rw [← add_assoc, add_self, zero_add]
    · intro s _
      simp only
      rw [← add_assoc, add_self, zero_add]
  have hconst : ∀ s ∈ OF, (XF.filter fun x => x + s ∈ Y).card = N := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, OF] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    refine Finset.card_nbij' (fun x => (Mt g⁻¹) *ᵥ x) (fun x => (Mt g) *ᵥ x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, XF] at hx ⊢
      refine ⟨orb_inv (G.inv_mem hg) hx.1, ?_⟩
      have := orb_inv (G.inv_mem hg) hx.2
      rwa [mulVec_add, inv_left] at this
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, XF] at hx ⊢
      refine ⟨orb_inv hg hx.1, ?_⟩
      have := orb_inv hg hx.2
      rwa [mulVec_add] at this
    · intro x _
      exact inv_right g x
    · intro x _
      exact inv_left g x
  have hsum : ∑ x ∈ XF, (XF.filter fun y => x + y ∈ O).card = OF.card * N := by
    rw [Finset.sum_congr rfl hstep]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have hc : ∀ s ∈ OF, (∑ x ∈ XF, if x + s ∈ Y then 1 else 0) = N := fun s hs => by
      rw [← Finset.card_filter]
      exact hconst s hs
    rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
  have hlow : ∀ x ∈ XF, HF.card ≤ (XF.filter fun y => x + y ∈ O).card := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, XF] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    refine Finset.card_le_card_of_injOn (fun y => (Mt g) *ᵥ y) ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, HF, XF,
        Finset.mem_filter] at hy ⊢
      obtain ⟨h, hh, rfl⟩ := hy
      refine ⟨orb_inv hg (orb_inv (hH hh) hv), ?_⟩
      refine ⟨g * h, G.mul_mem hg (hH hh), ?_⟩
      rw [Units.val_mul, ← mulVec_mulVec, hw, mulVec_add, mulVec_add, hfix h hh]
    · intro y _ y' _ hyy
      have := congrArg (fun u => (Mt g⁻¹) *ᵥ u) hyy
      simpa only [inv_left] using this
  have hge : XF.card * HF.card ≤ ∑ x ∈ XF, (XF.filter fun y => x + y ∈ O).card := by
    have := Finset.card_nsmul_le_sum XF (fun x => (XF.filter fun y => x + y ∈ O).card) HF.card hlow
    rwa [smul_eq_mul] at this
  rw [ncard_eq Y, ncard_eq (kOrbit H v), hN, ncard_eq O]
  calc XF.card * HF.card ≤ OF.card * N := hge.trans hsum.le
    _ = N * OF.card := Nat.mul_comm _ _

theorem count_bound {x₀ v : Vec24} (H : Subgroup GL24)
    (hH : H ≤ GA) (hfix : ∀ h ∈ H, (Mt h) *ᵥ x₀ = x₀) (hx₀ : x₀ ∈ XS) (hv : v ∈ XS) :
    XS.ncard * (kOrbit H v).ncard ≤ (fib (x₀ + v)).ncard * (kOrbit GA (x₀ + v)).ncard := by
  have hX : XS = kOrbit GA x₀ := (kOrbit_eq_of_mem hx₀).symm
  unfold fib
  rw [hX] at hv ⊢
  exact count_bound_gen hH hfix hv

theorem orbit_disj {K : Subgroup GL24} {a b : Vec24} (h : a ∉ kOrbit K b) :
    Disjoint (kOrbit K a) (kOrbit K b) := by
  rw [Set.disjoint_left]
  intro c hca hcb
  apply h
  rw [← kOrbit_eq_of_mem hcb, kOrbit_eq_of_mem hca]
  exact mem_kOrbit_self _ _

theorem kOrbit_zero : kOrbit GA 0 = {0} := by
  ext w
  constructor
  · rintro ⟨g, -, rfl⟩
    rw [mulVec_zero]
    rfl
  · intro hw
    rw [Set.mem_singleton_iff.mp hw]
    exact mem_kOrbit_self _ _

theorem ne_zero {c : Nat} (hc : c < 2 ^ 24) (h0 : c ≠ 0) : toVecD 24 c ≠ 0 := by
  intro h
  rw [← toVecD_zero 24] at h
  exact h0 (toVecD_injective hc (by norm_num) h)

abbrev O0 : Set Vec24 := {0}

abbrev Gu : Set Vec24 := kOrbit GA (toVecD 24 10876918)

abbrev Gw : Set Vec24 := kOrbit GA (toVecD 24 16120435)

theorem v1_mem : stabVecOf 1 ∈ XS := (memX (by decide)).mpr x1

theorem v3_mem : stabVecOf 2 ∈ XS := (memX (by decide)).mpr x2

theorem u_eq : stabVecOf 0 + stabVecOf 1 = toVecD 24 10876918 := by
  rw [stabVecOf, stabVecOf, ← toVecD_xor]
  rfl

theorem w_eq : stabVecOf 0 + stabVecOf 2 = toVecD 24 16120435 := by
  rw [stabVecOf, stabVecOf, ← toVecD_xor]
  rfl

theorem q_X {x : Vec24} (hx : x ∈ XS) : q x = 0 := by
  have h : x ∈ kOrbit GA (stabVecOf 0) := by rw [kOrbit_eq_of_mem z_mem]; exact hx
  have hz : Native.stabVec 0 = 16663704 := rfl
  rw [q_orbit h, stabVecOf, hz, q_val, Nat.eq_of_beq_eq_true kqz]
  rfl

theorem q_one_ne : (1 : ZMod 2) ≠ 0 := by decide

theorem q_Gw {x : Vec24} (hx : x ∈ Gw) : q x = 1 := by
  rw [q_orbit hx, q_val, Nat.eq_of_beq_eq_true kqw]
  rfl

theorem q_Gu {x : Vec24} (hx : x ∈ Gu) : q x = 0 := by
  rw [q_orbit hx, q_val, Nat.eq_of_beq_eq_true kqu]
  rfl

theorem w_notin_X : toVecD 24 16120435 ∉ XS := fun h =>
  q_one_ne ((q_Gw (mem_kOrbit_self _ _)).symm.trans (q_X h))

theorem w_notin_Gu : toVecD 24 16120435 ∉ Gu := fun h =>
  q_one_ne ((q_Gw (mem_kOrbit_self _ _)).symm.trans (q_Gu h))

theorem u_notin_X : toVecD 24 10876918 ∉ XS := fun h =>
  absurd ((memX (by decide)).mp h) (by rw [mu]; decide)

theorem notin_O0 {c : Nat} (hc : c < 2 ^ 24) (h0 : c ≠ 0) : toVecD 24 c ∉ O0 :=
  ne_zero hc h0

theorem notin_zero {c : Nat} (hc : c < 2 ^ 24) (h0 : c ≠ 0) : toVecD 24 c ∉ kOrbit GA 0 := by
  rw [kOrbit_zero]
  exact notin_O0 hc h0

theorem d0 {c : Nat} (hc : c < 2 ^ 24) (h0 : c ≠ 0) : Disjoint O0 (kOrbit GA (toVecD 24 c)) := by
  have h := (orbit_disj (notin_zero hc h0)).symm
  rwa [kOrbit_zero] at h

theorem zero_notin_orbit {c : Nat} (hc : c < 2 ^ 24) (h0 : c ≠ 0) :
    (0 : Vec24) ∉ kOrbit GA (toVecD 24 c) := fun h =>
  Set.disjoint_left.mp (d0 hc h0) (Set.mem_singleton 0) h

theorem orbit_root0 : kOrbit GA (toVecD 24 (Native.fullRoot 0)) = O0 := by
  change kOrbit GA (toVecD 24 0) = O0
  rw [toVecD_zero, kOrbit_zero]

theorem orbit_root2 : kOrbit GA (toVecD 24 (Native.fullRoot 2)) = XS := rfl

theorem notin_X_small {c : Nat} (hc : c < 2 ^ 24) (hX : toVecD 24 c ∈ XS) :
    2 ≤ c := by
  have hm := (memX hc).mp hX
  rcases Nat.lt_or_ge c 2 with h | h
  · interval_cases c
    · rw [m0] at hm
      exact absurd hm (by decide)
    · rw [m1] at hm
      exact absurd hm (by decide)
  · exact h

theorem fullOK_two : Native.fullOK 2 = true := by
  unfold Native.fullOK Native.fullOKOf
  rw [Bool.and_eq_true]
  refine ⟨enum2, ?_⟩
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro i _ hi
  have hX : toVecD 24 ((Native.fullOrb 2).pts[i]!) ∈ XS := by
    rw [X_eq]
    exact ⟨i, hi, rfl⟩
  exact decide_eq_true (notin_X_small (pts_lt hi) hX)

end CertificateChecks.KernelSporSch.Co1Full2135

end
