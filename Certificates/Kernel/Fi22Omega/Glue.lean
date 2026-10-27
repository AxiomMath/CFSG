module

public import Certificates.Kernel.Fi22Omega.Gens
public import Certificates.Kernel.I242.Gens
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Fi22D4
public import CFSG.Certificates.Kernel.Fi22Omega.Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open Equiv CFSG.KC.Fi22Omega CFSG.KC.Benes CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.BfsPin CertificateChecks.KernelI242 CertificateChecks.KernelSpor
  CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.Native CFSG.Certificates.SetOrbit
open scoped Pointwise

theorem wordPt_zero (A : Nat → Nat) (p : Nat) : wordPt A 128 0 p = p := rfl

theorem wordPt_one (A : Nat → Nat) (p : Nat) : wordPt A 128 1 p = pg 12 4095 (A 0) p := rfl

theorem unpack_get3510 {P x : Nat} (hx : x < 3510) : (unpack 3510 12 P)[x]! = pg 12 4095 P x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  rfl

theorem u0_eq : ptSet 3510 fi22OmegaU0 = maskSet (rootM 0) := by
  ext x
  have e := Nat.eq_of_beq_eq_true u0
  change (x : ℕ) ∈ fi22OmegaU0.toList ↔ (rootM 0).testBit x = true
  rw [e, testBit_wordMask]
  simp only [wordPt_zero, u0L, exists_eq_right]

theorem smul_eq_of_maps {σ : Perm (Fin 3510)} {S : Set (Fin 3510)} (h : ∀ x ∈ S, σ x ∈ S) :
    σ • S = S := by
  have hsub : σ • S ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite S)
  rw [← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective σ)]

theorem root0_eq : rootM 0 = Nat.lor (MS 7) (Nat.lor (MS 8) (MS 9)) :=
  Nat.eq_of_beq_eq_true (band_true orbs).1

theorem mem_orb {x : Fin 3510} (hx : x ∈ maskSet (rootM 0)) :
    ∃ k < 3, (MS (Nat.add 7 k)).testBit x = true := by
  change (rootM 0).testBit x = true at hx
  rw [root0_eq, nlor, nlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true] at hx
  rcases hx with h | h | h
  · exact ⟨0, by decide, h⟩
  · exact ⟨1, by decide, h⟩
  · exact ⟨2, by decide, h⟩

theorem orb_sub {k : Nat} (hk : k < 3) {q : Nat} (h : (MS (Nat.add 7 k)).testBit q = true) :
    (rootM 0).testBit q = true := by
  rw [root0_eq, nlor, nlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true]
  interval_cases k
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem mem_u0L {x : Fin 3510} (hx : x ∈ maskSet (rootM 0)) : (x : Nat) ∈ u0L := by
  rw [← u0_eq] at hx
  exact hx

theorem yArr_eq {r : Nat} (hr : r < 8) : i242YArr r = unpack 3510 12 (Y.S r) := by
  rw [← yArrs.2 r hr]
  simp [i242YArrs, hr]

theorem i242Y_le_stab :
    i242Y ≤ MulAction.stabilizer (Perm (Fin 3510)) (ptSet 3510 fi22OmegaU0) := by
  rw [i242Y_eq, Subgroup.closure_le]
  rintro _ ⟨r, hr, rfl⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, u0_eq]
  refine smul_eq_of_maps fun x hx => ?_
  obtain ⟨k, hk, hO⟩ := mem_orb hx
  have hm := mapsOK_sound (allN_spec (allN_spec yFix r hr) k hk) x (mem_u0L hx) hO
  have hy : ((i242y r) x : Nat) = pg 12 4095 (Y.S r) x := by
    rw [← i242_rep_y hr x, yArr_eq hr, unpack_get3510 x.2]
  rw [wordPt_one, ← hy] at hm
  exact orb_sub hk hm

theorem lit2_get0 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[0]! = a := rfl

theorem fiveQGen_size : fi22FiveQGenArrs.size = 2 := by
  rw [fi22FiveQGenArrs]
  rfl

theorem fiveQGen_eq {k : Nat} (hk : k < 2) : fi22FiveQGenArrs[k]! = unpack 3510 12 (H.F k) := by
  rw [← fiveArr_eq (by omega), fi22FiveQGenArrs]
  interval_cases k
  · rw [lit2_get0, fi22FiveQ1Arr]
  · rw [lit2_get1, fi22FiveQ2Arr]

theorem fiveQ_le_stab :
    fi22FiveQ ≤ MulAction.stabilizer (Perm (Fin 3510)) (ptSet 3510 fi22OmegaU0) := by
  rw [fi22FiveQ, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := by
    have := hk
    rw [Set.mem_setOf_eq, fiveQGen_size] at this
    exact this
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, u0_eq]
  refine smul_eq_of_maps fun x hx => ?_
  have hc := cpK_iff (band_true (allN_spec lets k hk2)).2
  have hv := validA_unpack hc.2.1
  have hm := mapsOK_sound (allN_spec qFix k hk2) x (mem_u0L hx) hx
  have hq : ((permOfArr 3510 fi22FiveQGenArrs[k]!) x : Nat) = pg 12 4095 (H.F k) x := by
    rw [fiveQGen_eq hk2, ← (rep_of_validA hv) x, unpack_get3510 x.2]
  rw [wordPt_one, ← hq] at hm
  exact hm

end CertificateChecks.KernelFi22Omega

end
