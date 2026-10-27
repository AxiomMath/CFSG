module

public import Certificates.Kernel.Misc.Perm.U33B.Checks
public import CFSG.Certificates.Kernel.Misc.PermU33BSound
public import CFSG.Certificates.Kernel.Misc.PermCover
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.U33SmallIndexInputs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33B

open Equiv CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.U33B CFSG.KC.LQT.P
open CFSG.GH74.KGroups.U33 CFSG.SignalizerFunctorTheorem.NonLocalExc

theorem hA : ∀ a < [pa, pb].length, AG a = pcode ([pa, pb].getD a 1) := by
  decide +kernel

theorem enc : ClosEnc (pcode (n := 28)) (mul 28) (one 28) := pcode_enc (by norm_num)

theorem G_eq : QP.originalSubgroup = Subgroup.closure {g | g ∈ [pa, pb]} := by
  rw [QP, CFSG.Sporadic.Schreier.certificate_originalSubgroup]

theorem word_elt (W : Nat → List Nat) (C : Nat → Nat) (m : Nat)
    (h : allN m (wordAt 28 AG 2 W C) = true) (j : Nat) (hj : j < m) :
    ∃ g ∈ QP.originalSubgroup, pcode g = C j := by
  have hj' := (allN_iff _ _).1 h j hj
  obtain ⟨h1, h2⟩ := andB_eq_true hj'
  obtain ⟨g, hg, hgc⟩ := word_mem (by norm_num) [pa, pb] hA h1
  exact ⟨g, G_eq ▸ hg, hgc.trans (Nat.eq_of_beq_eq_true h2)⟩

noncomputable def tE (j : Nat) : Perm (Fin 28) :=
  if h : j < 28 then (word_elt TW T 28 twB j h).choose else 1

noncomputable def kE (j : Nat) : Perm (Fin 28) :=
  if h : j < 2 then (word_elt KW KG 2 kwB j h).choose else 1

theorem tE_spec {j : Nat} (h : j < 28) : tE j ∈ QP.originalSubgroup ∧ pcode (tE j) = T j := by
  unfold tE
  split
  · exact (word_elt TW T 28 twB j h).choose_spec
  · contradiction

theorem kE_spec {j : Nat} (h : j < 2) : kE j ∈ QP.originalSubgroup ∧ pcode (kE j) = KG j := by
  unfold kE
  split
  · exact (word_elt KW KG 2 kwB j h).choose_spec
  · contradiction

abbrev K : Subgroup (Perm (Fin 28)) := Subgroup.closure {g | g ∈ [kE 0, kE 1]}

theorem hKG : ∀ j < [kE 0, kE 1].length, KG j = pcode ([kE 0, kE 1].getD j 1) := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact (kE_spec (j := 0) (by norm_num)).2.symm
  · exact (kE_spec (j := 1) (by norm_num)).2.symm

theorem clos : (∀ k < 216, ∃ g ∈ K, pcode g = E k) ∧ 216 ≤ Nat.card K ∧
    ∀ {CT : Nat → Nat}, (∀ k < 216, closedAt (mul 28) KG [kE 0, kE 1].length 216 E CT k = true) →
      Nat.card K = 216 ∧ ∀ g ∈ K, ∃ k < 216, pcode g = E k :=
  clos_card enc [kE 0, kE 1] hKG (by norm_num) ((allN_iff _ _).1 treeB) ((allN_iff _ _).1 sortB)

theorem img_eq0 {g : Perm (Fin 28)} {c : Nat} (hc : pcode g = c) : img c 0 = (g 0).val := by
  rw [← hc]
  exact pcode_img (by norm_num) g 0

theorem mem_B {g : Perm (Fin 28)} : g ∈ Bsub ↔ g ∈ QP.originalSubgroup ∧ g 0 = 0 := by
  simp [Bsub, MulAction.mem_stabilizer_iff]

theorem K_le : K ≤ Bsub := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  have hf := (allN_iff _ _).1 kfixB
  rw [SetLike.mem_coe, mem_B]
  rcases hg with rfl | rfl
  · refine ⟨(kE_spec (j := 0) (by norm_num)).1, ?_⟩
    have h := hf 0 (by norm_num)
    rw [img_eq0 (kE_spec (j := 0) (by norm_num)).2] at h
    exact Fin.ext (Nat.eq_of_beq_eq_true h)
  · refine ⟨(kE_spec (j := 1) (by norm_num)).1, ?_⟩
    have h := hf 1 (by norm_num)
    rw [img_eq0 (kE_spec (j := 1) (by norm_num)).2] at h
    exact Fin.ext (Nat.eq_of_beq_eq_true h)

theorem t_fix : ∀ j < 28, 0 < j → tE j 0 ≠ 0 := by
  intro j hj hj0 h
  have hf := impB_eq_true ((allN_iff _ _).1 fixB j hj) (Nat.blt_eq.mpr hj0)
  rw [img_eq0 (tE_spec hj).2, h] at hf
  exact absurd hf (by decide)

theorem ht0 : tE 0 = 1 := by
  apply enc.inj
  rw [(tE_spec (j := 0) (by norm_num)).2, enc.enc_one]
  exact Nat.eq_of_beq_eq_true t0B

theorem hcl : ∀ j < 28, ∀ a ∈ [pa, pb], ∃ j' < 28, tE j * a * (tE j')⁻¹ ∈ K := by
  intro j hj a ha
  have hai : ∃ ai < 2, AG ai = pcode a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, by norm_num, hA 0 (by norm_num)⟩
    · exact ⟨1, by norm_num, hA 1 (by norm_num)⟩
  obtain ⟨ai, hai2, hAa⟩ := hai
  have hc := (allN_iff _ _).1 ((allN_iff _ _).1 coverB j hj) ai hai2
  rw [letB_eq] at hc
  obtain ⟨hj', hc⟩ := andB_eq_true hc
  rw [letB_eq] at hc
  obtain ⟨ht, he⟩ := andB_eq_true hc
  set j' := img (inv 28 (AG ai)) j
  set t := IX (Nat.add (Nat.mul j 2) ai)
  have hj'' : j' < 28 := Nat.blt_eq.mp hj'
  refine ⟨j', hj'', ?_⟩
  obtain ⟨g, hg, hgc⟩ := clos.1 t (Nat.blt_eq.mp ht)
  have hpc : pcode (tE j * a * (tE j')⁻¹) = E t := by
    rw [enc.enc_mul, enc.enc_mul, ← pcode_inv (by norm_num), (tE_spec hj).2, (tE_spec hj'').2,
      ← hAa]
    exact (Nat.eq_of_beq_eq_true he).symm
  rw [← enc.inj (hgc.trans hpc.symm)]
  exact hg

theorem K_eq : K = Bsub := by
  refine le_antisymm K_le fun g hg => ?_
  obtain ⟨hgG, h0⟩ := mem_B.1 hg
  rw [G_eq] at hgG
  exact CFSG.KC.Misc.Cover.mem_of_fix [pa, pb] K tE 28 (by norm_num) ht0 0
    (fun k hk => (mem_B.1 (K_le hk)).2) t_fix hcl g hgG h0

theorem listB : ExactList pcode Bsub 216 E := by
  rw [← K_eq]
  unfold ExactList
  exact ⟨clos.1, (clos.2.2 ((allN_iff _ _).1 closedB)).2, sort_distinct ((allN_iff _ _).1 sortB)⟩

theorem cardB : Nat.card Bsub = 216 := by
  rw [← K_eq]
  exact (clos.2.2 ((allN_iff _ _).1 closedB)).1

open Certificates in
open CFSG.SignalizerFunctorTheorem.NonLocalExc in
theorem facts : Nat.card Bsub = 216 ∧
    (∀ x ∈ Bsub, ∀ y ∈ Bsub, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1) ∧
    Nat.card {g // g ∈ Bsub ∧ g ^ 3 = 1} = 27 ∧
    ∃ z ∈ Bsub, z ^ 3 = 1 ∧ z ≠ 1 ∧
      (∃ x ∈ Bsub, ∃ y ∈ Bsub, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z = x * y * x⁻¹ * y⁻¹) ∧
      ∀ a ∈ Bsub, a ^ 3 = 1 → a ≠ 1 → a ≠ z → a⁻¹ ≠ z →
        Nat.card {x // x ∈ Bsub ∧ ¬ x ^ 3 = 1 ∧ (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹)} ≤ 11 :=
  u33b_sound listB cardB (by decide) (by decide) (by decide) ((allN_iff _ _).1 cubeB)
    (Nat.eq_of_beq_eq_true cnt3) zB ((allN_iff _ _).1 smallB)

end CertificateChecks.KernelMisc.U33B

end
