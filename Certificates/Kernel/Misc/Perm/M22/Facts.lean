module

public import Certificates.Kernel.Misc.Perm.M22.Checks
public import CFSG.Certificates.Kernel.Misc.PermM22Sound
public import CFSG.Certificates.Kernel.Misc.PermCover
public import CFSG.Sporadic.Mathieu.M22

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M22

open Equiv CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.LQT.P CFSG.Sporadic.Mathieu
open CFSG.Blueprint
open CFSG.RankThree.Asc83Table.M22

theorem treeAll : ∀ i < 20160, treeAt (mul 22) (one 22) KG 2 E PA i = true :=
  (allN_iff _ _).1 treeB

theorem sortAll : ∀ i < 20160, sortAt 20160 E SG i = true := (allN_iff _ _).1 sortB

theorem closedAll : ∀ i < 20160, closedAt (mul 22) KG 2 20160 E CT i = true :=
  (allN_iff _ _).1 closedB

theorem badAll : ∀ i < 20160, badAt i = true := (allN_iff _ _).1 badB

theorem hA : ∀ a < [m22gA, m22gB].length, AG a = pcode ([m22gA, m22gB].getD a 1) := by
  decide +kernel
theorem hX : pcode x = xC := by decide +kernel
theorem hY : pcode y = yC := by decide +kernel
theorem hW : ∀ k < 9, pcode (w k) = WC k := by decide +kernel
theorem hQ : ∀ k < 9, ∀ l < 9, q8K q8L k l = m22Q8.contains (k, l) := by decide +kernel

theorem enc : ClosEnc (pcode (n := 22)) (mul 22) (one 22) := pcode_enc (by norm_num)

theorem M22_eq' : NativeSporadic.M22 = Subgroup.closure {g | g ∈ [m22gA, m22gB]} := by
  rw [m22_eq]
  congr 1
  ext z
  simp

theorem word_elt (W : Nat → List Nat) (C : Nat → Nat) (m : Nat)
    (h : allN m (wordAt 22 AG 2 W C) = true) (j : Nat) (hj : j < m) :
    ∃ g ∈ NativeSporadic.M22, pcode g = C j := by
  have hj' := (allN_iff _ _).1 h j hj
  obtain ⟨h1, h2⟩ := andB_eq_true hj'
  obtain ⟨g, hg, hgc⟩ := word_mem (by norm_num) [m22gA, m22gB] hA h1
  exact ⟨g, M22_eq' ▸ hg, hgc.trans (Nat.eq_of_beq_eq_true h2)⟩

noncomputable def tE (j : Nat) : Perm (Fin 22) :=
  if h : j < 22 then (word_elt TW T 22 twB j h).choose else 1

noncomputable def kE (j : Nat) : Perm (Fin 22) :=
  if h : j < 2 then (word_elt KW KG 2 kwB j h).choose else 1

theorem tE_spec {j : Nat} (h : j < 22) : tE j ∈ NativeSporadic.M22 ∧ pcode (tE j) = T j := by
  unfold tE
  split
  · exact (word_elt TW T 22 twB j h).choose_spec
  · contradiction

theorem kE_spec {j : Nat} (h : j < 2) : kE j ∈ NativeSporadic.M22 ∧ pcode (kE j) = KG j := by
  unfold kE
  split
  · exact (word_elt KW KG 2 kwB j h).choose_spec
  · contradiction

abbrev K : Subgroup (Perm (Fin 22)) := Subgroup.closure {g | g ∈ [kE 0, kE 1]}

theorem hKG : ∀ j < [kE 0, kE 1].length, KG j = pcode ([kE 0, kE 1].getD j 1) := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact (kE_spec (by norm_num)).2.symm
  · exact (kE_spec (by norm_num)).2.symm

theorem clos : (∀ k < 20160, ∃ g ∈ K, pcode g = E k) ∧ 20160 ≤ Nat.card K ∧
    ∀ {CT : Nat → Nat}, (∀ k < 20160, closedAt (mul 22) KG [kE 0, kE 1].length 20160 E CT k = true) →
      Nat.card K = 20160 ∧ ∀ g ∈ K, ∃ k < 20160, pcode g = E k :=
  clos_card enc [kE 0, kE 1] hKG (by norm_num) treeAll sortAll

theorem img_eq0 {g : Perm (Fin 22)} {c : Nat} (hc : pcode g = c) : img c 0 = (g 0).val := by
  rw [← hc]
  exact pcode_img (by norm_num) g 0

theorem K_fix : ∀ k ∈ K, k 0 = 0 := by
  have hle : K ≤ MulAction.stabilizer (Perm (Fin 22)) (0 : Fin 22) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    have hf := (allN_iff _ _).1 kfixB
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Perm.smul_def]
    rcases hg with rfl | rfl
    · have h := hf 0 (by norm_num)
      rw [img_eq0 (kE_spec (j := 0) (by norm_num)).2] at h
      exact Fin.ext (Nat.eq_of_beq_eq_true h)
    · have h := hf 1 (by norm_num)
      rw [img_eq0 (kE_spec (j := 1) (by norm_num)).2] at h
      exact Fin.ext (Nat.eq_of_beq_eq_true h)
  intro k hk
  exact hle hk

theorem t_fix : ∀ j < 22, 0 < j → tE j 0 ≠ 0 := by
  intro j hj hj0 h
  have hf := impB_eq_true ((allN_iff _ _).1 fixB j hj) (Nat.blt_eq.mpr hj0)
  rw [img_eq0 (tE_spec hj).2, h] at hf
  exact absurd hf (by decide)

theorem ht0 : tE 0 = 1 := by
  apply enc.inj
  rw [(tE_spec (j := 0) (by norm_num)).2, enc.enc_one]
  exact Nat.eq_of_beq_eq_true t0B

theorem hcl : ∀ j < 22, ∀ a ∈ [m22gA, m22gB], ∃ j' < 22, tE j * a * (tE j')⁻¹ ∈ K := by
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
  set j' := img (inv 22 (AG ai)) j
  set t := IX (Nat.add (Nat.mul j 2) ai)
  have hj'' : j' < 22 := Nat.blt_eq.mp hj'
  refine ⟨j', hj'', ?_⟩
  obtain ⟨g, hg, hgc⟩ := clos.1 t (Nat.blt_eq.mp ht)
  have hpc : pcode (tE j * a * (tE j')⁻¹) = E t := by
    rw [enc.enc_mul, enc.enc_mul, ← pcode_inv (by norm_num), (tE_spec hj).2, (tE_spec hj'').2,
      ← hAa]
    exact (Nat.eq_of_beq_eq_true he).symm
  rw [← enc.inj (hgc.trans hpc.symm)]
  exact hg

theorem stab : ∀ g ∈ NativeSporadic.M22, g 0 = 0 → g ∈ K := by
  intro g hg h0
  rw [M22_eq'] at hg
  exact CFSG.KC.Misc.Cover.mem_of_fix [m22gA, m22gB] K tE 22 (by norm_num) ht0 0 K_fix t_fix hcl
    g hg h0

theorem facts : ∀ g ∈ NativeSporadic.M22, g 0 = 0 → ∀ k < 9, ∀ l < 9, g * x = w k * g →
    g * y = w l * g → m22Q8.contains (k, l) = true := by
  intro g hg h0
  obtain ⟨k', hk', hgk⟩ := (clos.2.2 closedAll).2 g (stab g hg h0)
  have hb : noBadK xC yC WC q8L (E k') = true := badAll k' hk'
  rw [← hgk] at hb
  exact noBadK_sound hX hY hW hQ hb

end CertificateChecks.KernelMisc.M22

end
