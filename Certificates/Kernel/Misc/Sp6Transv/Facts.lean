module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6TransvFacts
public import Certificates.Kernel.Misc.Sp6Transv.Checks
public import CFSG.Certificates.Kernel.Misc.Sp6TransvKit
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6Transv.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6Transv

theorem emul (a b : H6) : enc6 (a * b) = MULF (enc6 a) (enc6 b) := enc6_enc.enc_mul a b

theorem eq_of_enc {a b : H6} (h : enc6 a = enc6 b) : a = b := enc6_enc.inj h

theorem enc_one : enc6 1 = ONE := enc6_enc.enc_one

@[expose] def gTC : List ℕ :=
  [1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 1, 1, 1]

@[expose] def gTIC : List ℕ :=
  [1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 1, 0, 0]

theorem pairs : pairCheck (csG0, csG0I) = true ∧ pairCheck (csG1, csG1I) = true ∧
    pairCheck (aC, aI) = true ∧ pairCheck (bC, bI) = true ∧ pairCheck (gTC, gTIC) = true :=
  ⟨pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel)⟩

@[expose] noncomputable def cs0 : H6 := ofCode _ pairs.1
@[expose] noncomputable def cs1 : H6 := ofCode _ pairs.2.1
@[expose] noncomputable def ha : H6 := ofCode _ pairs.2.2.1
@[expose] noncomputable def hb : H6 := ofCode _ pairs.2.2.2.1
@[expose] noncomputable def gT : H6 := ofCode _ pairs.2.2.2.2

theorem enc_ofCode {cc : List ℕ × List ℕ} (h : pairCheck cc = true) (h2 : canon6 cc.2 = true) :
    enc6 (ofCode cc h) = pk cc.1 ∧ enc6 (ofCode cc h)⁻¹ = pk cc.2 :=
  ⟨enc6_of (mat6_ofCode cc h) (pairCheck_spec h).1, enc6_of (mat6_ofCode_inv cc h) h2⟩

theorem enc_cs0 : enc6 cs0 = KS 5 ∧ enc6 cs0⁻¹ = KS 7 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_cs1 : enc6 cs1 = KS 6 ∧ enc6 cs1⁻¹ = KS 8 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_ha : enc6 ha = KS 9 ∧ enc6 ha⁻¹ = KS 11 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.2.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_hb : enc6 hb = KS 10 ∧ enc6 hb⁻¹ = KS 12 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.2.2.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_gT : enc6 gT = L 7 ∧ enc6 gT⁻¹ = LI 7 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.2.2.2 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

structure Hyp (z : Fin 3 → H6) (t s f0 f2 : H6) (q : Fin 5 → H6) : Prop where
  hz : ∀ i, mat6 (z i) = dec6 (zCode i)
  ht : mat6 t = dec6 tCode
  hs : mat6 s = dec6 CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv.s0C
  hf0 : mat6 f0 = dec6 fl0C
  hf2 : mat6 f2 = dec6 fl2C
  hq : ∀ i, mat6 (q i) = dec6 (qCode i)

variable {z : Fin 3 → H6} {t s f0 f2 : H6} {q : Fin 5 → H6}

theorem Hyp.es (H : Hyp z t s f0 f2 q) : enc6 s = KS 0 := by
  rw [enc6_of H.hs (by decide +kernel)]; decide +kernel

theorem Hyp.ez0 (H : Hyp z t s f0 f2 q) : enc6 (z 0) = KS 1 := by
  rw [enc6_of (H.hz 0) (by decide +kernel)]; decide +kernel

theorem Hyp.ez1 (H : Hyp z t s f0 f2 q) : enc6 (z 1) = KS 2 := by
  rw [enc6_of (H.hz 1) (by decide +kernel)]; decide +kernel

theorem Hyp.ez2 (H : Hyp z t s f0 f2 q) : enc6 (z 2) = KS 3 := by
  rw [enc6_of (H.hz 2) (by decide +kernel)]; decide +kernel

theorem Hyp.et (H : Hyp z t s f0 f2 q) : enc6 t = KS 4 := by
  rw [enc6_of H.ht (by decide +kernel)]; decide +kernel

theorem Hyp.ef0 (H : Hyp z t s f0 f2 q) : enc6 f0 = L 0 := by
  rw [enc6_of H.hf0 (by decide +kernel)]; decide +kernel

theorem Hyp.ef2 (H : Hyp z t s f0 f2 q) : enc6 f2 = L 2 := by
  rw [enc6_of H.hf2 (by decide +kernel)]; decide +kernel

theorem Hyp.eq (H : Hyp z t s f0 f2 q) : ∀ j < 5, QG j = enc6 ([q 0, q 1, q 2, q 3, q 4].getD j 1)
  | 0, _ => by rw [List.getD_cons_zero, enc6_of (H.hq 0) (by decide +kernel)]; decide +kernel
  | 1, _ => by
    rw [List.getD_cons_succ, List.getD_cons_zero, enc6_of (H.hq 1) (by decide +kernel)]
    decide +kernel
  | 2, _ => by
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [enc6_of (H.hq 2) (by decide +kernel)]
    decide +kernel
  | 3, _ => by
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [enc6_of (H.hq 3) (by decide +kernel)]
    decide +kernel
  | 4, _ => by
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [enc6_of (H.hq 4) (by decide +kernel)]
    decide +kernel
  | j + 5, h => absurd h (by omega)

theorem Hyp.s_sq (H : Hyp z t s f0 f2 q) : s * s = 1 :=
  eq_of_enc (by rw [emul, H.es, enc_one]; decide +kernel)

theorem Hyp.s_inv (H : Hyp z t s f0 f2 q) : s⁻¹ = s := inv_eq_of_mul_eq_one_right H.s_sq

theorem Hyp.z_inv0 (H : Hyp z t s f0 f2 q) : (z 0)⁻¹ = z 0 * z 0 :=
  inv_eq_of_mul_eq_one_right (eq_of_enc (by rw [← mul_assoc, emul, emul, H.ez0, enc_one]; decide +kernel))

theorem Hyp.z_inv1 (H : Hyp z t s f0 f2 q) : (z 1)⁻¹ = z 1 * z 1 :=
  inv_eq_of_mul_eq_one_right (eq_of_enc (by rw [← mul_assoc, emul, emul, H.ez1, enc_one]; decide +kernel))

theorem Hyp.z_inv2 (H : Hyp z t s f0 f2 q) : (z 2)⁻¹ = z 2 * z 2 :=
  inv_eq_of_mul_eq_one_right (eq_of_enc (by rw [← mul_assoc, emul, emul, H.ez2, enc_one]; decide +kernel))

theorem Hyp.f0_sq (H : Hyp z t s f0 f2 q) : f0 * f0 = 1 :=
  eq_of_enc (by rw [emul, H.ef0, enc_one]; decide +kernel)

theorem Hyp.f2_sq (H : Hyp z t s f0 f2 q) : f2 * f2 = 1 :=
  eq_of_enc (by rw [emul, H.ef2, enc_one]; decide +kernel)

theorem Hyp.rels (H : Hyp z t s f0 f2 q) :
    s * s = 1 ∧ s ≠ 1 ∧ s * z 0 = z 0 * s ∧ s * z 2 = z 2 * s ∧ s * z 1 * s⁻¹ = (z 1)⁻¹ ∧
    f0 * f0 = 1 ∧ f0 * z 0 * f0⁻¹ = (z 0)⁻¹ ∧ f0 * z 1 = z 1 * f0 ∧ f0 * z 2 = z 2 * f0 ∧
    f2 * f2 = 1 ∧ f2 * z 2 * f2⁻¹ = (z 2)⁻¹ ∧ f2 * z 0 = z 0 * f2 ∧ f2 * z 1 = z 1 * f2 := by
  have i0 : f0⁻¹ = f0 := inv_eq_of_mul_eq_one_right H.f0_sq
  have i2 : f2⁻¹ = f2 := inv_eq_of_mul_eq_one_right H.f2_sq
  refine ⟨H.s_sq, fun h => ?_, ?_, ?_, ?_, H.f0_sq, ?_, ?_, ?_, H.f2_sq, ?_, ?_, ?_⟩
  · have e := congrArg enc6 h
    rw [H.es, enc_one] at e
    exact absurd e (by decide +kernel)
  · exact eq_of_enc (by rw [emul, emul, H.es, H.ez0]; decide +kernel)
  · exact eq_of_enc (by rw [emul, emul, H.es, H.ez2]; decide +kernel)
  · exact eq_of_enc (by rw [H.s_inv, H.z_inv1, emul, emul, emul, H.es, H.ez1]; decide +kernel)
  · exact eq_of_enc (by rw [i0, H.z_inv0, emul, emul, emul, H.ef0, H.ez0]; decide +kernel)
  · exact eq_of_enc (by rw [emul, emul, H.ef0, H.ez1]; decide +kernel)
  · exact eq_of_enc (by rw [emul, emul, H.ef0, H.ez2]; decide +kernel)
  · exact eq_of_enc (by rw [i2, H.z_inv2, emul, emul, emul, H.ef2, H.ez2]; decide +kernel)
  · exact eq_of_enc (by rw [emul, emul, H.ef2, H.ez0]; decide +kernel)
  · exact eq_of_enc (by rw [emul, emul, H.ef2, H.ez1]; decide +kernel)

@[expose] noncomputable def csl (i : ℕ) : H6 := ![cs0, cs1, cs0⁻¹, cs1⁻¹] ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

theorem enc_csl : ∀ l < 8, KS (5 + l % 4) = enc6 (csl l) := by
  intro l _
  have h : l % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold csl
  rcases (by omega : l % 4 = 0 ∨ l % 4 = 1 ∨ l % 4 = 2 ∨ l % 4 = 3) with e | e | e | e <;>
    simp only [e] <;> first | exact enc_cs0.1.symm | exact enc_cs1.1.symm | exact enc_cs0.2.symm |
      exact enc_cs1.2.symm

theorem Hyp.cs0_mem (H : Hyp z t s f0 f2 q) : cs0 ∈ Subgroup.centralizer ({s} : Set H6) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact eq_of_enc (by rw [emul, emul, H.es, enc_cs0.1]; decide +kernel)

theorem Hyp.cs1_mem (H : Hyp z t s f0 f2 q) : cs1 ∈ Subgroup.centralizer ({s} : Set H6) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact eq_of_enc (by rw [emul, emul, H.es, enc_cs1.1]; decide +kernel)

theorem Hyp.csl_mem (H : Hyp z t s f0 f2 q) (i : ℕ) :
    csl i ∈ Subgroup.centralizer ({s} : Set H6) := by
  unfold csl
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with e | e | e | e <;>
    simp only [e]
  · exact H.cs0_mem
  · exact H.cs1_mem
  · exact inv_mem H.cs0_mem
  · exact inv_mem H.cs1_mem

theorem Hyp.wordE_mem (H : Hyp z t s f0 f2 q) :
    ∀ n v, wordE csl n v ∈ Subgroup.centralizer ({s} : Set H6)
  | 0, _ => one_mem _
  | n + 1, v => mul_mem (H.csl_mem _) (H.wordE_mem n _)

@[expose] noncomputable def tgs : List H6 :=
  (List.range 4).map fun l => wordE csl (Nat.mod (TW l) 16) (Nat.div (TW l) 16)

theorem tgs_enc : ∀ j < tgs.length, TG j = enc6 (tgs.getD j 1) := by
  intro j hj
  have hl : tgs.length = 4 := by simp [tgs]
  rw [hl] at hj
  have hw := (allN_iff _ _).1 (GK.all 0 (by norm_num)) j hj
  rw [Nat.eq_of_beq_eq_true hw,
    wordF_enc (L := fun i => KS (Nat.add 5 (Nat.mod i 4))) (fun l hl => enc_csl l hl)]
  simp only [tgs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

@[expose] noncomputable def T1 : Subgroup H6 := Subgroup.closure {g | g ∈ tgs}

theorem tree_T1 : ∀ k < 512, treeAt MULF ONE TG tgs.length E P k = true :=
  forall_of_chunks 256 2 _ fun c hc => TK.all c hc

theorem sort_T1 : ∀ i < 512, sortAt 512 E S i = true :=
  (allR_iff _ _ _).1 (SK.all 0 (by norm_num)) |> fun h i hi => h i (Nat.zero_le _) hi

theorem closed_T1 : ∀ k < 512, closedAt MULF TG tgs.length 512 E C k = true :=
  forall_of_chunks 256 2 _ fun c hc => CK.all c hc

theorem T1_facts :
    (∀ k < 512, ∃ g ∈ T1, enc6 g = E k) ∧ Nat.card T1 = 512 ∧ ∀ g ∈ T1, ∃ k < 512, enc6 g = E k := by
  obtain ⟨h1, -, h3⟩ := clos_card_proved enc6_enc tgs tgs_enc (by norm_num) tree_T1 sort_T1
  obtain ⟨h4, h5⟩ := h3 closed_T1
  exact ⟨h1, h4, h5⟩

theorem Hyp.T1_le (H : Hyp z t s f0 f2 q) : T1 ≤ Subgroup.centralizer ({s} : Set H6) := by
  rw [T1, Subgroup.closure_le]
  intro g hg
  simp only [tgs, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
  obtain ⟨l, -, rfl⟩ := hg
  exact H.wordE_mem _ _

theorem q_parts :
    (∀ k < 32, treeAt MULF ONE QG 5 EQ QP k = true) ∧ (∀ i < 32, sortAt 32 EQ QS i = true) ∧
    (∀ k < 32, closedAt MULF QG 5 32 EQ QC k = true) ∧ abelQ EQ = true ∧
    countQ EQ (KS 1) (KS 3) = true ∧
    (∀ k < 9, treeAt MULF ONE (fun l => KS (1 + 2 * l)) 2 EZ PZ k = true) ∧
    (∀ i < 9, sortAt 9 EZ SZ i = true) ∧
    (∀ k < 9, closedAt MULF (fun l => KS (1 + 2 * l)) 2 9 EZ CZ k = true) := by
  have hq : qB 0 = true := QK.all 0 (by norm_num)
  unfold qB at hq
  obtain ⟨h1, hq⟩ := andB_eq_true hq
  obtain ⟨h2, hq⟩ := andB_eq_true hq
  obtain ⟨h3, hq⟩ := andB_eq_true hq
  obtain ⟨h4, hq⟩ := andB_eq_true hq
  obtain ⟨h5, hq⟩ := andB_eq_true hq
  obtain ⟨h6, hq⟩ := andB_eq_true hq
  obtain ⟨h7, h8⟩ := andB_eq_true hq
  have r : ∀ {n : ℕ} {f : ℕ → Bool}, allR 0 n f = true → ∀ i < n, f i = true :=
    fun h i hi => (allR_iff _ _ _).1 h i (Nat.zero_le _) (by omega)
  exact ⟨r h1, r h2, r h3, h4, h5, r h6, r h7, r h8⟩

theorem Hyp.card_E9 (H : Hyp z t s f0 f2 q) :
    Nat.card (Subgroup.closure {g | g ∈ [z 0, z 2]}) = 9 := by
  have hG : ∀ j < [z 0, z 2].length, KS (1 + 2 * j) = enc6 ([z 0, z 2].getD j 1) := by
    intro j hj
    have hj' : j < 2 := by simpa using hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact H.ez0.symm
    · exact H.ez2.symm
  obtain ⟨-, -, h3⟩ := clos_card_proved enc6_enc [z 0, z 2] hG (by norm_num) q_parts.2.2.2.2.2.1
    q_parts.2.2.2.2.2.2.1
  exact (h3 q_parts.2.2.2.2.2.2.2).1

theorem Hyp.E9_le (H : Hyp z t s f0 f2 q) :
    Subgroup.closure {g | g ∈ [z 0, z 2]} ≤ Subgroup.centralizer ({s} : Set H6) := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hg with rfl | rfl
  · exact (H.rels.2.2.1).symm
  · exact (H.rels.2.2.2.1).symm

theorem Hyp.card_cen_le (H : Hyp z t s f0 f2 q) :
    Nat.card (Subgroup.centralizer ({s} : Set H6)) * 63 ≤ Nat.card H6 := by
  have hob : obB 0 = true := OK.all 0 (by norm_num)
  unfold obB at hob
  obtain ⟨h1, h2⟩ := andB_eq_true hob
  have ht := (allR_iff _ _ _).1 h1
  have hs := (allR_iff _ _ _).1 h2
  have hc := conj_tree (G := fun l => if l = 0 then ha else hb) (x₀ := s) (N := 63) (E := OE) (PA := OP)
    (g := fun l => KS (9 + l)) (gi := fun l => KS (11 + l))
    (fun l hl => by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact enc_ha.1.symm
      · exact enc_hb.1.symm)
    (fun l hl => by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact enc_ha.2.symm
      · exact enc_hb.2.symm)
    (by rw [H.es]; exact fun k hk => ht k (Nat.zero_le _) hk)
  have hd := sort_distinct_proved (fun i hi => hs i (Nat.zero_le _) hi)
  choose! h hh using hc
  refine CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_centralizer_mul_le
    (fun k : Fin 63 => h k * s * (h k)⁻¹) ?_ fun k => ⟨h k, rfl⟩
  intro a b e
  exact Fin.ext (hd a a.2 b b.2 (by rw [hh a a.2, hh b b.2]; exact congrArg enc6 e))

theorem Hyp.cs0_order (H : Hyp z t s f0 f2 q) : orderOf cs0 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (eq_of_enc ?_) fun h => ?_
  · rw [enc6_pow, enc_cs0.1, enc_one]
    decide +kernel
  · have e := congrArg enc6 h
    rw [enc_cs0.1, enc_one] at e
    exact absurd e (by decide +kernel)

theorem Hyp.card_cen (H : Hyp z t s f0 f2 q) :
    Nat.card (Subgroup.centralizer ({s} : Set H6)) = 23040 := by
  have h1 := H.card_cen_le
  rw [card_H6] at h1
  have d1 : 512 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) := by
    rw [← T1_facts.2.1]
    exact Subgroup.card_dvd_of_le H.T1_le
  have d2 : 9 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) := by
    rw [← H.card_E9]
    exact Subgroup.card_dvd_of_le H.E9_le
  have d3 : 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) := by
    have h := orderOf_dvd_natCard (⟨cs0, H.cs0_mem⟩ : Subgroup.centralizer ({s} : Set H6))
    rwa [Subgroup.orderOf_mk, H.cs0_order] at h
  have d : 23040 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2) d3
  have hpos : 0 < Nat.card (Subgroup.centralizer ({s} : Set H6)) := Nat.card_pos
  obtain ⟨m, hm⟩ := d
  rw [hm] at h1 hpos ⊢
  have : m ≤ 1 := by nlinarith
  have : m ≠ 0 := by rintro rfl; simp at hpos
  obtain rfl : m = 1 := by omega
  rfl

end CertificateChecks.KernelMisc.Sp6Transv.Facts

end
