module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6SRFacts
public import Certificates.Kernel.Misc.Sp6SR.Checks
public import Certificates.Kernel.Misc.Sp6Transv.FactsQ
public import Certificates.Kernel.Misc.Sp6Transv.FactsN
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6SR.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Sp6SR
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv
open CertificateChecks.KernelMisc.Sp6SR
open CertificateChecks.KernelMisc.Sp6Transv.Facts (enc_ofCode orB_true commF_iff tree_mem)

theorem emul (a b : H6) : enc6 (a * b) = MULF (enc6 a) (enc6 b) := enc6_enc.enc_mul a b

theorem eq_of_enc {a b : H6} (h : enc6 a = enc6 b) : a = b := enc6_enc.inj h

theorem enc_one : enc6 1 = ONE := enc6_enc.enc_one

theorem comm_of {g h : H6} {a b : ℕ} (hg : enc6 g = a) (hh : enc6 h = b)
    (e : MULF a b = MULF b a) : g * h = h * g :=
  eq_of_enc (by rw [emul, emul, hg, hh]; exact e)

theorem mem_cen_of {g h : H6} {a b : ℕ} (hg : enc6 g = a) (hh : enc6 h = b)
    (e : MULF a b = MULF b a) : g ∈ Subgroup.centralizer ({h} : Set H6) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  first | exact comm_of hg hh e | exact (comm_of hg hh e).symm

theorem inv_of_mul {g h : H6} {a b : ℕ} (hg : enc6 g = a) (hh : enc6 h = b) (e : MULF a b = ONE) :
    h = g⁻¹ :=
  eq_inv_of_mul_eq_one_right (eq_of_enc (by rw [emul, hg, hh, enc_one]; exact e))

theorem inv_eq_sq {g : H6} {a : ℕ} (hg : enc6 g = a) (e : MULF a (MULF a a) = ONE) :
    g⁻¹ = g * g :=
  inv_eq_of_mul_eq_one_right (eq_of_enc (by rw [emul, emul, hg, enc_one]; exact e))

theorem ne_of_enc {g h : H6} {a b : ℕ} (hg : enc6 g = a) (hh : enc6 h = b) (e : a ≠ b) : g ≠ h :=
  fun h' => e (by rw [← hg, ← hh, h'])

@[expose] def cg0C : List ℕ :=
  [1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1,
    0, 1, 0, 0]

@[expose] def cg0IC : List ℕ :=
  [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1,
    0, 1, 0, 0]

@[expose] def cg1C : List ℕ :=
  [0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1]

@[expose] def cg1IC : List ℕ :=
  [0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1,
    0, 0, 1, 0]

theorem pairs : pairCheck (cg0C, cg0IC) = true ∧ pairCheck (cg1C, cg1IC) = true ∧
    pairCheck (aC, aI) = true ∧ pairCheck (bC, bI) = true :=
  ⟨pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel)⟩

@[expose] noncomputable def cg0 : H6 := ofCode _ pairs.1
@[expose] noncomputable def cg1 : H6 := ofCode _ pairs.2.1
@[expose] noncomputable def ha : H6 := ofCode _ pairs.2.2.1
@[expose] noncomputable def hb : H6 := ofCode _ pairs.2.2.2

theorem enc_cg0 : enc6 cg0 = KY 13 ∧ enc6 cg0⁻¹ = KY 15 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_cg1 : enc6 cg1 = KY 14 ∧ enc6 cg1⁻¹ = KY 16 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_ha : enc6 ha = KY 9 ∧ enc6 ha⁻¹ = KY 11 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.2.1 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

theorem enc_hb : enc6 hb = KY 10 ∧ enc6 hb⁻¹ = KY 12 := by
  obtain ⟨h1, h2⟩ := enc_ofCode pairs.2.2.2 (by decide +kernel)
  exact ⟨h1.trans (by decide +kernel), h2.trans (by decide +kernel)⟩

@[expose] noncomputable def cgl (l : ℕ) : H6 := if l = 0 then cg0 else cg1

theorem enc_cgl : ∀ l < 2, KY (Nat.add 13 l) = enc6 (cgl l) ∧ KY (Nat.add 15 l) = enc6 (cgl l)⁻¹ := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨enc_cg0.1.symm, enc_cg0.2.symm⟩
  · exact ⟨enc_cg1.1.symm, enc_cg1.2.symm⟩

structure Hyp (z : Fin 3 → H6) (s : H6) : Prop where
  hz : ∀ i, mat6 (z i) = dec6 (zCode i)
  hs : mat6 s = dec6 srC

variable {z : Fin 3 → H6} {s : H6}

theorem Hyp.es (H : Hyp z s) : enc6 s = KY 0 := by
  rw [enc6_of H.hs (by decide +kernel)]; decide +kernel

theorem Hyp.ez0 (H : Hyp z s) : enc6 (z 0) = KY 1 := by
  rw [enc6_of (H.hz 0) (by decide +kernel)]; decide +kernel

theorem Hyp.ez1 (H : Hyp z s) : enc6 (z 1) = KY 2 := by
  rw [enc6_of (H.hz 1) (by decide +kernel)]; decide +kernel

theorem Hyp.ez2 (H : Hyp z s) : enc6 (z 2) = KY 3 := by
  rw [enc6_of (H.hz 2) (by decide +kernel)]; decide +kernel

theorem Hyp.eu (H : Hyp z s) : enc6 (z 1 * z 2) = KY 4 := by
  rw [emul, H.ez1, H.ez2]; decide +kernel

theorem Hyp.ew (H : Hyp z s) : enc6 (z 1 * z 2 ^ 2) = KY 5 := by
  rw [pow_two, emul, emul, H.ez1, H.ez2]; decide +kernel

theorem Hyp.ex2 (H : Hyp z s) : enc6 (z 0 * (z 1 * z 2)) = KY 6 := by
  rw [emul, H.ez0, H.eu]; decide +kernel

theorem Hyp.z_inv0 (H : Hyp z s) : (z 0)⁻¹ = z 0 * z 0 := inv_eq_sq H.ez0 (by decide +kernel)

theorem Hyp.ex3 (H : Hyp z s) : enc6 ((z 0)⁻¹ * (z 1 * z 2)) = KY 7 := by
  rw [H.z_inv0, emul, emul, H.ez0, H.eu]; decide +kernel

theorem Hyp.w_inv (H : Hyp z s) : (z 1 * z 2 ^ 2)⁻¹ = z 1 * z 2 ^ 2 * (z 1 * z 2 ^ 2) :=
  inv_eq_sq H.ew (by decide +kernel)

theorem Hyp.ew2 (H : Hyp z s) : enc6 (z 1 * z 2 ^ 2 * (z 1 * z 2 ^ 2)) = KY 8 := by
  rw [emul, H.ew]; decide +kernel

theorem Hyp.s_sq (H : Hyp z s) : s * s = 1 :=
  eq_of_enc (by rw [emul, H.es, enc_one]; decide +kernel)

theorem Hyp.s_inv (H : Hyp z s) : s⁻¹ = s := inv_eq_of_mul_eq_one_right H.s_sq

theorem Hyp.rels (H : Hyp z s) :
    s * s = 1 ∧ s ≠ 1 ∧ s * z 0 = z 0 * s ∧ s * (z 1 * z 2) = z 1 * z 2 * s ∧
      s * (z 1 * z 2 ^ 2) * s⁻¹ = (z 1 * z 2 ^ 2)⁻¹ := by
  refine ⟨H.s_sq, ne_of_enc H.es enc_one (by decide +kernel), comm_of H.es H.ez0 (by decide +kernel),
    comm_of H.es H.eu (by decide +kernel), ?_⟩
  rw [H.s_inv, H.w_inv]
  generalize hw : z 1 * z 2 ^ 2 = w
  have ew : enc6 w = KY 5 := by rw [← hw]; exact H.ew
  exact eq_of_enc (by simp only [emul, H.es, ew]; decide +kernel)

@[expose] noncomputable def csl (i : ℕ) : H6 :=
  ![cg0, cg1, cg0⁻¹, cg1⁻¹] ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

theorem enc_csl : ∀ l < 8, KY (Nat.add 13 (Nat.mod l 4)) = enc6 (csl l) := by
  intro l _
  change KY (13 + l % 4) = enc6 (csl l)
  unfold csl
  rcases (by omega : l % 4 = 0 ∨ l % 4 = 1 ∨ l % 4 = 2 ∨ l % 4 = 3) with e | e | e | e <;>
    simp only [e]
  · exact enc_cg0.1.symm
  · exact enc_cg1.1.symm
  · exact enc_cg0.2.symm
  · exact enc_cg1.2.symm

theorem Hyp.cg0_mem (H : Hyp z s) : cg0 ∈ Subgroup.centralizer ({s} : Set H6) :=
  mem_cen_of enc_cg0.1 H.es (by decide +kernel)

theorem Hyp.cg1_mem (H : Hyp z s) : cg1 ∈ Subgroup.centralizer ({s} : Set H6) :=
  mem_cen_of enc_cg1.1 H.es (by decide +kernel)

theorem Hyp.cgl_mem (H : Hyp z s) (l : ℕ) : cgl l ∈ Subgroup.centralizer ({s} : Set H6) := by
  unfold cgl
  split_ifs
  · exact H.cg0_mem
  · exact H.cg1_mem

theorem Hyp.csl_mem (H : Hyp z s) (i : ℕ) : csl i ∈ Subgroup.centralizer ({s} : Set H6) := by
  unfold csl
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with e | e | e | e <;>
    simp only [e]
  · exact H.cg0_mem
  · exact H.cg1_mem
  · exact inv_mem H.cg0_mem
  · exact inv_mem H.cg1_mem

theorem Hyp.wordE_mem (H : Hyp z s) :
    ∀ n v, wordE csl n v ∈ Subgroup.centralizer ({s} : Set H6)
  | 0, _ => one_mem _
  | n + 1, v => mul_mem (H.csl_mem _) (H.wordE_mem n _)

@[expose] noncomputable def tgs : List H6 :=
  (List.range 4).map fun l => wordE csl (Nat.mod (TW l) 16) (Nat.div (TW l) 16)

theorem tgs_enc : ∀ j < tgs.length, TG j = enc6 (tgs.getD j 1) := by
  intro j hj
  have hl : tgs.length = 4 := by simp [tgs]
  rw [hl] at hj
  have hw := (allN_iff _ _).1 (chTw.all 0 (by norm_num)) j hj
  rw [Nat.eq_of_beq_eq_true hw,
    wordF_enc (L := fun i => KY (Nat.add 13 (Nat.mod i 4))) (fun l hl => enc_csl l hl)]
  simp only [tgs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

@[expose] noncomputable def TSub : Subgroup H6 := Subgroup.closure {g | g ∈ tgs}

theorem tree_T : ∀ k < 512, treeAt MULF ONE TG tgs.length TE TP k = true :=
  forall_of_chunks 256 2 _ fun c hc => chTr.all c hc

theorem sort_T : ∀ i < 512, sortAt 512 TE TS i = true :=
  (allR_iff _ _ _).1 (chSr.all 0 (by norm_num)) |> fun h i hi => h i (Nat.zero_le _) hi

theorem closed_T : ∀ k < 512, closedAt MULF TG tgs.length 512 TE TC k = true :=
  forall_of_chunks 256 2 _ fun c hc => chCl.all c hc

theorem T_facts :
    (∀ k < 512, ∃ g ∈ TSub, enc6 g = TE k) ∧ Nat.card TSub = 512 ∧
      ∀ g ∈ TSub, ∃ k < 512, enc6 g = TE k := by
  obtain ⟨h1, -, h3⟩ := clos_card_proved enc6_enc tgs tgs_enc (by norm_num) tree_T sort_T
  obtain ⟨h4, h5⟩ := h3 closed_T
  exact ⟨h1, h4, h5⟩

theorem Hyp.T_le (H : Hyp z s) : TSub ≤ Subgroup.centralizer ({s} : Set H6) := by
  rw [TSub, Subgroup.closure_le]
  intro g hg
  simp only [tgs, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
  obtain ⟨l, -, rfl⟩ := hg
  exact H.wordE_mem _ _

theorem z_parts :
    (∀ k < 9, treeAt MULF ONE (fun l => KY (Nat.add 1 (Nat.mul 3 l))) 2 EZ PZ k = true) ∧
    (∀ i < 9, sortAt 9 EZ SZ i = true) ∧
    (∀ k < 9, closedAt MULF (fun l => KY (Nat.add 1 (Nat.mul 3 l))) 2 9 EZ CZ k = true) := by
  have h : zB 0 = true := chZ.all 0 (by norm_num)
  unfold zB at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h3⟩ := andB_eq_true h
  have r : ∀ {n : ℕ} {f : ℕ → Bool}, allR 0 n f = true → ∀ i < n, f i = true :=
    fun h i hi => (allR_iff _ _ _).1 h i (Nat.zero_le _) (by omega)
  exact ⟨r h1, r h2, r h3⟩

@[expose] noncomputable def E9 (z : Fin 3 → H6) : Subgroup H6 :=
  Subgroup.closure {g | g ∈ [z 0, z 1 * z 2]}

theorem Hyp.E9_facts (H : Hyp z s) :
    (∀ k < 9, ∃ g ∈ E9 z, enc6 g = EZ k) ∧ Nat.card (E9 z) = 9 := by
  have hG : ∀ j < [z 0, z 1 * z 2].length,
      KY (Nat.add 1 (Nat.mul 3 j)) = enc6 ([z 0, z 1 * z 2].getD j 1) := by
    intro j hj
    have hj' : j < 2 := by simpa using hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact H.ez0.symm
    · exact H.eu.symm
  obtain ⟨h1, -, h3⟩ := clos_card_proved enc6_enc [z 0, z 1 * z 2] hG (by norm_num) z_parts.1
    z_parts.2.1
  exact ⟨h1, (h3 z_parts.2.2).1⟩

theorem Hyp.E9_le (H : Hyp z s) : E9 z ≤ Subgroup.centralizer ({s} : Set H6) := by
  rw [E9, Subgroup.closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rw [SetLike.mem_coe]
  rcases hg with rfl | rfl
  · exact mem_cen_of H.ez0 H.es (by decide +kernel)
  · exact mem_cen_of H.eu H.es (by decide +kernel)

theorem Hyp.card_cen_le (H : Hyp z s) :
    Nat.card (Subgroup.centralizer ({s} : Set H6)) * 315 ≤ Nat.card H6 := by
  have hob : sB 0 = true := chS.all 0 (by norm_num)
  unfold sB at hob
  obtain ⟨h1, h2⟩ := andB_eq_true hob
  have ht := (allR_iff _ _ _).1 h1
  have hs := (allR_iff _ _ _).1 h2
  have hc := conj_tree (G := fun l => if l = 0 then ha else hb) (x₀ := s) (N := 315) (E := SE)
    (PA := SP) (g := fun l => KY (Nat.add 9 l)) (gi := fun l => KY (Nat.add 11 l))
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
    (fun k : Fin 315 => h k * s * (h k)⁻¹) ?_ fun k => ⟨h k, rfl⟩
  intro a b e
  exact Fin.ext (hd a a.2 b b.2 (by rw [hh a a.2, hh b b.2]; exact congrArg enc6 e))

theorem Hyp.card_cen (H : Hyp z s) : Nat.card (Subgroup.centralizer ({s} : Set H6)) = 4608 := by
  have h1 := H.card_cen_le
  rw [card_H6] at h1
  have d1 : 512 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) := by
    rw [← T_facts.2.1]
    exact Subgroup.card_dvd_of_le H.T_le
  have d2 : 9 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) := by
    rw [← H.E9_facts.2]
    exact Subgroup.card_dvd_of_le H.E9_le
  have d : 4608 ∣ Nat.card (Subgroup.centralizer ({s} : Set H6)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have hpos : 0 < Nat.card (Subgroup.centralizer ({s} : Set H6)) := Nat.card_pos
  obtain ⟨m, hm⟩ := d
  rw [hm] at h1 hpos ⊢
  have : m ≤ 1 := by nlinarith
  have : m ≠ 0 := by rintro rfl; simp at hpos
  obtain rfl : m = 1 := by omega
  rfl

theorem Hyp.le_of_card (H : Hyp z s) {R X : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6))
    (hX : X ≤ Subgroup.centralizer ({s} : Set H6)) (hXc : Nat.card X = 512) : R ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : IsPGroup 2 X := IsPGroup.of_card (n := 9) (by rw [hXc]; norm_num)
  have hsup : IsPGroup 2 (X ⊔ R : Subgroup H6) :=
    IsPGroup.to_sup_of_normal_right' hX2 h2 (hX.trans hN)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(X ⊔ R))).mp hsup
  have hd : 2 ^ k ∣ 512 * 9 := by
    rw [← hk, show 512 * 9 = Nat.card (Subgroup.centralizer ({s} : Set H6)) by
      rw [H.card_cen]]
    exact Subgroup.card_dvd_of_le (sup_le hX hR)
  have hk' : 2 ^ k ∣ 512 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 9)).dvd_of_dvd_mul_right hd
  have hle : Nat.card (X ⊔ R : Subgroup H6) ≤ Nat.card X := by
    rw [hk, hXc]
    exact Nat.le_of_dvd (by norm_num) hk'
  have heq : X = X ⊔ R := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [heq]
  exact le_sup_right

theorem in_parts : CI 0 < 9 ∧ CI 1 < 9 ∧ EZ (CI 0) = KY 6 ∧ MULF (EZ (CI 0)) (EZ (CI 1)) = ONE ∧
    ∀ k < 512, interN 512 128 TE TS (rt 2) NB (EZ (CI 0)) (EZ (CI 1)) k = true := by
  have h0 : inB 0 = true := chIn.all 0 (by norm_num)
  unfold inB at h0
  obtain ⟨ha, -⟩ := andB_eq_true h0
  obtain ⟨h1, ha⟩ := andB_eq_true ha
  obtain ⟨h2, ha⟩ := andB_eq_true ha
  obtain ⟨h3, h4⟩ := andB_eq_true ha
  refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    ?_⟩
  have h := forall_of_chunks 256 2 _ (fun c hc => by
    have e := chIn.all c hc
    unfold inB at e
    exact (andB_eq_true e).2)
  exact fun k hk => h k (by omega)

theorem Hyp.code_R3 (H : Hyp z s) {R : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) :
    ∀ x ∈ R, ∃ j < 128, enc6 x = rt 2 j := by
  obtain ⟨c0, c1, ec0, ec01, hin⟩ := in_parts
  set c := z 0 * (z 1 * z 2) with hc
  have hcC : c ∈ Subgroup.centralizer ({s} : Set H6) :=
    H.E9_le (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  have enc_c : enc6 c = EZ (CI 0) := by rw [ec0]; exact H.ex2
  obtain ⟨ci, -, eci⟩ := H.E9_facts.1 _ c1
  have hci : ci = c⁻¹ := inv_of_mul enc_c eci ec01
  rw [hci] at eci
  have hT := H.le_of_card hR h2 hN H.T_le T_facts.2.1
  have hT' := H.le_of_card hR h2 hN (X := TSub.map (MulAut.conj c).toMonoidHom)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hcC (H.T_le hy)) (inv_mem hcC))
    (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, T_facts.2.1])
  intro x hx
  obtain ⟨k, hk, ek⟩ := T_facts.2.2 x (hT hx)
  obtain ⟨y, hy, hyx⟩ := hT' hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  obtain ⟨k', hk', ek'⟩ := T_facts.2.2 y hy
  have h := hin k hk
  simp only [interN, letB_eq] at h
  cases hb : Nat.ble 1048576 (NB k)
  · rw [hb] at h
    obtain ⟨hr, h⟩ := andB_eq_true h
    obtain ⟨hlo, hhi⟩ := andB_eq_true h
    have hr' : NB k ≤ 512 := Nat.ble_eq.mp hr
    have hy' : MULF (MULF (EZ (CI 1)) (TE k)) (EZ (CI 0)) = enc6 y := by
      rw [← ek, ← eci, ← enc_c, ← emul, ← emul, ← hyx]
      exact congrArg enc6 (by group)
    have hne := not_mem_of_gap
      (y := MULF (MULF (EZ (CI 1)) (TE k)) (EZ (CI 0))) sort_T hr'
      (fun h0 => by
        have h' := Nat.blt_eq.mp (impB_eq_true hlo (Nat.blt_eq.mpr h0))
        rwa [Nat.pred_eq_sub_one] at h')
      (fun h1 => Nat.blt_eq.mp (impB_eq_true hhi (Nat.blt_eq.mpr h1))) k' hk'
    exact absurd (ek'.symm.trans hy'.symm) hne
  · rw [hb] at h
    obtain ⟨hj, he⟩ := andB_eq_true h
    exact ⟨_, Nat.blt_eq.mp hj, ek.trans (Nat.eq_of_beq_eq_true he).symm⟩

theorem Hyp.card_le (H : Hyp z s) {R : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) :
    Nat.card R ≤ 128 := by
  have hc := H.code_R3 hR h2 hN
  choose! j hj ej using hc
  have hinj : Function.Injective fun x : R => (⟨j x, hj x x.2⟩ : Fin 128) := by
    intro a b e
    have e' : j a = j b := congrArg Fin.val e
    exact Subtype.ext (eq_of_enc (by rw [ej a a.2, ej b b.2, e']))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Fin 128), Fintype.card_fin] at this

end CertificateChecks.KernelMisc.Sp6SR.Facts

end
