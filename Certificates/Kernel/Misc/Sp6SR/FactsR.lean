module

public import Certificates.Kernel.Misc.Sp6SR.Facts
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6SR.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Sp6SR
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6SR
open CertificateChecks.KernelMisc.Sp6Transv.Facts (orB_true)
open CFSG.KC.LQT.P (letB)
open CFSG.KC.Ord (andB orB)

variable {z : Fin 3 → H6} {s : H6}

open Classical in
@[expose] noncomputable def eltOf (n : ℕ) : H6 := if h : ∃ g : H6, enc6 g = n then h.choose else 1

theorem enc_eltOf {n : ℕ} (h : ∃ g : H6, enc6 g = n) : enc6 (eltOf n) = n := by
  rw [eltOf, dif_pos h]
  exact h.choose_spec

theorem eltOf_eq {g : H6} {n : ℕ} (h : enc6 g = n) : eltOf n = g :=
  eq_of_enc ((enc_eltOf ⟨g, h⟩).trans h.symm)

theorem rall {n : ℕ} {f : ℕ → Bool} (h : allR 0 n f = true) : ∀ i < n, f i = true :=
  fun i hi => (allR_iff _ _ _).1 h i (Nat.zero_le _) (by omega)

theorem conj_tree_mem {K : Subgroup H6} {g gi : ℕ → ℕ} {G : ℕ → H6}
    (hg : ∀ l < 2, g l = enc6 (G l)) (hgi : ∀ l < 2, gi l = enc6 (G l)⁻¹) (hK : ∀ l < 2, G l ∈ K)
    {x₀ : H6} {N : ℕ} {E PA : ℕ → ℕ}
    (ht : ∀ k < N, treeAt (fun x l => conjF (g l) (gi l) x) (enc6 x₀) (fun l => l) 2 E PA k =
      true) :
    ∀ k < N, ∃ h ∈ K, E k = enc6 (h * x₀ * h⁻¹) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h : Nat.beq (E 0) (enc6 x₀) = true := ht 0 hk
      exact ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact Nat.eq_of_beq_eq_true h⟩
    | succ k =>
      have h := ht (k + 1) hk
      simp only [treeAt, letB_eq] at h
      obtain ⟨hp, h⟩ := andB_eq_true h
      obtain ⟨hl, he⟩ := andB_eq_true h
      have hp' := Nat.blt_eq.mp hp
      have hl' := Nat.blt_eq.mp hl
      obtain ⟨u, hu, eu⟩ := ih _ hp' (by omega)
      refine ⟨G (Nat.shiftRight (PA (k + 1)) 24) * u, mul_mem (hK _ hl') hu, ?_⟩
      rw [Nat.eq_of_beq_eq_true he, conjF, eu, hg _ hl', hgi _ hl', ← enc6_enc.enc_mul,
        ← enc6_enc.enc_mul]
      have e : ∀ a : H6, a * (u * x₀ * u⁻¹) * a⁻¹ = a * u * x₀ * (a * u)⁻¹ := fun a => by group
      rw [e]

theorem of_facts : OF 0 = 0 ∧ OF 7 = 126 ∧ (∀ j < 7, OF j < OF (j + 1) ∧ OT j < 3) ∧
    (∀ t < 3, OT (PP t) = t ∧ PP t < 7) ∧ (∀ j < 8, OF j ≤ 126) := by
  decide +kernel

theorem orb_of : ∀ k < 126, ∃ j < 7, OF j ≤ k ∧ k < OF (j + 1) := by
  decide +kernel

theorem ro_facts : RO 0 = 0 ∧ RO 1 = 8 ∧ RO 2 = 40 ∧ RO 3 = 168 := by
  decide +kernel

theorem rg_facts : ∀ t < 3, 0 < NG t ∧ RG (GO t) = 126 := by
  decide +kernel

theorem rn_pos : ∀ t < 3, 0 < RO (t + 1) - RO t := by
  decide +kernel

theorem oc_126 : oc 126 = KY 0 := rfl

theorem oc_ne {k : ℕ} (hk : k ≠ 126) : oc k = OE k := by
  have h : Nat.beq k 126 = false := by
    cases e : Nat.beq k 126
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk
  unfold oc ocF
  rw [h]

theorem orb_parts (j : ℕ) (hj : j < 7) :
    (RI j < 512 ∧ OE (OF j) = TE (RI j)) ∧
    (∀ k < OF (j + 1) - OF j, treeAt cstep (OE (OF j)) (fun l => l) 2 (fun k => OE (OF j + k))
      (fun k => OP (OF j + k)) k = true) ∧
    (∀ k < OF (j + 1) - OF j, MI (OF j + k) < RO (OT j + 1) - RO (OT j) ∧
      RE (RO (OT j) + MI (OF j + k)) = OE (OF j + k)) ∧
    (j ≠ PP (OT j) → digitsIn (OF j) (OF (j + 1)) (SW j % 16) (SW j / 16) = true ∧
      wordO oc (SW j % 16) (SW j / 16) = OE (OF (PP (OT j)))) := by
  have h : orbAt j = true := (allN_iff _ _).1 (chOb.all 0 (by norm_num)) j hj
  unfold orbAt at h
  simp only [letB_eq] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h1a, h1b⟩ := andB_eq_true h1
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h4⟩ := andB_eq_true h
  refine ⟨⟨Nat.blt_eq.mp h1a, Nat.eq_of_beq_eq_true h1b⟩, rall h2, fun k hk => ?_, fun hne => ?_⟩
  · have e := rall h3 k hk
    unfold memAt at e
    obtain ⟨e1, e2⟩ := andB_eq_true e
    exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩
  · have hb : Bool.not (Nat.beq j (PP (OT j))) = true := by
      cases e : Nat.beq j (PP (OT j))
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hne
    obtain ⟨e1, e2⟩ := andB_eq_true (impB_eq_true h4 hb)
    exact ⟨e1, Nat.eq_of_beq_eq_true e2⟩

theorem Hyp.orb_conj (H : Hyp z s) (j : ℕ) (hj : j < 7) :
    ∃ x₀ : H6, ∀ k < OF (j + 1) - OF j, ∃ h ∈ Subgroup.centralizer ({s} : Set H6),
      OE (OF j + k) = enc6 (h * x₀ * h⁻¹) := by
  obtain ⟨⟨hr, hroot⟩, htree, -, -⟩ := orb_parts j hj
  obtain ⟨x₀, -, ex₀⟩ := T_facts.1 _ hr
  rw [hroot, ← ex₀] at htree
  exact ⟨x₀, conj_tree_mem (g := fun l => KY (Nat.add 13 l)) (gi := fun l => KY (Nat.add 15 l))
    (fun l hl => (enc_cgl l hl).1) (fun l hl => (enc_cgl l hl).2) (fun l _ => H.cgl_mem l)
    htree⟩

theorem Hyp.orb_mem (H : Hyp z s) {R : Subgroup H6}
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) {j : ℕ}
    (hj : j < 7) {k k' : ℕ} (hk : k < OF (j + 1) - OF j) (hk' : k' < OF (j + 1) - OF j) {x : H6}
    (hx : x ∈ R) (ex : enc6 x = OE (OF j + k)) : ∃ y ∈ R, enc6 y = OE (OF j + k') := by
  obtain ⟨x₀, hc⟩ := H.orb_conj j hj
  obtain ⟨h, hh, eh⟩ := hc k hk
  obtain ⟨h', hh', eh'⟩ := hc k' hk'
  have hxe : x = h * x₀ * h⁻¹ := eq_of_enc (ex.trans eh)
  have hx₀ : x₀ ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (hN (inv_mem hh)) x).mp hx
    rw [hxe] at this
    simpa [mul_assoc] using this
  exact ⟨h' * x₀ * h'⁻¹, (Subgroup.mem_normalizer_iff.mp (hN hh') x₀).mp hx₀, eh'.symm⟩

theorem wordO_mem {R : Subgroup H6} {O : ℕ → ℕ} {lo hi : ℕ}
    (hd : ∀ d, d = 126 ∨ (lo ≤ d ∧ d < hi) → ∃ g ∈ R, enc6 g = O d) :
    ∀ n v, digitsIn lo hi n v = true → ∃ g ∈ R, enc6 g = wordO O n v
  | 0, _, _ => ⟨1, one_mem _, enc_one⟩
  | n + 1, v, h => by
    change letB (Nat.mod v 128) (fun d => andB (orB (Nat.beq d 126)
      (andB (Nat.ble lo d) (Nat.blt d hi))) (digitsIn lo hi n (Nat.div v 128))) = true at h
    rw [letB_eq] at h
    obtain ⟨h1, h2⟩ := andB_eq_true h
    obtain ⟨g, hg, eg⟩ := wordO_mem hd n _ h2
    have hd' : Nat.mod v 128 = 126 ∨ (lo ≤ Nat.mod v 128 ∧ Nat.mod v 128 < hi) := by
      rcases orB_true h1 with e | e
      · exact Or.inl (Nat.eq_of_beq_eq_true e)
      · obtain ⟨e1, e2⟩ := andB_eq_true e
        exact Or.inr ⟨Nat.le_of_ble_eq_true e1, Nat.blt_eq.mp e2⟩
    obtain ⟨g', hg', eg'⟩ := hd _ hd'
    refine ⟨g' * g, mul_mem hg' hg, ?_⟩
    change enc6 (g' * g) = MULF (O (Nat.mod v 128)) (wordO O n (Nat.div v 128))
    rw [emul, eg, eg']

@[expose] noncomputable def rgens (t : ℕ) : List H6 :=
  (List.range (NG t)).map fun l => eltOf (rgen t l)

@[expose] noncomputable def RSub (t : ℕ) : Subgroup H6 := Subgroup.closure {g | g ∈ rgens t}

theorem rgens_length (t : ℕ) : (rgens t).length = NG t := by simp [rgens]

theorem r_parts (t : ℕ) (ht : t < 3) :
    (∀ l < NG t, RG (GO t + l) = 126 ∨
      (OF (PP t) ≤ RG (GO t + l) ∧ RG (GO t + l) < OF (PP t + 1))) ∧
    (∀ k < RO (t + 1) - RO t, treeAt MULF ONE (rgen t) (rgens t).length (rt t)
      (fun k => RP (RO t + k)) k = true) ∧
    (∀ i < RO (t + 1) - RO t, sortAt (RO (t + 1) - RO t) (rt t) (fun k => RS (RO t + k)) i =
      true) ∧
    (∀ k < RO (t + 1) - RO t, closedAt MULF (rgen t) (rgens t).length (RO (t + 1) - RO t) (rt t)
      (fun i => RC (CO t + i)) k = true) := by
  have h : rAt t = true := chR.all t ht
  unfold rAt at h
  simp only [letB_eq] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h4⟩ := andB_eq_true h
  rw [rgens_length]
  refine ⟨fun l hl => ?_, rall h2, rall h3, rall h4⟩
  rcases orB_true ((allN_iff _ _).1 h1 l hl) with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · obtain ⟨e1, e2⟩ := andB_eq_true e
    exact Or.inr ⟨Nat.le_of_ble_eq_true e1, Nat.blt_eq.mp e2⟩

theorem Hyp.rgen_ex (H : Hyp z s) (t : ℕ) (ht : t < 3) :
    ∀ l < NG t, ∃ g : H6, enc6 g = rgen t l := by
  intro l hl
  obtain ⟨-, -, -, hpp, -⟩ := of_facts
  obtain ⟨-, hp⟩ := hpp t ht
  rcases (r_parts t ht).1 l hl with e | ⟨e1, e2⟩
  · refine ⟨s, ?_⟩
    change enc6 s = oc (RG (GO t + l))
    rw [e, oc_126, H.es]
  · have h126 : RG (GO t + l) ≠ 126 := by
      have := of_facts.2.2.2.2 (PP t + 1) (by omega)
      omega
    obtain ⟨x₀, hc⟩ := H.orb_conj _ hp
    obtain ⟨h, -, eh⟩ := hc (RG (GO t + l) - OF (PP t)) (by omega)
    refine ⟨h * x₀ * h⁻¹, ?_⟩
    change enc6 _ = oc (RG (GO t + l))
    have e : OF (PP t) + (RG (GO t + l) - OF (PP t)) = RG (GO t + l) := by omega
    rw [oc_ne h126, ← eh, e]

theorem getD_map_range {n j : ℕ} (f : ℕ → H6) (hj : j < n) :
    ((List.range n).map f).getD j 1 = f j := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

theorem Hyp.rgens_enc (H : Hyp z s) (t : ℕ) (ht : t < 3) :
    ∀ j < (rgens t).length, rgen t j = enc6 ((rgens t).getD j 1) := by
  intro j hj
  rw [rgens_length] at hj
  have e : (rgens t).getD j 1 = eltOf (rgen t j) := getD_map_range _ hj
  rw [e]
  exact (enc_eltOf (H.rgen_ex t ht j hj)).symm

theorem Hyp.R_facts (H : Hyp z s) (t : ℕ) (ht : t < 3) :
    (∀ k < RO (t + 1) - RO t, ∃ g ∈ RSub t, enc6 g = rt t k) ∧
    Nat.card (RSub t) = RO (t + 1) - RO t ∧
    (∀ g ∈ RSub t, ∃ k < RO (t + 1) - RO t, enc6 g = rt t k) ∧
    (∀ i < RO (t + 1) - RO t, ∀ j < RO (t + 1) - RO t, rt t i = rt t j → i = j) := by
  obtain ⟨-, h2, h3, h4⟩ := r_parts t ht
  have hG := H.rgens_enc t ht
  have hpos : 0 < RO (t + 1) - RO t := rn_pos t ht
  obtain ⟨e1, -, e3⟩ := clos_card_proved enc6_enc (rgens t) hG hpos h2 h3
  obtain ⟨e4, e5⟩ := e3 h4
  exact ⟨e1, e4, e5, sort_distinct_proved h3⟩

theorem Hyp.s_mem_R (H : Hyp z s) (t : ℕ) (ht : t < 3) : s ∈ RSub t := by
  obtain ⟨hpos, hrg⟩ := rg_facts t ht
  have e : eltOf (rgen t 0) = s := by
    refine eltOf_eq ?_
    change enc6 s = oc (RG (GO t + 0))
    rw [Nat.add_zero, hrg, oc_126, H.es]
  rw [← e]
  exact Subgroup.subset_closure (List.mem_map.2 ⟨0, List.mem_range.2 hpos, rfl⟩)

theorem Hyp.mem_R_of (H : Hyp z s) {t : ℕ} (ht : t < 3) {k : ℕ} (hk : k < RO (t + 1) - RO t)
    {x : H6} (ex : enc6 x = rt t k) : x ∈ RSub t := by
  obtain ⟨g, hg, eg⟩ := (H.R_facts t ht).1 k hk
  rwa [eq_of_enc (ex.trans eg.symm)]

theorem Hyp.tag_mem (H : Hyp z s) {R : Subgroup H6}
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) (hs : s ∈ R)
    {j : ℕ} (hj : j < 7) {k : ℕ} (hk1 : OF j ≤ k) (hk2 : k < OF (j + 1)) {x : H6} (hx : x ∈ R)
    (ex : enc6 x = OE k) : x ∈ RSub (OT j) ∧ RSub (OT j) ≤ R := by
  obtain ⟨-, -, hfac, hpp, -⟩ := of_facts
  have ht : OT j < 3 := (hfac j hj).2
  obtain ⟨hpt, hp⟩ := hpp _ ht
  obtain ⟨-, -, hmem, hsw⟩ := orb_parts j hj
  have hk' : k - OF j < OF (j + 1) - OF j := by omega
  have ek : OF j + (k - OF j) = k := by omega
  have ex' : enc6 x = OE (OF j + (k - OF j)) := by rw [ek]; exact ex
  refine ⟨?_, ?_⟩
  · obtain ⟨m1, m2⟩ := hmem _ hk'
    exact H.mem_R_of ht m1 (ex'.trans m2.symm)
  · have hp1 : OF (PP (OT j)) < OF (PP (OT j) + 1) := (hfac _ hp).1
    have hroot : ∃ y ∈ R, enc6 y = OE (OF (PP (OT j)) + 0) := by
      by_cases hjp : j = PP (OT j)
      · rw [← hjp]
        exact H.orb_mem hN hj hk' (by omega) hx ex'
      · obtain ⟨hdig, hw⟩ := hsw hjp
        have hle := of_facts.2.2.2.2 (j + 1) (by omega)
        obtain ⟨y, hy, ey⟩ := wordO_mem (R := R) (O := oc) (lo := OF j) (hi := OF (j + 1))
          (fun d hd => by
            rcases hd with rfl | ⟨d1, d2⟩
            · exact ⟨s, hs, by rw [oc_126, H.es]⟩
            · rw [oc_ne (by omega)]
              have e : OF j + (d - OF j) = d := by omega
              rw [← e]
              exact H.orb_mem hN hj hk' (by omega) hx ex') _ _ hdig
        exact ⟨y, hy, by rw [ey, hw, Nat.add_zero]⟩
    obtain ⟨y, hy, ey⟩ := hroot
    rw [RSub, Subgroup.closure_le]
    intro g hg
    simp only [rgens, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    rcases (r_parts _ ht).1 l hl with e | ⟨e1, e2⟩
    · have e' : eltOf (rgen (OT j) l) = s := by
        refine eltOf_eq ?_
        change enc6 s = oc (RG (GO (OT j) + l))
        rw [e, oc_126, H.es]
      rw [SetLike.mem_coe, e']
      exact hs
    · have h126 : RG (GO (OT j) + l) ≠ 126 := by
        have := of_facts.2.2.2.2 (PP (OT j) + 1) (by omega)
        omega
      obtain ⟨y', hy', ey'⟩ := H.orb_mem hN hp (by omega : 0 < OF (PP (OT j) + 1) - OF (PP (OT j)))
        (k' := RG (GO (OT j) + l) - OF (PP (OT j))) (by omega) hy ey
      have e' : eltOf (rgen (OT j) l) = y' := by
        refine eltOf_eq ?_
        change enc6 y' = oc (RG (GO (OT j) + l))
        have e : OF (PP (OT j)) + (RG (GO (OT j) + l) - OF (PP (OT j))) = RG (GO (OT j) + l) := by
          omega
        rw [oc_ne h126, ey', e]
      rw [SetLike.mem_coe, e']
      exact hy'

theorem cv_all : ∀ i < 128, rt 2 i = ONE ∨ rt 2 i = KY 0 ∨ (CV i < 126 ∧ OE (CV i) = rt 2 i) := by
  intro i hi
  have h := (allN_iff _ _).1 (chCv.all 0 (by norm_num)) i hi
  simp only [letB_eq] at h
  rcases orB_true h with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  rcases orB_true e with e | e
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e))
  · obtain ⟨e1, e2⟩ := andB_eq_true e
    exact Or.inr (Or.inr ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩)

theorem mx_parts : MX 0 < 8 ∧ MX 1 < 32 ∧ MX 3 < 7 ∧ MULF (rt 0 (MX 0)) (rt 1 (MX 1)) = OE (MX 2) ∧
    OF (MX 3) ≤ MX 2 ∧ MX 2 < OF (MX 3 + 1) ∧ OT (MX 3) = 2 := by
  have h : mxB 0 = true := chMx.all 0 (by norm_num)
  unfold mxB at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h7⟩ := andB_eq_true h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4,
    Nat.le_of_ble_eq_true h5, Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h7⟩

theorem Hyp.le_R3 (H : Hyp z s) {R : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) :
    R ≤ RSub 2 := by
  intro x hx
  obtain ⟨j, hj, ej⟩ := H.code_R3 hR h2 hN x hx
  have e : RO (2 + 1) - RO 2 = 128 := by decide +kernel
  exact H.mem_R_of (t := 2) (by norm_num) (by rw [e]; exact hj) ej

theorem Hyp.normal_cases (H : Hyp z s) {R : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) (hs : s ∈ R) :
    R = Subgroup.zpowers s ∨ R = RSub 0 ∨ R = RSub 1 ∨ R = RSub 2 := by
  have h3 := H.le_R3 hR h2 hN
  have htag : ∀ q ∈ R, q = 1 ∨ q = s ∨ ∃ j < 7, q ∈ RSub (OT j) ∧ RSub (OT j) ≤ R := by
    intro q hq
    obtain ⟨i, hi, ei⟩ := H.code_R3 hR h2 hN q hq
    rcases cv_all i hi with e | e | ⟨hc, e⟩
    · exact Or.inl (eq_of_enc (by rw [ei, e, enc_one]))
    · exact Or.inr (Or.inl (eq_of_enc (by rw [ei, e, H.es])))
    · obtain ⟨j, hj, hj1, hj2⟩ := orb_of _ hc
      exact Or.inr (Or.inr ⟨j, hj, H.tag_mem hN hs hj hj1 hj2 hq (ei.trans e.symm)⟩)
  have hot : ∀ j < 7, OT j = 0 ∨ OT j = 1 ∨ OT j = 2 := fun j hj => by
    have := (of_facts.2.2.1 j hj).2
    omega
  by_cases hR3 : RSub 2 ≤ R
  · exact Or.inr (Or.inr (Or.inr (le_antisymm h3 hR3)))
  obtain ⟨m0, m1, m3, mul, m21, m22, mt⟩ := mx_parts
  obtain ⟨r0, r1, r2, r3⟩ := ro_facts
  by_cases h1 : RSub 0 ≤ R <;> by_cases h2' : RSub 1 ≤ R
  · exfalso
    obtain ⟨a, ha, ea⟩ := (H.R_facts 0 (by norm_num)).1 (MX 0) (by rw [r0, r1]; exact m0)
    obtain ⟨b, hb, eb⟩ := (H.R_facts 1 (by norm_num)).1 (MX 1) (by rw [r1, r2]; exact m1)
    have hab := (H.tag_mem hN hs m3 m21 m22 (mul_mem (h1 ha) (h2' hb))
      (by rw [emul, ea, eb, mul])).2
    rw [mt] at hab
    exact hR3 hab
  · refine Or.inr (Or.inl (le_antisymm (fun q hq => ?_) h1))
    rcases htag q hq with rfl | rfl | ⟨j, hj, hqj, hjR⟩
    · exact one_mem _
    · exact H.s_mem_R 0 (by norm_num)
    · rcases hot j hj with e | e | e <;> rw [e] at hqj hjR
      · exact hqj
      · exact absurd hjR h2'
      · exact absurd hjR hR3
  · refine Or.inr (Or.inr (Or.inl (le_antisymm (fun q hq => ?_) h2')))
    rcases htag q hq with rfl | rfl | ⟨j, hj, hqj, hjR⟩
    · exact one_mem _
    · exact H.s_mem_R 1 (by norm_num)
    · rcases hot j hj with e | e | e <;> rw [e] at hqj hjR
      · exact absurd hjR h1
      · exact hqj
      · exact absurd hjR hR3
  · refine Or.inl (le_antisymm (fun q hq => ?_) ((Subgroup.zpowers_le).mpr hs))
    rcases htag q hq with rfl | rfl | ⟨j, hj, hqj, hjR⟩
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
    · rcases hot j hj with e | e | e <;> rw [e] at hqj hjR
      · exact absurd hjR h1
      · exact absurd hjR h2'
      · exact absurd hjR hR3

end CertificateChecks.KernelMisc.Sp6SR.Facts

end
