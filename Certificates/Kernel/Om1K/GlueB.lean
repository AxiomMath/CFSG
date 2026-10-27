module

public import Certificates.Kernel.Om1K.Glue
public import Certificates.Kernel.Om1K.BJoin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CertificateChecks.KernelOm2 (pc2 wAK)
open CertificateChecks.KernelLC.E8 (RT FT NEG)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (OmGen.BadElt Om1Facts.E Om1Facts.G
  Om1Facts.Wp Om1Facts.t Om1Facts.ta Om1Facts.tb Om1Facts.tc Om1Facts.z Om1Facts.R Om1Facts.R'
  Om1Facts.i0' Om1Facts.j0' Om1Facts.D Om1Facts.TwinFail Om1Facts.tup)

theorem ip_pc {P Q i : Nat} (hi : i < 240) :
    pg 8 (mask 8) (pc2 P Q) i = pg 8 (mask 8) P (pg 8 (mask 8) Q i) :=
  PF.pg_pcomp (by norm_num) hi

theorem ipB (P i : Nat) : B.ip P i = pg 8 (mask 8) P i := rfl

theorem pr_ipn {P : Nat} {g : Equiv.Perm (Fin 240)} (h : PR P g) {p : Nat} (hp : p < 240) :
    pg 8 (mask 8) P p = (g ⟨p, hp⟩ : Nat) := h ⟨p, hp⟩

theorem pr_conj {A B C : Nat} {a b : Equiv.Perm (Fin 240)} (hA : PR A a) (hB : PR B b)
    (h : pc2 A B = pc2 C A) : PR C (a * b * a⁻¹) := by
  intro y
  have e : pg 8 (mask 8) (pc2 A B) (a⁻¹ y) = pg 8 (mask 8) (pc2 C A) (a⁻¹ y) := by rw [h]
  have hy : a (a⁻¹ y) = y := by simp
  rw [ip_pc (a⁻¹ y).2, ip_pc (a⁻¹ y).2, pr_ip hA (a⁻¹ y), hy, pr_ip hB, pr_ip hA] at e
  rw [← e]
  simp [Equiv.Perm.mul_apply]

theorem ip_lt {Q : Nat} (hQ : B.cnK Q = true) {i : Nat} (hi : i < 240) : pg 8 (mask 8) Q i < 240 :=
  Nat.blt_eq.mp (allN_spec (range_of_canonK hQ) i hi)

theorem pr_inv {P Q : Nat} {g : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : B.cnK Q = true)
    (h : pc2 P Q = pidn 240 8) : PR Q g⁻¹ := by
  intro x
  have hlt := ip_lt hQ x.2
  have e : pg 8 (mask 8) (pc2 P Q) x = pg 8 (mask 8) (pidn 240 8) x := by rw [h]
  rw [ip_pc x.2, pr_ip pr_pid] at e
  have e2 : g ⟨pg 8 (mask 8) Q x, hlt⟩ = x := Fin.ext ((pr_ip hP _).symm.trans e)
  have e3 : g⁻¹ x = ⟨pg 8 (mask 8) Q x, hlt⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact e2.symm
  change pg 8 (mask 8) Q x = ((g⁻¹ x : Fin 240) : Nat)
  rw [e3]

theorem pr_ne {P Q : Nat} {g h : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : PR Q h)
    (hne : B.NeAt P Q) : g ≠ h := by
  rintro rfl
  obtain ⟨p, hp, e⟩ := hne
  exact e ((hP ⟨p, hp⟩).trans (hQ ⟨p, hp⟩).symm)

theorem pr_inv_eq {P Q : Nat} {g h : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : PR Q h)
    (e : pc2 P Q = pidn 240 8) : h = g⁻¹ := by
  have h1 := pr_pc hP hQ
  rw [e] at h1
  exact eq_inv_of_mul_eq_one_right (pr_eq h1 pr_pid)

theorem eq_of_pr {P Q : Nat} {g : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : PR Q g)
    (cP : B.cnK P = true) (cQ : B.cnK Q = true) : P = Q := by
  obtain ⟨-, hw, hp0, -⟩ := PF.canon_facts cP
  obtain ⟨-, -, hq0, -⟩ := PF.canon_facts cQ
  exact PF.eq_of_fields (PF.w_pos hw) hp0 hq0 fun i hi =>
    (pr_ipn hP hi).trans (pr_ipn hQ hi).symm

theorem fld_le (r o m : Nat) : fld(r, o, m) ≤ m := Nat.and_le_right

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem i0_mem : Om1Facts.E wI0 ∈ Om1Facts.R := Subgroup.subset_closure (Set.mem_insert _ _)

theorem j0_mem : Om1Facts.E wJ0 ∈ Om1Facts.R :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem conj_R : ∀ r ∈ Om1Facts.R, Om1Facts.E wS1 * r * (Om1Facts.E wS1)⁻¹ ∈ Om1Facts.R' := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : Om1Facts.E wS1 * (x * y) * (Om1Facts.E wS1)⁻¹ =
        (Om1Facts.E wS1 * x * (Om1Facts.E wS1)⁻¹) * (Om1Facts.E wS1 * y * (Om1Facts.E wS1)⁻¹) := by
      group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : Om1Facts.E wS1 * x⁻¹ * (Om1Facts.E wS1)⁻¹ =
        (Om1Facts.E wS1 * x * (Om1Facts.E wS1)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem pr_KR : ∀ k < 8, ∃ g ∈ Om1Facts.R, PR (BD.KR k) g := by
  intro k hk
  rw [B.krOK_sound (allN_spec B.kKR k hk)]
  have p11 := pr_pc pr_i0 pr_i0
  have p111 := pr_pc p11 pr_i0
  have m11 := Om1Facts.R.mul_mem i0_mem i0_mem
  have m111 := Om1Facts.R.mul_mem m11 i0_mem
  interval_cases k
  · exact ⟨1, Om1Facts.R.one_mem, pr_pid⟩
  · exact ⟨_, i0_mem, pr_i0⟩
  · exact ⟨_, m11, p11⟩
  · exact ⟨_, m111, p111⟩
  · exact ⟨_, j0_mem, pr_j0⟩
  · exact ⟨_, Om1Facts.R.mul_mem j0_mem i0_mem, pr_pc pr_j0 pr_i0⟩
  · exact ⟨_, Om1Facts.R.mul_mem j0_mem m11, pr_pc pr_j0 p11⟩
  · exact ⟨_, Om1Facts.R.mul_mem j0_mem m111, pr_pc pr_j0 p111⟩

theorem pr_KS : ∀ k < 8, ∃ g ∈ Om1Facts.R', PR (BD.KS k) g := by
  intro k hk
  obtain ⟨-, e⟩ := B.ksOK_sound (allN_spec B.kKS k hk)
  obtain ⟨g, hg, hp⟩ := pr_KR k hk
  exact ⟨_, conj_R g hg, pr_conj pr_s1 hp e⟩

theorem tg_mem : ∀ k < 7, ∃ g ∈ Om1Facts.G wT, PR (A.TG.G k) g := fun k hk =>
  ⟨_, E_mem_G (getD_mem (by rw [A.kLens.2.1]; exact hk)), pr_TG hk⟩

theorem cc_mem : ∀ k < 5, ∃ g ∈ Om1Facts.G wCc, PR (A.CC.G k) g := fun k hk =>
  ⟨_, E_mem_G (getD_mem (by rw [A.kLens.2.2.2.1]; exact hk)), pr_CC hk⟩

theorem pr_gI {G : Nat → Nat} {ng k : Nat} {S : Subgroup (Equiv.Perm (Fin 240))}
    (hG : ∀ k < ng, ∃ g ∈ S, PR (G k) g) (hk : k ≤ ng) : ∃ g ∈ S, PR (B.gI G ng k) g := by
  unfold B.gI
  cases hb : Nat.beq k ng
  · have hne : k ≠ ng := Nat.ne_of_beq_eq_false hb
    obtain ⟨g, hg, hp⟩ := hG k (by omega)
    exact ⟨g, hg, hp⟩
  · exact ⟨1, S.one_mem, pr_pid⟩

theorem pr_Lh {G A AI R : Nat → Nat} {ng nL : Nat} {S : Subgroup (Equiv.Perm (Fin 240))}
    (hG : ∀ k < ng, ∃ g ∈ S, PR (G k) g) (hc : allN nL (B.lhOK G A AI R ng) = true) :
    ∀ h < nL, ∃ s ∈ S, PR (A h) s ∧ PR (AI h) s⁻¹ := by
  intro h hh
  obtain ⟨a, ha, b, hb, e1, e2, e3⟩ := B.lhOK_sound (allN_spec hc h hh)
  obtain ⟨g1, hg1, p1⟩ := pr_gI hG ha
  obtain ⟨g2, hg2, p2⟩ := pr_gI hG hb
  have hA : PR (A h) (g1 * g2) := by
    rw [e1]
    exact pr_pc p1 p2
  exact ⟨g1 * g2, S.mul_mem hg1 hg2, hA, pr_inv hA e3 e2⟩

theorem lhT : ∀ h < 57, ∃ s ∈ Om1Facts.G wT, PR (BD.LhG h) s ∧ PR (BD.LhI h) s⁻¹ :=
  pr_Lh tg_mem B.kLh

theorem lcC : ∀ h < 31, ∃ s ∈ Om1Facts.G wCc, PR (BD.LcG h) s ∧ PR (BD.LcI h) s⁻¹ :=
  pr_Lh cc_mem B.kLc

theorem wDT_ok : ∀ w ∈ wDT, wordOK w = true := by decide +kernel

theorem wDT_lt : ∀ w ∈ wDT, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)

theorem wDT_len : wDT.length = 204 := by decide +kernel

theorem dt_D : ∀ j < 204, ∃ d ∈ Om1Facts.D, PR (BD.DG j) d := by
  intro j hj
  obtain ⟨-, e, ne1, ne2⟩ := B.dtOK_sound (allN_spec B.kDT j hj)
  have hw : wDT.getD j [] ∈ wDT := getD_mem (by rw [wDT_len]; exact hj)
  have pg := pr_E (wDT_lt _ hw)
  have hd := pr_conj pg pr_t e.symm
  refine ⟨_, ⟨Om1Facts.E (wDT.getD j []), Subgroup.subset_closure ⟨_, wDT_ok _ hw, rfl⟩, rfl,
    pr_ne hd pr_t ne1, pr_ne hd (pr_pc pr_t pr_z) ne2⟩, hd⟩

abbrev Cl (x : Equiv.Perm (Fin 240)) : Subgroup (Equiv.Perm (Fin 240)) :=
  Subgroup.closure (((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') ∪
    {y | ∃ h ∈ Om1Facts.G wT, y = h * x * h⁻¹})

theorem s1rev : Om1Facts.E wS1.reverse = (Om1Facts.E wS1)⁻¹ :=
  pr_eq (pr_EL (k := 5) (by norm_num)) pr_s1i

theorem k0_le : Om1Facts.G A.k0W ≤ Subgroup.closure
    ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') := by
  unfold Om1Facts.G
  rw [Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  have hR : ∀ g ∈ Om1Facts.R, g ∈ Subgroup.closure
      ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') :=
    fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hR' : ∀ g ∈ Om1Facts.R', g ∈ Subgroup.closure
      ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') :=
    fun g hg => Subgroup.subset_closure (Or.inr hg)
  have l1 : ∀ r ∈ wS1, r < 240 := elW_lt _ (by decide)
  have l2 : ∀ r ∈ wI0, r < 240 := elW_lt _ (by decide)
  have l3 : ∀ r ∈ wJ0, r < 240 := elW_lt _ (by decide)
  have l4 : ∀ r ∈ wS1.reverse, r < 240 := elW_lt _ (by decide)
  have l12 : ∀ r ∈ wS1 ++ wI0, r < 240 := fun r hr => (List.mem_append.1 hr).elim (l1 r) (l2 r)
  have l13 : ∀ r ∈ wS1 ++ wJ0, r < 240 := fun r hr => (List.mem_append.1 hr).elim (l1 r) (l3 r)
  simp only [A.k0W, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact hR _ i0_mem
  · exact hR _ j0_mem
  · rw [E_append l12 l4, E_append l1 l2, s1rev]
    exact hR' _ (Subgroup.subset_closure (Set.mem_insert _ _))
  · rw [E_append l13 l4, E_append l1 l3, s1rev]
    exact hR' _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem pr_EK : ∀ k < 32, ∃ g ∈ Subgroup.closure
    ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R'), PR (EK.T k) g :=
  fun k hk => ⟨_, k0_le (enumK.2.2.1 k hk), enumK.2.1 k hk⟩

theorem cl_mono (x : Equiv.Perm (Fin 240)) :
    Subgroup.closure ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') ≤ Cl x :=
  Subgroup.closure_mono Set.subset_union_left

theorem wLet_mem {X XV l : Nat} {x : Equiv.Perm (Fin 240)} (hx : PR X x)
    (hxv : B.wInv l = true → PR XV x⁻¹) (hl : B.wLetOK l = true) :
    ∃ g ∈ Cl x, PR (B.wLet X XV l) g := by
  have hty : fld(l, 0, 3) ≤ 3 := fld_le _ _ _
  unfold B.wLetOK at hl
  unfold B.wInv at hxv
  unfold B.wLet
  simp only [strictB_eq] at hl
  simp only [strictN_eq]
  generalize fld(l, 2, 127) = k at hl ⊢
  generalize fld(l, 0, 3) = ty at hl hxv hty ⊢
  interval_cases ty
  · obtain ⟨g, hg, hp⟩ := pr_EK k (Nat.blt_eq.mp hl)
    exact ⟨g, cl_mono x hg, hp⟩
  · obtain ⟨s, hs, hS, hSI⟩ := lhT k (Nat.blt_eq.mp hl)
    refine ⟨s * x * s⁻¹, Subgroup.subset_closure (Or.inr ⟨s, hs, rfl⟩), ?_⟩
    have := pr_pc hS (pr_pc hx hSI)
    rw [← mul_assoc] at this
    exact this
  · obtain ⟨s, hs, hS, hSI⟩ := lhT k (Nat.blt_eq.mp hl)
    have e : (s * x * s⁻¹)⁻¹ = s * (x⁻¹ * s⁻¹) := by group
    refine ⟨(s * x * s⁻¹)⁻¹, inv_mem (Subgroup.subset_closure (Or.inr ⟨s, hs, rfl⟩)), ?_⟩
    rw [e]
    exact pr_pc hS (pr_pc (hxv rfl) hSI)
  · exact ⟨x, Subgroup.subset_closure (Or.inr ⟨1, one_mem _, by group⟩), hx⟩

theorem wProd_mem {X XV nl l1 l2 l3 l4 : Nat} {x : Equiv.Perm (Fin 240)} (hx : PR X x)
    (hxv : (B.wInv l1 || B.wInv l2 || B.wInv l3 || B.wInv l4) = true → PR XV x⁻¹)
    (h1 : B.wLetOK l1 = true) (h2 : B.wLetOK l2 = true) (h3 : B.wLetOK l3 = true)
    (h4 : B.wLetOK l4 = true) (hnl : nl ≤ 4) (hnl0 : nl ≠ 0) :
    ∃ g ∈ Cl x, PR (B.wProd X XV nl l1 l2 l3 l4) g := by
  obtain ⟨g1, m1, p1⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h1
  obtain ⟨g2, m2, p2⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h2
  obtain ⟨g3, m3, p3⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h3
  obtain ⟨g4, m4, p4⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h4
  have hnl1 : 1 ≤ nl := Nat.pos_of_ne_zero hnl0
  unfold B.wProd
  interval_cases nl
  · exact ⟨g1, m1, p1⟩
  · exact ⟨g1 * g2, mul_mem m1 m2, pr_pc p1 p2⟩
  · exact ⟨g1 * (g2 * g3), mul_mem m1 (mul_mem m2 m3), pr_pc p1 (pr_pc p2 p3)⟩
  · exact ⟨g1 * (g2 * (g3 * g4)), mul_mem m1 (mul_mem m2 (mul_mem m3 m4)),
      pr_pc p1 (pr_pc p2 (pr_pc p3 p4))⟩

theorem bad_of_wit {En W : Nat → Nat} {nE i : Nat} {x : Equiv.Perm (Fin 240)}
    (hEv : ∀ i < nE, PR (En i) (permOfArr 240 (unpack 240 8 (En i))))
    (hx : PR (En i) x) (hw : B.witOK En nE W i = true) (hn : B.noWit W i = false) :
    OmGen.BadElt (Om1Facts.G wT) (↑Om1Facts.R ∪ ↑Om1Facts.R') Om1Facts.D x := by
  have hne0 := B.noWit_sound hn
  rcases B.witOK_sound hw with h0 | ⟨hnl, hxi, hj, hl1, hl2, hl3, hl4, hinv, hval⟩
  · exact absurd h0 hne0
  · have hxv : (B.wInv fld(W i, 3, 511) || B.wInv fld(W i, 12, 511) || B.wInv fld(W i, 21, 511) ||
        B.wInv fld(W i, 30, 511)) = true → PR (En fld(W i, 39, 8191)) x⁻¹ := fun h => by
      have hv := hEv _ hxi
      rw [pr_inv_eq hx hv (hinv h)] at hv
      exact hv
    obtain ⟨g, hg, hp⟩ := wProd_mem hx hxv hl1 hl2 hl3 hl4 hnl hne0
    rw [hval] at hp
    obtain ⟨d, hd, pd⟩ := dt_D _ hj
    exact ⟨g, by rw [pr_eq hp pd]; exact hd, hg⟩

theorem bad_count {En W : Nat → Nat} {nE bound : Nat} {ws : List (List Nat)}
    (hEv : ∀ i < nE, PR (En i) (permOfArr 240 (unpack 240 8 (En i))))
    (hEc : ∀ x ∈ Om1Facts.G ws, ∃ i < nE, PR (En i) x)
    (hw : ∀ i < nE, B.witOK En nE W i = true)
    (hc : ((List.range nE).filter (B.noWit W)).length ≤ bound) :
    {x | x ∈ Om1Facts.G ws ∧
      ¬ OmGen.BadElt (Om1Facts.G wT) (↑Om1Facts.R ∪ ↑Om1Facts.R') Om1Facts.D x}.ncard ≤ bound := by
  refine (ncard_le_of_pr (T := En) fun x hx => ?_).trans hc
  obtain ⟨i, hi, hp⟩ := hEc x hx.1
  refine ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩, hp⟩
  cases hnw : B.noWit W i
  · exact absurd (bad_of_wit hEv hp (hw i hi) hnw) hx.2
  · rfl

theorem bad_fact :
    {x | x ∈ Om1Facts.G wS0 ∧
      ¬ OmGen.BadElt (Om1Facts.G wT) (↑Om1Facts.R ∪ ↑Om1Facts.R') Om1Facts.D x}.ncard ≤ 64 ∧
    {x | x ∈ Om1Facts.G wP3 ∧
      ¬ OmGen.BadElt (Om1Facts.G wT) (↑Om1Facts.R ∪ ↑Om1Facts.R') Om1Facts.D x}.ncard ≤ 3 :=
  ⟨bad_count enum0.2.1 enum0.2.2.2 B.wit0_all B.cnt0,
    bad_count enum1.2.1 enum1.2.2.2 (allN_spec B.kW1) B.cnt1⟩

theorem cjAt_eq {S SI G : Nat} {s g : Equiv.Perm (Fin 240)} (hs : PR S s) (hsi : PR SI s⁻¹)
    (hg : PR G g) (q : Fin 240) : B.cjAt S SI G q = ((s * g * s⁻¹) q : Nat) := by
  unfold B.cjAt
  simp only [ipB]
  rw [pr_ip hsi, pr_ip hg, pr_ip hs]
  rfl

theorem xpw_eq {X : Nat} {x : Equiv.Perm (Fin 240)} (hx : PR X x) {k : Nat} (hk : k < 4)
    (q : Fin 240) : B.xpw X k q = ((x ^ k) q : Nat) := by
  unfold B.xpw
  simp only [ipB]
  interval_cases k
  · change (q : Nat) = ((x ^ 0) q : Nat)
    simp
  · change pg 8 (mask 8) X q = ((x ^ 1) q : Nat)
    rw [pow_one, pr_ip hx]
  · change pg 8 (mask 8) X (pg 8 (mask 8) X q) = ((x ^ 2) q : Nat)
    rw [pr_ip hx, pr_ip hx, pow_two]
    rfl
  · change pg 8 (mask 8) X (pg 8 (mask 8) X (pg 8 (mask 8) X q)) = ((x ^ 3) q : Nat)
    rw [pr_ip hx, pr_ip hx, pr_ip hx, pow_three]
    rfl

theorem twinFail_of {X Y S SI : Nat} {x y s : Equiv.Perm (Fin 240)} (hx : PR X x) (hy : PR Y y)
    (hs : PR S s) (hsi : PR SI s⁻¹) (h : B.TwinFailK X Y S SI) : Om1Facts.TwinFail x y s := by
  obtain ⟨⟨g, hg, hk⟩, a, ha, b, hb, p, hp, hne⟩ := h
  have mem : ∀ {G : Nat}, G ∈ [X, Y] → ∃ g' ∈ ({x, y} : Set (Equiv.Perm (Fin 240))), PR G g' := by
    intro G hG
    rcases List.mem_cons.1 hG with rfl | hG'
    · exact ⟨x, Set.mem_insert _ _, hx⟩
    · rw [List.mem_singleton] at hG'
      subst hG'
      exact ⟨y, Set.mem_insert_of_mem _ rfl, hy⟩
  obtain ⟨g', hg', pg⟩ := mem hg
  obtain ⟨a', ha', pa⟩ := mem ha
  obtain ⟨b', hb', pb⟩ := mem hb
  refine ⟨⟨g', hg', fun k hk4 => ⟨fun e => ?_, fun e => ?_⟩⟩, a', ha', b', hb', fun e => ?_⟩
  · obtain ⟨q, hq, hne⟩ := (hk k hk4).1
    apply hne
    rw [cjAt_eq hs hsi pg ⟨q, hq⟩, e, ← xpw_eq hx hk4 ⟨q, hq⟩]
  · obtain ⟨q, hq, hne⟩ := (hk k hk4).2
    apply hne
    rw [cjAt_eq hs hsi pg ⟨q, hq⟩, e, Equiv.Perm.mul_apply]
    simp only [ipB]
    rw [← pr_ip hy, ← xpw_eq hx hk4 ⟨q, hq⟩]
  · apply hne
    have e1 : B.ip a (B.cjAt S SI b p) = ((a' * (s * b' * s⁻¹)) ⟨p, hp⟩ : Nat) := by
      rw [cjAt_eq hs hsi pb ⟨p, hp⟩]
      simp only [ipB]
      rw [pr_ip pa]
      rfl
    have e2 : B.cjAt S SI b (B.ip a p) = (((s * b' * s⁻¹) * a') ⟨p, hp⟩ : Nat) := by
      simp only [ipB]
      rw [pr_ipn pa hp]
      rw [cjAt_eq hs hsi pb]
      rfl
    rw [e1, e2, e]

theorem q8_core {En SQ RT PRw Lg LgI : Nat → Nat} {nE nR nL tt : Nat} {withR : Bool}
    {τ x y : Equiv.Perm (Fin 240)} {S : Subgroup (Equiv.Perm (Fin 240))} {i j : Nat}
    (hτ : PR tt τ) (hττ : τ * τ = 1)
    (hsq : allN nE (B.sqOK En SQ RT tt nR) = true) (hrt : allN nR (B.rootOK En RT nE) = true)
    (hrow : ∀ a < nR, B.q8Row En RT PRw Lg LgI nL nR withR a = true)
    (hL : ∀ h < nL, ∃ s ∈ S, PR (Lg h) s ∧ PR (LgI h) s⁻¹)
    (hi : i < nE) (hj : j < nE) (hx : PR (En i) x) (hy : PR (En j) y)
    (hxx : x * x = τ) (hyy : y * y = τ) (hyx : y * x * y⁻¹ = x⁻¹) :
    (withR = true ∧ x ∈ Om1Facts.R ∧ y ∈ Om1Facts.R) ∨
      (withR = true ∧ x ∈ Om1Facts.R' ∧ y ∈ Om1Facts.R') ∨
        ∃ _ : 0 < nL, ∃ s ∈ S, Om1Facts.TwinFail x y s := by
  have root : ∀ {i : Nat} {w : Equiv.Perm (Fin 240)}, i < nE → PR (En i) w → w * w = τ →
      ∃ a < nR, fld(RT a, 0, 8191) = i := by
    intro i w hi hw hww
    rcases B.sqOK_sound (allN_spec hsq i hi) with h | ⟨p, hp, hne⟩
    · exact h
    · refine absurd ?_ hne
      simp only [ipB]
      rw [pr_ipn hw hp, pr_ip hw, pr_ipn hτ hp, ← hww]
      rfl
  have inR : ∀ {a i : Nat} {w : Equiv.Perm (Fin 240)}, a < nR → fld(RT a, 0, 8191) = i →
      PR (En i) w → fld(RT a, 13, 1) = 1 → w ∈ Om1Facts.R := by
    intro a i w ha hai hw h1
    have e := (B.rootOK_sound (allN_spec hrt a ha)).2.1 h1
    rw [hai] at e
    rw [e] at hw
    obtain ⟨g, hg, hp⟩ := pr_KR _ (Nat.lt_succ_of_le (fld_le _ _ _))
    rw [pr_eq hw hp]
    exact hg
  have inR' : ∀ {a i : Nat} {w : Equiv.Perm (Fin 240)}, a < nR → fld(RT a, 0, 8191) = i →
      PR (En i) w → fld(RT a, 17, 1) = 1 → w ∈ Om1Facts.R' := by
    intro a i w ha hai hw h1
    have e := (B.rootOK_sound (allN_spec hrt a ha)).2.2 h1
    rw [hai] at e
    rw [e] at hw
    obtain ⟨g, hg, hp⟩ := pr_KS _ (Nat.lt_succ_of_le (fld_le _ _ _))
    rw [pr_eq hw hp]
    exact hg
  obtain ⟨a, ha, hai⟩ := root hi hx hxx
  obtain ⟨b, hb, hbj⟩ := root hj hy hyy
  have hpf := B.q8Row_sound (hrow a ha) b hb
  rw [hai, hbj] at hpf
  rcases hpf with ⟨p, hp, hne⟩ | ⟨hw, ha1, hb1⟩ | ⟨hw, ha1, hb1⟩ | ⟨h, hh, htw⟩
  · exfalso
    have h4 : x * x * x * x = 1 := by
      calc x * x * x * x = (x * x) * (x * x) := by group
        _ = 1 := by rw [hxx, hττ]
    have e : y * x = x * x * x * y := by
      rw [eq_inv_of_mul_eq_one_left h4]
      exact mul_inv_eq_iff_eq_mul.1 hyx
    apply hne
    simp only [ipB]
    rw [pr_ipn hx hp, pr_ip hy, pr_ipn hy hp, pr_ip hx, pr_ip hx, pr_ip hx]
    exact congrArg (fun w : Equiv.Perm (Fin 240) => ((w ⟨p, hp⟩ : Fin 240) : Nat)) e
  · exact Or.inl ⟨hw, inR ha hai hx ha1, inR hb hbj hy hb1⟩
  · exact Or.inr (Or.inl ⟨hw, inR' ha hai hx ha1, inR' hb hbj hy hb1⟩)
  · obtain ⟨s, hs, hS, hSI⟩ := hL h hh
    exact Or.inr (Or.inr ⟨by omega, s, hs, twinFail_of hx hy hS hSI htw⟩)

theorem sq_of_permOK {P : Nat} {g : Equiv.Perm (Fin 240)} (hP : PR P g)
    (h : permOK 240 8 (mask 8) (240 * 8) P P = true) : g * g = 1 := by
  obtain ⟨-, -, h3⟩ := permOK_facts h
  ext x
  have e := (h3 x x.2).2
  rw [pr_ip hP x, pr_ip hP (g x)] at e
  simpa [Equiv.Perm.mul_apply] using e

theorem t_sq : Om1Facts.t * Om1Facts.t = 1 :=
  sq_of_permOK pr_t (allN_spec A.kFTv 15 (by norm_num))

theorem ta_sq : Om1Facts.ta * Om1Facts.ta = 1 :=
  sq_of_permOK pr_ta (allN_spec A.kFTv 3 (by norm_num))

theorem tc_sq : Om1Facts.tc * Om1Facts.tc = 1 :=
  sq_of_permOK pr_tc (allN_spec A.kFTv 23 (by norm_num))

theorem q80_fact : ∀ x ∈ Om1Facts.G wS0, ∀ y ∈ Om1Facts.G wS0, x * x = Om1Facts.t →
    y * y = Om1Facts.t → y * x * y⁻¹ = x⁻¹ →
    (x ∈ Om1Facts.R ∧ y ∈ Om1Facts.R) ∨ (x ∈ Om1Facts.R' ∧ y ∈ Om1Facts.R') ∨
      ∃ s ∈ Om1Facts.G wT, Om1Facts.TwinFail x y s := by
  intro x hx y hy hxx hyy hyx
  obtain ⟨i, hi, px⟩ := enum0.2.2.2 x hx
  obtain ⟨j, hj, py⟩ := enum0.2.2.2 y hy
  rcases q8_core pr_t t_sq B.kSq0 B.kRt0 B.q80_all lhT hi hj px py hxx hyy hyx with
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem q8a_fact : (∀ x ∈ Om1Facts.G wSa, x * x ≠ Om1Facts.tb) ∧
    ∀ x ∈ Om1Facts.G wSa, ∀ y ∈ Om1Facts.G wSa, x * x = Om1Facts.ta → y * y = Om1Facts.ta →
      y * x * y⁻¹ ≠ x⁻¹ := by
  refine ⟨fun x hx hxx => ?_, fun x hx y hy hxx hyy hyx => ?_⟩
  · obtain ⟨i, hi, px⟩ := enuma.2.2.2 x hx
    rcases B.sqOK_sound (allN_spec B.kSba i hi) with ⟨a, ha, -⟩ | ⟨p, hp, hne⟩
    · exact absurd ha (Nat.not_lt_zero _)
    · apply hne
      unfold B.TB
      simp only [ipB]
      rw [pr_ipn px hp, pr_ip px, pr_ipn pr_tb hp, ← hxx]
      rfl
  · obtain ⟨i, hi, px⟩ := enuma.2.2.2 x hx
    obtain ⟨j, hj, py⟩ := enuma.2.2.2 y hy
    have hL : ∀ h < 0, ∃ s ∈ (⊤ : Subgroup (Equiv.Perm (Fin 240))),
        PR (BD.LhG h) s ∧ PR (BD.LhI h) s⁻¹ := fun h hh => absurd hh (Nat.not_lt_zero _)
    rcases q8_core pr_ta ta_sq B.kSqa B.kRta B.q8a_all hL hi hj px py hxx hyy hyx with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true
    · exact absurd h (Nat.lt_irrefl 0)

theorem q8c_fact : ∀ x ∈ Om1Facts.G wSc, ∀ y ∈ Om1Facts.G wSc, x * x = Om1Facts.tc →
    y * y = Om1Facts.tc → y * x * y⁻¹ = x⁻¹ → ∃ s ∈ Om1Facts.G wCc, Om1Facts.TwinFail x y s := by
  intro x hx y hy hxx hyy hyx
  obtain ⟨i, hi, px⟩ := enumc.2.2.2 x hx
  obtain ⟨j, hj, py⟩ := enumc.2.2.2 y hy
  rcases q8_core pr_tc tc_sq B.kSqc B.kRtc B.q8c_all lcC hi hj px py hxx hyy hyx with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact h

theorem pr_i0' : PR (BD.OC 0) Om1Facts.i0' := by
  obtain ⟨-, h0, -⟩ := B.oNodeOK_sound (allN_spec B.kOrb 0 (by norm_num))
  exact pr_conj pr_s1 pr_i0 (h0 rfl).2.2.1

theorem pr_j0' : PR (BD.OD 0) Om1Facts.j0' := by
  obtain ⟨-, h0, -⟩ := B.oNodeOK_sound (allN_spec B.kOrb 0 (by norm_num))
  exact pr_conj pr_s1 pr_j0 (h0 rfl).2.2.2

abbrev TupR (m : Nat) (s : Equiv.Perm (Fin 240)) : Prop :=
  PR (BD.OA m) (s * Om1Facts.E wI0 * s⁻¹) ∧ PR (BD.OB m) (s * Om1Facts.E wJ0 * s⁻¹) ∧
    PR (BD.OC m) (s * Om1Facts.i0' * s⁻¹) ∧ PR (BD.OD m) (s * Om1Facts.j0' * s⁻¹)

theorem tup_tree : ∀ m < 576, ∃ s ∈ Om1Facts.G wT, TupR m s := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨-, h0, h1⟩ := B.oNodeOK_sound (allN_spec B.kOrb m hm)
    by_cases hm0 : m = 0
    · subst hm0
      obtain ⟨e1, e2, -, -⟩ := h0 rfl
      refine ⟨1, one_mem _, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        simpa using pr_i0
      · rw [e2]
        simpa using pr_j0
      · simpa using pr_i0'
      · simpa using pr_j0'
    · obtain ⟨par, hpar, k, hk, e⟩ := h1 hm0
      obtain ⟨s, hs, pa, pb, pc', pd⟩ := ih par hpar (by omega)
      have hg := pr_TG hk
      have e0 : pc2 (A.TG.G k) (BD.OA par) = pc2 (BD.OA m) (A.TG.G k) := e 0 (by norm_num)
      have e1 : pc2 (A.TG.G k) (BD.OB par) = pc2 (BD.OB m) (A.TG.G k) := e 1 (by norm_num)
      have e2 : pc2 (A.TG.G k) (BD.OC par) = pc2 (BD.OC m) (A.TG.G k) := e 2 (by norm_num)
      have e3 : pc2 (A.TG.G k) (BD.OD par) = pc2 (BD.OD m) (A.TG.G k) := e 3 (by norm_num)
      refine ⟨Om1Facts.E (wT.getD k []) * s,
        mul_mem (E_mem_G (getD_mem (by rw [A.kLens.2.1]; exact hk))) hs, ?_, ?_, ?_, ?_⟩
      · convert pr_conj hg pa e0 using 1
        group
      · convert pr_conj hg pb e1 using 1
        group
      · convert pr_conj hg pc' e2 using 1
        group
      · convert pr_conj hg pd e3 using 1
        group

theorem tuple_fact : 576 ≤ {p | ∃ s ∈ Om1Facts.G wT, p = Om1Facts.tup s}.ncard := by
  choose! f hf using tup_tree
  have cn : ∀ m < 576, ∀ c < 4, B.cnK (B.oc c m) = true := fun m hm =>
    (B.oNodeOK_sound (allN_spec B.kOrb m hm)).1
  have hnd : ((List.range 576).map fun m => Om1Facts.tup (f m)).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro m hm m' hm' he
    rw [List.mem_range] at hm hm'
    obtain ⟨-, a, b, c, d⟩ := hf m hm
    obtain ⟨-, a', b', c', d'⟩ := hf m' hm'
    simp only [Om1Facts.tup, Prod.mk.injEq] at he
    obtain ⟨ea, eb, ec, ed⟩ := he
    rw [ea] at a
    rw [eb] at b
    rw [ec] at c
    rw [ed] at d
    apply B.tupK_inj m hm m' hm'
    unfold B.tupK
    rw [eq_of_pr a a' (cn m hm 0 (by norm_num)) (cn m' hm' 0 (by norm_num)),
      eq_of_pr b b' (cn m hm 1 (by norm_num)) (cn m' hm' 1 (by norm_num)),
      eq_of_pr c c' (cn m hm 2 (by norm_num)) (cn m' hm' 2 (by norm_num)),
      eq_of_pr d d' (cn m hm 3 (by norm_num)) (cn m' hm' 3 (by norm_num))]
  refine le_trans ?_ (hnd.length_le_ncard (Set.toFinite _) ?_)
  · simp
  · intro p hp
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hp
    exact ⟨f m, (hf m (List.mem_range.1 hm)).1, rfl⟩

end CertificateChecks.KernelOm1

end
