module

public import CFSG.Certificates.Kernel.J4Q.CovTabSound
public import Certificates.Kernel.J4Cov3.TabChecks
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QT2AMod
public import CFSG.Sporadic.J4.QT2AGen
public import CFSG.Sporadic.J4.QTOutNorm
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure

public section

namespace CertificateChecks.KernelJ4Cov3

open CFSG CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
open CFSG.KS.J4CovTab CFSG.KC.J4Q CFSG.StandardType.SporadicShape

private theorem g5_getL {m : ℕ} (hm : m < 3) : (g5Mats ())[m]? = (locMats ())[m]? := by
  unfold g5Mats
  have hl : (locMats ()).size = 3 := CertificateChecks.KernelJ4Q.matFacts.locSize
  exact Array.getElem?_append_left (by rw [hl]; exact hm)

private theorem g5i_getL {m : ℕ} (hm : m < 3) : (g5Invs ())[m]? = (locInvs ())[m]? := by
  unfold g5Invs
  have hl : (locInvs ()).size = 3 := by
    have := CertificateChecks.KernelJ4Q.matFacts.locSize
    simpa [locInvs] using this
  exact Array.getElem?_append_left (by rw [hl]; exact hm)

private theorem g5_getB (m : ℕ) : (g5Mats ())[m + 3]? = baseMats[m]? := by
  unfold g5Mats
  have hl : (locMats ()).size = 3 := CertificateChecks.KernelJ4Q.matFacts.locSize
  rw [Array.getElem?_append_right (by omega), hl, Nat.add_sub_cancel]

private theorem g5i_getB (m : ℕ) : (g5Invs ())[m + 3]? = baseInvs[m]? := by
  unfold g5Invs
  have hl : (locInvs ()).size = 3 := by
    have := CertificateChecks.KernelJ4Q.matFacts.locSize
    simpa [locInvs] using this
  rw [Array.getElem?_append_right (by omega), hl, Nat.add_sub_cancel]

theorem gens_rep {k : ℕ} (hk : k < 5) :
    jRep (getN CFSG.KD.J4Q.one CFSG.KD.J4Cov3.mats k) (gen5 k) := by
  have hX : rowsMatrix ((g5Mats ())[k]?.getD idRows) = Mx (gen5 k) :=
    g5Mats_spec CertificateChecks.KernelJ4Q.matFacts k
  refine ⟨_, ?_, ?_, hX⟩
  · by_cases h3 : k < 3
    · rw [g5_getL h3]
      exact (CertificateChecks.KernelJ4Q.loc_gens k).1
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      rw [g5_getB]
      exact (CertificateChecks.KernelJ4Q.base_gens m).1
  · by_cases h3 : k < 3
    · rw [g5_getL h3, (CertificateChecks.KernelJ4Q.loc_gens k).2]
      interval_cases k <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      rw [g5_getB, (CertificateChecks.KernelJ4Q.base_gens m).2]
      have : m < 2 := by omega
      interval_cases m <;> rfl

theorem invs_rep {k : ℕ} (hk : k < 5) :
    jRep (getN CFSG.KD.J4Q.one CFSG.KD.J4Cov3.invs k) (gen5 k)⁻¹ := by
  have hX : rowsMatrix ((g5Invs ())[k]?.getD idRows) = Mx (gen5 k)⁻¹ :=
    g5Invs_spec CertificateChecks.KernelJ4Q.matFacts k
  refine ⟨_, ?_, ?_, hX⟩
  · by_cases h3 : k < 3
    · rw [g5i_getL h3]
      exact (CertificateChecks.KernelJ4Q.loc_invs k).1
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      rw [g5i_getB]
      exact (CertificateChecks.KernelJ4Q.base_invs m).1
  · by_cases h3 : k < 3
    · rw [g5i_getL h3, (CertificateChecks.KernelJ4Q.loc_invs k).2]
      interval_cases k <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      rw [g5i_getB, (CertificateChecks.KernelJ4Q.base_invs m).2]
      have : m < 2 := by omega
      interval_cases m <;> rfl

theorem jfacts : ∃ p1 p2 g1 g2 t : J, Facts jRep gen5 CFSG.KD.J4Q.rm (v2N rootV)
    CFSG.KD.J4Cov3.cj CFSG.KD.J4Cov3.cw CFSG.KD.J4Cov3.fu p1 p2 g1 g2 t :=
  chk_sound (jModel CertificateChecks.KernelJ4Q.hK) gen5 (fun _ hk => gens_rep hk)
    (fun _ hk => invs_rep hk) CFSG.KD.J4Cov3.chk

section Group

variable {p1 p2 g1 g2 t : J}
  (F : Facts jRep gen5 CFSG.KD.J4Q.rm (v2N rootV) CFSG.KD.J4Cov3.cj CFSG.KD.J4Cov3.cw
    CFSG.KD.J4Cov3.fu p1 p2 g1 g2 t)

noncomputable def Psub (p1 p2 : J) : Subgroup J := Subgroup.closure {p1, p2}

theorem tab_zero : tab p1 p2 0 = 1 := by simp [tab]

theorem tab_mem (k : ℕ) : tab p1 p2 k ∈ Psub p1 p2 := by
  have h1 : p1 ∈ Psub p1 p2 := Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : p2 ∈ Psub p1 p2 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  unfold tab
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 _) (Subgroup.pow_mem _ h2 _))
    (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
      (Subgroup.pow_mem _ h1 _)) (Subgroup.pow_mem _ h2 _)) _)

include F

theorem Psub_subset : (Psub p1 p2 : Set J) ⊆ tab p1 p2 '' Set.Iio 27 := by
  refine closure_subset_of_closed {p1, p2} _ ⟨0, by norm_num, tab_zero⟩ ?_
  rintro _ ⟨n, hn, rfl⟩ g hg
  rcases hg with rfl | rfl
  · obtain ⟨l, hl, e⟩ := F.clos1 n hn
    exact ⟨l, hl, e.symm⟩
  · obtain ⟨l, hl, e⟩ := F.clos2 n hn
    exact ⟨l, hl, e.symm⟩

theorem card_Psub : Nat.card (Psub p1 p2) = 27 := by
  have hset : (Psub p1 p2 : Set J) = ↑((Finset.range 27).image (tab p1 p2)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Psub_subset F hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn, rfl⟩)
    · intro hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact tab_mem n
  have h1 : Nat.card (Psub p1 p2) = ((Finset.range 27).image (tab p1 p2)).card := by
    rw [← Set.ncard_coe_finset, ← hset]
    exact Nat.card_coe_set_eq _
  rw [h1, Finset.card_image_of_injOn, Finset.card_range]
  intro n hn m hm h
  have hn' := Finset.mem_range.1 (Finset.mem_coe.1 hn)
  have hm' := Finset.mem_range.1 (Finset.mem_coe.1 hm)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact F.dist m hm' n hlt h
  · exact F.dist n hn' m hgt h.symm

omit F in
theorem isConj_of_mul {G : Type*} [Group G] {a b c : G} (h : c * a = b * c) : IsConj a b :=
  isConj_iff.2 ⟨c, by rw [h, mul_inv_cancel_right]⟩

omit F in
theorem isConj_of_mul_inv {G : Type*} [Group G] {a b c : G} (h : b * c * a = c) :
    IsConj a b⁻¹ := by
  have e : c * a = b⁻¹ * c := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
    exact h
  exact isConj_of_mul e

omit F in
theorem isConj_inv {G : Type*} [Group G] {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by rw [← hc]; group⟩

theorem cj_conj {j : ℕ} (hj : j < CFSG.KD.J4Cov3.cj.length) :
    IsConj (tab p1 p2 (cjM CFSG.KD.J4Cov3.cj j)) p1 := by
  obtain ⟨-, c, hc⟩ := F.conj j hj
  exact isConj_of_mul hc

theorem inv_conj : IsConj p1⁻¹ p1 := by
  have h := cj_conj F F.cj0.1
  rw [F.cj0.2] at h
  have e : tab p1 p2 18 = p1⁻¹ := by
    have : tab p1 p2 18 = p1 ^ 2 := by simp [tab]
    rw [this, eq_inv_iff_mul_eq_one, ← pow_succ, F.p3]
  rwa [e] at h

theorem tab_conj {k : ℕ} (hk0 : 0 < k) (hk : k < 27) : IsConj (tab p1 p2 k) p1 := by
  obtain ⟨u, -, j, hj, h | h⟩ := F.wit k hk0 hk
  · exact (isConj_of_mul h).trans (cj_conj F hj)
  · exact IsConj.trans (isConj_of_mul_inv h)
      (IsConj.trans (isConj_inv (cj_conj F hj)) (inv_conj F))

omit F in
theorem factorization_three_J4 : (86775571046077562880 : ℕ).factorization 3 = 3 := by
  have h : (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

omit F in
theorem controlsAt_of_isConj {K : Type} [Group K] {x y : K} {Y : Subgroup K}
    (hY : SporKRestControlsAt x Y) (hxy : IsConj x y) (hyY : y ∈ Y) :
    SporKRestControlsAt y Y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  have hcY : c⁻¹ ∈ Y := hY c⁻¹ (by rw [inv_inv, hc]; exact hyY)
  intro g hg
  have h2 : c⁻¹ * g ∈ Y := hY _ (by
    have : (c⁻¹ * g)⁻¹ * x * (c⁻¹ * g) = g⁻¹ * (c * x * c⁻¹) * g := by group
    rw [this, hc]
    exact hg)
  simpa using Y.mul_mem (Y.inv_mem hcY) h2

omit F in
theorem inv_conj_mem {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (k : G) {x : G}
    (hx : x ∈ ((k • P : Sylow p G) : Subgroup G)) : k⁻¹ * x * k ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx

omit F in
theorem conj_mem_smul {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (k : G) {g : G}
    (hg : g ∈ (P : Subgroup G)) : k * g * k⁻¹ ∈ ((k • P : Sylow p G) : Subgroup G) := by
  have h := Subgroup.smul_mem_pointwise_smul g (MulAut.conj k) (P : Subgroup G) hg
  rw [← Sylow.coe_subgroup_smul] at h
  simpa [MulAut.smul_def, MulAut.conj_apply] using h

theorem one_class (PS : Sylow 3 J) (hPS : (PS : Subgroup J) = Psub p1 p2) {x : J}
    (hx : orderOf x = 3) : IsConj p1 x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq J PS Q
  have hxQ : x ∈ (Q : Subgroup J) := hQ (Subgroup.mem_zpowers x)
  rw [← hk] at hxQ
  have h1 : k⁻¹ * x * k ∈ Psub p1 p2 := hPS ▸ inv_conj_mem PS k hxQ
  obtain ⟨m, hm, hmx⟩ := Psub_subset F h1
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      have h2 : k⁻¹ * x * k = 1 := by rw [← hmx, h0, tab_zero]
      have hx1 : x = 1 := by
        calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
          _ = 1 := by rw [h2]; group
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · exact h0
  have hc := tab_conj F hm0 hm
  rw [hmx] at hc
  refine IsConj.symm (IsConj.trans ?_ hc)
  exact isConj_iff.2 ⟨k⁻¹, by group⟩

theorem Y_top (PS : Sylow 3 J) (hPS : (PS : Subgroup J) = Psub p1 p2) (hco : IsCoatom Hj)
    {Y : Subgroup J} (hPY : Psub p1 p2 ≤ Y) {x : J} (hx : orderOf x = 3)
    (hctl : SporKRestControlsAt x Y) : Y = ⊤ := by
  have hp1 : p1 ∈ Y := hPY (Subgroup.subset_closure (Set.mem_insert _ _))
  have hy : SporKRestControlsAt p1 Y :=
    controlsAt_of_isConj hctl (one_class F PS hPS hx).symm hp1
  have hmem : ∀ (g : J) (m : ℕ), p1 * g = g * tab p1 p2 m → g ∈ Y := by
    intro g m e
    apply hy
    have : g⁻¹ * p1 * g = tab p1 p2 m := by
      rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact hPY (tab_mem m)
  have hg1 : g1 ∈ Y := hmem _ _ F.fu1.2
  have hg2 : g2 ∈ Y := hmem _ _ F.fu2.2
  have htY : t ∈ Y := hmem _ _ F.fu3.2
  have hgY : Subgroup.closure ({g1, g2} : Set J) ≤ Y := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hg1
    · exact hg2
  have hH : Hj ≤ Y := by
    rw [Subgroup.closure_le]
    have hx : ∀ k < 3, xJ k ∈ Y := by
      intro k hk
      have e : gen5 k = xJ k := by simp [gen5, hk]
      rw [← e]
      exact hgY (F.gen k hk)
    rintro _ (rfl | rfl | rfl)
    · exact hx 0 (by norm_num)
    · exact hx 1 (by norm_num)
    · exact hx 2 (by norm_num)
  obtain ⟨n, hn, hv⟩ := F.root
  have tnot : t ∉ Hj :=
    not_mem_Hj CertificateChecks.KernelJ4Q.hK CertificateChecks.KernelJ4Q.matFacts hn hv
  exact hco.2 Y (lt_of_le_of_ne hH fun e => tnot (e ▸ htY))

omit F in
theorem mem_conjPre {G : Type*} [Group G] (Y : Subgroup G) (k g : G) :
    g ∈ Y.comap (MulAut.conj k).toMonoidHom ↔ k * g * k⁻¹ ∈ Y := by
  simp [Subgroup.mem_comap, MulAut.conj_apply]

theorem generating (PS : Sylow 3 J) (hPS : (PS : Subgroup J) = Psub p1 p2) (hco : IsCoatom Hj)
    {x : J} (hx : orderOf x = 3) : SporKRestGenerating 3 x := by
  intro Y hYS hctl
  obtain ⟨S, hSY⟩ := hYS
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq J PS S
  have hPY' : Psub p1 p2 ≤ Y.comap (MulAut.conj k).toMonoidHom := by
    intro g hg
    rw [← hPS] at hg
    have h1 : k * g * k⁻¹ ∈ ((k • PS : Sylow 3 J) : Subgroup J) := conj_mem_smul PS k hg
    rw [hk] at h1
    exact (mem_conjPre Y k g).2 (hSY h1)
  have hctl' : SporKRestControlsAt (k⁻¹ * x * k) (Y.comap (MulAut.conj k).toMonoidHom) := by
    intro g hg
    have hg' := (mem_conjPre Y k _).1 hg
    have e : (k * g * k⁻¹)⁻¹ * x * (k * g * k⁻¹) =
        k * (g⁻¹ * (k⁻¹ * x * k) * g) * k⁻¹ := by group
    exact (mem_conjPre Y k g).2 (hctl _ (by rw [e]; exact hg'))
  have hx' : orderOf (k⁻¹ * x * k) = 3 := by
    have e : k⁻¹ * x * k = MulAut.conj k⁻¹ x := by simp [MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq]
    exact hx
  have hY' := Y_top F PS hPS hco hPY' hx' hctl'
  rw [eq_top_iff]
  intro h _
  have h1 : k⁻¹ * h * k ∈ Y.comap (MulAut.conj k).toMonoidHom := by
    rw [hY']
    exact Subgroup.mem_top _
  simpa [mul_assoc] using (mem_conjPre Y k _).1 h1

theorem cover_of_facts (PS : Sylow 3 J) (hPS : (PS : Subgroup J) = Psub p1 p2)
    (hco : IsCoatom Hj) : SporKRestCover 3 J := by
  intro E hE hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  exact ⟨x, hx, hx1', generating F PS hPS hco (orderOf_eq_prime (hE.2 x hx) hx1')⟩

end Group

theorem sporKRest_cover_J : SporKRestCover 3 J := by
  have hF : J4Facts := j4Facts
  obtain ⟨p1, p2, g1, g2, t, F⟩ := jfacts
  have : Finite J := inferInstance
  obtain ⟨PS, hPS⟩ : ∃ PS : Sylow 3 J, (PS : Subgroup J) = Psub p1 p2 :=
    ⟨Sylow.ofCard (Psub p1 p2) (by
      rw [card_Psub F, card_J hF, factorization_three_J4]
      norm_num), rfl⟩
  exact cover_of_facts F PS hPS (isCoatom_Hj hF)

theorem sporKRest_cover_J4_3_native :
    SporKRestCover 3 CFSG.Blueprint.NativeSporadic.J4 :=
  @SporKRestCover.of_mulEquiv J CFSG.Blueprint.NativeSporadic.J4 inferInstance inferInstance
    (seedEquiv CertificateChecks.KernelJ4Q.matFacts).symm 3 sporKRest_cover_J

end CertificateChecks.KernelJ4Cov3

end
