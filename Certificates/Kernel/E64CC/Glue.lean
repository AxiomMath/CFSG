module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cen3L
public import Certificates.Kernel.E64CC.Head
public import Certificates.Kernel.E64CC.Cm
public import Certificates.Kernel.E64CC.Set
public import Certificates.Kernel.E64CC.Res
public import Certificates.Kernel.E64CC.Trip
public import CFSG.Certificates.Kernel.E64CCSound
public import CFSG.Certificates.Kernel.E64CCModel

public section

namespace CertificateChecks.KernelE64CC

open CFSG.KC.E64CC CFSG.KC.E64CCSound CFSG.KC.E64CCModel CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.KLie.CT (fget)
open scoped commutatorElement

theorem rep_P' : ∀ g < 28, ∀ x : Fin 14,
    pg 4 (mask 4) (CFSG.KD.E64CC.D g) x = (phi (eW g) x : Nat) := by
  decide +kernel

theorem rep_P {g : Nat} (hg : g < 28) : Rep (CFSG.KD.E64CC.D g) (phi (eW g)) := rep_P' g hg

@[expose] def gM (k : Nat) : Equiv.Perm (Fin 14) :=
  if k = 0 then phi (eW 0 * eW 3) else phi (eW 4 * eW 16)

theorem rep_G' : ∀ k < 2, ∀ x : Fin 14, pg 4 (mask 4) (MT.G k) x = (gM k x : Nat) := by
  decide +kernel

theorem rep_T0' : ∀ x : Fin 14, pg 4 (mask 4) (MT.T 0) x = ((1 : Equiv.Perm (Fin 14)) x : Nat) := by
  decide +kernel

theorem phi_pi' : ∀ x : Fin 14, (phi (allOnes 7) x : Nat) = (x + 7) % 14 := by decide +kernel

theorem set_ok : ∀ s < 245, setK CFSG.KD.E64CC.D s = true := by
  intro s hs
  have h0 := PK.allN_iff.1 set0
  have h1 := PK.allN_iff.1 set1
  have h2 := PK.allN_iff.1 set2
  have h3 := PK.allN_iff.1 set3
  have h4 := PK.allN_iff.1 set4
  have h5 := PK.allN_iff.1 set5
  have h6 := PK.allN_iff.1 set6
  by_cases c0 : s < 35
  · simpa using h0 s c0
  by_cases c1 : s < 70
  · simpa [show 35 + (s - 35) = s by omega] using h1 (s - 35) (by omega)
  by_cases c2 : s < 105
  · simpa [show 70 + (s - 70) = s by omega] using h2 (s - 70) (by omega)
  by_cases c3 : s < 140
  · simpa [show 105 + (s - 105) = s by omega] using h3 (s - 105) (by omega)
  by_cases c4 : s < 175
  · simpa [show 140 + (s - 140) = s by omega] using h4 (s - 140) (by omega)
  by_cases c5 : s < 210
  · simpa [show 175 + (s - 175) = s by omega] using h5 (s - 175) (by omega)
  · simpa [show 210 + (s - 210) = s by omega] using h6 (s - 210) (by omega)

theorem res_ok : ∀ r, r ≠ 0 → r < 708 → resK CFSG.KD.E64CC.D MT.T r = true := by
  intro r hr0 hr
  have h0 := PK.allN_iff.1 res0
  have h1 := PK.allN_iff.1 res1
  have h2 := PK.allN_iff.1 res2
  have h3 := PK.allN_iff.1 res3
  have h4 := PK.allN_iff.1 res4
  have h5 := PK.allN_iff.1 res5
  have h6 := PK.allN_iff.1 res6
  by_cases c0 : r < 102
  · simpa [show 1 + (r - 1) = r by omega] using h0 (r - 1) (by omega)
  by_cases c1 : r < 203
  · simpa [show 102 + (r - 102) = r by omega] using h1 (r - 102) (by omega)
  by_cases c2 : r < 304
  · simpa [show 203 + (r - 203) = r by omega] using h2 (r - 203) (by omega)
  by_cases c3 : r < 405
  · simpa [show 304 + (r - 304) = r by omega] using h3 (r - 304) (by omega)
  by_cases c4 : r < 506
  · simpa [show 405 + (r - 405) = r by omega] using h4 (r - 405) (by omega)
  by_cases c5 : r < 607
  · simpa [show 506 + (r - 506) = r by omega] using h5 (r - 506) (by omega)
  · simpa [show 607 + (r - 607) = r by omega] using h6 (r - 607) (by omega)

@[expose] def Mt : Subgroup (Equiv.Perm (Fin 14)) := Subgroup.closure (gM '' {k | k < MT.ng})

theorem enum_facts : ∃ c : Nat → Equiv.Perm (Fin 14), c 0 = 1 ∧ (∀ i < MT.N, Rep (MT.T i) (c i)) ∧
    (∀ y ∈ Mt, ∃ i < MT.N, c i = y) ∧ (∀ i < MT.N, c i ∈ Mt) := by
  have hg : ∀ k < MT.ng, PRep 14 4 (MT.G k) (gM k) := fun k hk x => rep_G' k hk x
  obtain ⟨c, hc0, hc, hmem, hcl, hinj⟩ := leftOrb_reps (n := 14) (w := 4) (by norm_num) hg
    MT.cl MT.tr (by decide) (fun x => rep_T0' x) (by decide) MT.k
  refine ⟨c, hc0, hc, fun y hy => ?_, hmem⟩
  have := (group_of_reps (MonoidHom.id _) (fun _ _ h => h) gM c ⟨0, by decide, hc0⟩ hmem hcl
    hinj).2 y hy
  exact this

@[expose] def kOf (k₁ k₂ k₃ j : Nat) : Nat := if j = 0 then k₁ else if j = 1 then k₂ else k₃

@[expose] def gen6 (m : Nat → Nat) (l : Nat) : Wr 7 := eW (2 * m (l / 2) + l % 2)

theorem g6_eq (st l : Nat) :
    g6 CFSG.KD.E64CC.D st l = CFSG.KD.E64CC.D (2 * fget st (l / 2) 4 + l % 2) := by
  unfold g6
  congr 2
  exact Nat.and_one_is_mod l

theorem rep_g6 {st : Nat} (hm : ∀ j < 3, fget st j 4 < 14) {l : Nat} (hl : l < 6) :
    Rep (g6 CFSG.KD.E64CC.D st l) (phi (gen6 (fun j => fget st j 4) l)) := by
  rw [g6_eq]
  have := hm (l / 2) (by omega)
  exact rep_P (by omega)

theorem image_gen6 (m : Nat → Nat) :
    phi '' (gen6 m '' {l | l < 6}) = (fun l => phi (gen6 m l)) '' {l | l < 6} :=
  Set.image_image _ _ _

theorem map_closure_gen6 (m : Nat → Nat) :
    (Subgroup.closure (gen6 m '' {l | l < 6})).map phi =
      Subgroup.closure ((fun l => phi (gen6 m l)) '' {l | l < 6}) := by
  rw [MonoidHom.map_closure, image_gen6]

theorem closure_gen6_le {m m' : Nat → Nat} (h : ∀ j < 3, ∃ j' < 3, m j = m' j') :
    Subgroup.closure (gen6 m '' {l | l < 6}) ≤ Subgroup.closure (gen6 m' '' {l | l < 6}) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨j', hj', e⟩ := h (l / 2) (by simp only [Set.mem_setOf_eq] at hl; omega)
  refine Subgroup.subset_closure ⟨2 * j' + l % 2, by simp only [Set.mem_setOf_eq]; omega, ?_⟩
  simp only [gen6]
  rw [show (2 * j' + l % 2) / 2 = j' by omega, show (2 * j' + l % 2) % 2 = l % 2 by omega, e]

theorem gen6_mem_Mt {m : Nat → Nat} (hm : ∀ j < 3, m j < 14) {l : Nat} (hl : l < 6) :
    phi (gen6 m l) ∈ Mt := by
  obtain ⟨c, -, hc, -, hmem⟩ := enum_facts
  have hg : 2 * m (l / 2) + l % 2 < 28 := by
    have := hm (l / 2) (by omega)
    omega
  obtain ⟨hix, heq⟩ := ixK_spec (PK.allN_iff.1 ix_ok _ hg)
  have h1 := rep_eqK' (rep_P hg) heq
  change phi (eW (2 * m (l / 2) + l % 2)) ∈ Mt
  rw [← prep_eq (hc _ hix) h1]
  exact hmem _ hix

theorem closure_le_Mt {m : Nat → Nat} (hm : ∀ j < 3, m j < 14) :
    ∀ x ∈ Subgroup.closure (gen6 m '' {l | l < 6}), phi x ∈ Mt := by
  intro x hx
  have : (Subgroup.closure (gen6 m '' {l | l < 6})).map phi ≤ Mt := by
    rw [map_closure_gen6, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact gen6_mem_Mt hm hl
  exact this ⟨x, hx, rfl⟩

theorem pi_not_mem : phi (allOnes 7) ∉ Mt := by
  intro h
  obtain ⟨c, -, hc, hall, -⟩ := enum_facts
  obtain ⟨i, hi, e⟩ := hall _ h
  have hr := hc i hi
  rw [e] at hr
  obtain ⟨x, hx⟩ := exists_ne_pi hr (piK_spec pi_ok i hi)
  exact hx (phi_pi' x)

theorem triple {k₁ k₂ k₃ : Nat} (h₁ : k₁ < 14) (h₂ : k₂ < 14) (h₃ : k₃ < 14) {a : Wr 7}
    (ha : a ∈ Subgroup.closure (gen6 (kOf k₁ k₂ k₃) '' {l | l < 6}))
    (hc : ∀ l < 6, mkQ 7 a * mkQ 7 (gen6 (kOf k₁ k₂ k₃) l) =
      mkQ 7 (gen6 (kOf k₁ k₂ k₃) l) * mkQ 7 a) :
    mkQ 7 a ∈ ⁅(Subgroup.closure (gen6 (kOf k₁ k₂ k₃) '' {l | l < 6})).map (mkQ 7),
      (Subgroup.closure (gen6 (kOf k₁ k₂ k₃) '' {l | l < 6})).map (mkQ 7)⁆ := by
  set km := kOf k₁ k₂ k₃
  set Hs := Subgroup.closure (gen6 km '' {l | l < 6})
  have hkm : ∀ j < 3, km j < 14 := by
    intro j hj
    simp only [km, kOf]
    split_ifs <;> assumption
  have hHM := closure_le_Mt hkm
  have hcomm : ∀ l < 6, a * gen6 km l = gen6 km l * a := by
    intro l hl
    have hgl : gen6 km l ∈ Hs := Subgroup.subset_closure ⟨l, hl, rfl⟩
    have e := hc l hl
    rw [← map_mul, ← map_mul, mkQ_eq_iff] at e
    rcases e with e | e
    · exact inv_mul_eq_one.1 e
    · exfalso
      apply pi_not_mem
      rw [← e]
      exact hHM _ (mul_mem (inv_mem (mul_mem ha hgl)) (mul_mem hgl ha))
  obtain ⟨c, hc0, hcT, hall, -⟩ := enum_facts
  obtain ⟨i, hi, hci⟩ := hall _ (hHM a ha)
  have hrep : Rep (MT.T i) (phi a) := hci ▸ hcT i hi
  have hcen : ∀ j < 3, cenK (MT.T i) (CFSG.KD.E64CC.D (2 * km j))
      (CFSG.KD.E64CC.D (2 * km j + 1)) = true := by
    intro j hj
    have hk := hkm j hj
    have e0 : gen6 km (2 * j) = eW (2 * km j) := by
      simp only [gen6]
      rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega, Nat.add_zero]
    have e1 : gen6 km (2 * j + 1) = eW (2 * km j + 1) := by
      simp only [gen6]
      rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
    rw [cenK_iff hrep (rep_P (by omega)) (rep_P (by omega)), ← e0, ← e1, ← map_mul, ← map_mul,
      ← map_mul, ← map_mul, hcomm _ (by omega), hcomm _ (by omega)]
    exact ⟨rfl, rfl⟩
  have hb : ∀ j < 3, (CFSG.KD.E64CC.D (70 + km j)).testBit i = true := fun j hj =>
    cmK_spec (cm_ok _ (hkm j hj)) i hi (hcen j hj)
  have hk1 : km 0 = k₁ := rfl
  have hk2 : km 1 = k₂ := rfl
  have hk3 : km 2 = k₃ := rfl
  obtain ⟨j, hj, hji⟩ := clK_spec (PK.allN_iff.1 cl_ok k₁ h₁) (hk1 ▸ hb 0 (by norm_num))
  by_cases hi0 : i = 0
  · have : phi a = phi 1 := by rw [← hci, hi0, hc0, map_one]
    rw [phi_injective this, map_one]
    exact one_mem _
  have htr := PK.allN_iff.1 (PK.allN_iff.1 (trip_ok k₁ h₁) k₂ h₂) k₃ h₃
  obtain ⟨r, hr0, hr, hrc, hs, hset⟩ := tripK_spec htr hj (by rw [hji]; exact hi0)
    (by rw [hji]; exact hk2 ▸ hb 1 (by norm_num)) (by rw [hji]; exact hk3 ▸ hb 2 (by norm_num))
  set st := CFSG.KD.E64CC.D (84 + fld(CFSG.KD.E64CC.D (328 + r), 14, 1023))
  have hmask := mask3_iff (beq_true hset)
  have hst : ∀ j < 3, ∃ j' < 3, fget st j 4 = km j' := by
    intro j hj
    have := (hmask (fget st j 4)).1 (by interval_cases j <;> simp)
    rcases this with e | e | e
    · exact ⟨0, by norm_num, e⟩
    · exact ⟨1, by norm_num, e⟩
    · exact ⟨2, by norm_num, e⟩
  have hts : ∀ j < 3, ∃ j' < 3, km j = fget st j' 4 := by
    intro j hj
    have := (hmask (km j)).2 (by interval_cases j <;> simp [hk1, hk2, hk3])
    rcases this with e | e | e
    · exact ⟨0, by norm_num, e⟩
    · exact ⟨1, by norm_num, e⟩
    · exact ⟨2, by norm_num, e⟩
  have hm14 : ∀ j < 3, fget st j 4 < 14 := by
    intro j hj
    obtain ⟨j', hj', e⟩ := hst j hj
    rw [e]
    exact hkm j' hj'
  have hHe : Subgroup.closure (gen6 (fun j => fget st j 4) '' {l | l < 6}) = Hs :=
    le_antisymm (closure_gen6_le hst) (closure_gen6_le hts)
  have hγ : ∀ l < 6, Rep (g6 CFSG.KD.E64CC.D st l) (phi (gen6 (fun j => fget st j 4) l)) :=
    fun l hl => rep_g6 hm14 hl
  have hrT : Rep (MT.T (fget (CFSG.KD.E64CC.D (328 + r)) 0 14)) (phi a) := by
    rw [hrc, hji]
    exact hrep
  have hmemH : phi a ∈ Subgroup.closure ((fun l => phi (gen6 (fun j => fget st j 4) l)) ''
      {l | l < 6}) := by
    rw [← map_closure_gen6, hHe]
    exact ⟨a, ha, rfl⟩
  obtain ⟨hw, ho⟩ := resK_spec (res_ok r hr0 hr)
  by_cases hk : Nat.shiftRight (CFSG.KD.E64CC.D (328 + r)) 24 = 0
  · obtain ⟨x, hx, y, hy, e⟩ := witK_spec hrT hγ (hw hk)
    rw [← map_closure_gen6, hHe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, ← map_mul] at e
    have e2 := phi_injective e
    have hcm : a = ⁅x', y'⁆ := by
      rw [commutatorElement_def, ← e2]
      group
    rw [hcm, ← Subgroup.map_commutator]
    exact ⟨_, Subgroup.commutator_mem_commutator hx' hy', rfl⟩
  · obtain ⟨hsz, hout⟩ := outK_spec hrT (ho hk)
    exact absurd (setK_spec (set_ok _ hs) hγ hsz _ hmemH) hout

theorem memBar_eq (l : Fin 7) (h : (fanoLines.get ⟨l, by simp [fanoLines]⟩)ᶜ.card = 4) (b : Bool) :
    memBar _ h b = (Subgroup.closure ({eW (4 * l.val + 2 * (bif b then 0 else 1)),
      eW (4 * l.val + 2 * (bif b then 0 else 1) + 1)} : Set (Wr 7))).map (mkQ 7) := by
  rw [← memAt_eq_closure]
  rfl

theorem pair_eq (m : Nat → Nat) :
    gen6 m '' {l | l < 6} = ({eW (2 * m 0), eW (2 * m 0 + 1)} ∪ {eW (2 * m 1), eW (2 * m 1 + 1)} ∪
      {eW (2 * m 2), eW (2 * m 2 + 1)} : Set (Wr 7)) := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    interval_cases l <;> simp [gen6]
  · rintro (((h | h) | (h | h)) | (h | h))
    · exact ⟨0, by norm_num, by simp [gen6, h]⟩
    · exact ⟨1, by norm_num, by simp [gen6, h]⟩
    · exact ⟨2, by norm_num, by simp [gen6, h]⟩
    · exact ⟨3, by norm_num, by simp [gen6, h]⟩
    · exact ⟨4, by norm_num, by simp [gen6, h]⟩
    · exact ⟨5, by norm_num, by simp [gen6, h]⟩

theorem e64CenComm_kernel :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64CenComm := by
  intro α₁ hα₁ α₂ hα₂ α₃ hα₃ h₁ h₂ h₃ b₁ b₂ b₃ a ha hc₁ hc₂ hc₃
  obtain ⟨ℓ₁, hℓ₁, rfl⟩ := hα₁
  obtain ⟨ℓ₂, hℓ₂, rfl⟩ := hα₂
  obtain ⟨ℓ₃, hℓ₃, rfl⟩ := hα₃
  obtain ⟨n₁, rfl⟩ := List.mem_iff_get.1 hℓ₁
  obtain ⟨n₂, rfl⟩ := List.mem_iff_get.1 hℓ₂
  obtain ⟨n₃, rfl⟩ := List.mem_iff_get.1 hℓ₃
  set l₁ : Fin 7 := ⟨n₁, n₁.2⟩
  set l₂ : Fin 7 := ⟨n₂, n₂.2⟩
  set l₃ : Fin 7 := ⟨n₃, n₃.2⟩
  have e₁ : memBar _ h₁ b₁ = _ := memBar_eq l₁ h₁ b₁
  have e₂ : memBar _ h₂ b₂ = _ := memBar_eq l₂ h₂ b₂
  have e₃ : memBar _ h₃ b₃ = _ := memBar_eq l₃ h₃ b₃
  set k₁ := 2 * l₁.val + (bif b₁ then 0 else 1)
  set k₂ := 2 * l₂.val + (bif b₂ then 0 else 1)
  set k₃ := 2 * l₃.val + (bif b₃ then 0 else 1)
  have hk₁ : k₁ < 14 := by have := l₁.2; cases b₁ <;> simp [k₁] <;> omega
  have hk₂ : k₂ < 14 := by have := l₂.2; cases b₂ <;> simp [k₂] <;> omega
  have hk₃ : k₃ < 14 := by have := l₃.2; cases b₃ <;> simp [k₃] <;> omega
  have f₁ : 4 * l₁.val + 2 * (bif b₁ then 0 else 1) = 2 * k₁ := by cases b₁ <;> simp [k₁] <;> omega
  have f₂ : 4 * l₂.val + 2 * (bif b₂ then 0 else 1) = 2 * k₂ := by cases b₂ <;> simp [k₂] <;> omega
  have f₃ : 4 * l₃.val + 2 * (bif b₃ then 0 else 1) = 2 * k₃ := by cases b₃ <;> simp [k₃] <;> omega
  rw [f₁] at e₁
  rw [f₂] at e₂
  rw [f₃] at e₃
  have hH : memBar _ h₁ b₁ ⊔ memBar _ h₂ b₂ ⊔ memBar _ h₃ b₃ =
      (Subgroup.closure (gen6 (kOf k₁ k₂ k₃) '' {l | l < 6})).map (mkQ 7) := by
    rw [e₁, e₂, e₃, ← Subgroup.map_sup, ← Subgroup.map_sup, pair_eq, Subgroup.closure_union,
      Subgroup.closure_union]
    rfl
  rw [hH] at ha ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  refine triple hk₁ hk₂ hk₃ ha' fun l hl => ?_
  have hm₁ : ∀ i < 2, mkQ 7 (eW (2 * k₁ + i)) ∈ memBar _ h₁ b₁ := by
    intro i hi
    rw [e₁]
    interval_cases i
    · exact ⟨eW (2 * k₁ + 0), Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨eW (2 * k₁ + 1), Subgroup.subset_closure (by simp), rfl⟩
  have hm₂ : ∀ i < 2, mkQ 7 (eW (2 * k₂ + i)) ∈ memBar _ h₂ b₂ := by
    intro i hi
    rw [e₂]
    interval_cases i
    · exact ⟨eW (2 * k₂ + 0), Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨eW (2 * k₂ + 1), Subgroup.subset_closure (by simp), rfl⟩
  have hm₃ : ∀ i < 2, mkQ 7 (eW (2 * k₃ + i)) ∈ memBar _ h₃ b₃ := by
    intro i hi
    rw [e₃]
    interval_cases i
    · exact ⟨eW (2 * k₃ + 0), Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨eW (2 * k₃ + 1), Subgroup.subset_closure (by simp), rfl⟩
  change mkQ 7 a' * mkQ 7 (eW (2 * kOf k₁ k₂ k₃ (l / 2) + l % 2)) =
    mkQ 7 (eW (2 * kOf k₁ k₂ k₃ (l / 2) + l % 2)) * mkQ 7 a'
  interval_cases l
  · exact hc₁ _ (hm₁ 0 (by norm_num))
  · exact hc₁ _ (hm₁ 1 (by norm_num))
  · exact hc₂ _ (hm₂ 0 (by norm_num))
  · exact hc₂ _ (hm₂ 1 (by norm_num))
  · exact hc₃ _ (hm₃ 0 (by norm_num))
  · exact hc₃ _ (hm₃ 1 (by norm_num))

end CertificateChecks.KernelE64CC

end
