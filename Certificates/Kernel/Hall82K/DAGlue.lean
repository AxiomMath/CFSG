module

public import Certificates.Kernel.Hall82K.RmGlue
public import Certificates.Kernel.Hall82K.DA

public section

namespace CFSG.KD.Hall82A

open CFSG.KC.Hall82K CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.KC.Ord CFSG.KD.Hall82E CFSG.CGT.Hall82
open CFSG.KD.Hall82R CFSG.ComponentClassification.AS81.Hexa CFSG.Monster.B.Co2
open CFSG.ComponentClassification.AS81.HeTri CFSG.ComponentClassification.AS81.HeSylow

theorem oval_iff (v : Fin 64) : IsOvalVec v ↔ inKK v.val = true := by
  have h := beqB_eq82 (allN_spec82 ch840004mg_kmask v.val v.2)
  change v.val ∈ hallKList ↔ _
  rw [← memL_iff82, h]

theorem mem_hexaM_of_code {g : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) {i : ℕ} (hi : i < 2160)
    (hc : codeL g = EM i) : g ∈ hexaM := by
  obtain ⟨x, hx, hxc⟩ := hexaM_enum.2.2 i hi
  rw [code_inj hg (hexaM_enum.2.1 x hx).1 (hc.trans hxc.symm)]
  exact hx

theorem hexaL_le : hexaL ≤ hexaM := by
  obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hallLGens = [a0, a1] := ⟨_, _, rfl⟩
  have hz : zipArrK [52077576321, 61871938592] [a0, a1] = true := by
    rw [← h]
    exact ch840001enLG
  have hL : hexaL = grpN 64 [a0, a1] := by
    rw [← h]
  obtain ⟨h0, h1⟩ := andB_eq_true ch840002li
  obtain ⟨h0i, h0c⟩ := andB_eq_true h0
  obtain ⟨h1i, h1c⟩ := andB_eq_true h1
  obtain ⟨-, hA0, hc0, -⟩ := permK_sound ch840001pk.2.2.1 (zipArrK_getD hz 0 (by norm_num))
  obtain ⟨-, hA1, hc1, -⟩ := permK_sound ch840001pk.2.2.2 (zipArrK_getD hz 1 (by norm_num))
  rw [hL]
  refine grpN_le fun a ha => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact mem_hexaM_of_code hA0 (Nat.blt_eq.mp h0i) (hc0.trans (Nat.eq_of_beq_eq_true h0c).symm)
  · exact mem_hexaM_of_code hA1 (Nat.blt_eq.mp h1i) (hc1.trans (Nat.eq_of_beq_eq_true h1c).symm)

def kSub : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {x | ∀ v, IsOvalVec (x v) ↔ IsOvalVec v}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb v => (ha (b v)).trans (hb v)
  inv_mem' := fun {a} ha v => by
    rw [← ha (a⁻¹ v)]
    simp

theorem mem_kSub_of {x : Equiv.Perm (Fin 64)} {c : ℕ} (hv : ∀ v : Fin 64, (x v).val = apL c v.val)
    (hk : kIffK c = true) : x ∈ kSub := by
  intro v
  have h := beqB_eq82 ((allN_iff _ _).1 hk v.val v.2)
  rw [oval_iff, oval_iff, hv, ← h]

theorem hexaM_le_kSub : hexaM ≤ kSub := by
  obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hexaMGens = [a0, a1] := ⟨_, _, rfl⟩
  have hz : zipArrK [4439643498, 34633937090] [a0, a1] = true := by
    rw [← h]
    exact ch840004mg_code
  have hM : hexaM = grpN 64 [a0, a1] := by
    rw [← h]
  obtain ⟨-, -, -, hv0⟩ := permK_sound ch840001pk.1 (zipArrK_getD hz 0 (by norm_num))
  obtain ⟨-, -, -, hv1⟩ := permK_sound ch840001pk.2.1 (zipArrK_getD hz 1 (by norm_num))
  rw [hM]
  refine grpN_le fun a ha => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact mem_kSub_of hv0 ch840002kiff.1
  · exact mem_kSub_of hv1 ch840002kiff.2

theorem oval_apply {x : Equiv.Perm (Fin 64)} (hx : x ∈ hexaM) {h : Fin 64} (hh : IsOvalVec h) :
    IsOvalVec (x h) :=
  (hexaM_le_kSub hx h).2 hh

theorem lin : ∀ x ∈ hexaM, ∀ v w, x (xorF v w) = xorF (x v) (x w) :=
  fun x hx => mem_addSub.1 (hexaM_enum.2.1 x hx).1

theorem apply_zero {x : Equiv.Perm (Fin 64)} (hx : x ∈ hexaM) : x 0 = 0 := by
  have h := lin x hx 0 0
  have e : xorF 0 0 = (0 : Fin 64) := by decide
  rw [e] at h
  rw [h]
  apply Fin.ext
  rw [val_xorF, Nat.xor_self]
  rfl

theorem trans_at (v : Fin 64) : ∃ a ∈ hexaL,
    (IsOvalVec v → a 1 = v) ∧ (v ≠ 0 → ¬ IsOvalVec v → a 5 = v) := by
  have hc := (allN_iff _ _).1 ch840002tr v.val v.2
  simp only [transAtK, letB_eq] at hc
  obtain ⟨hw, hc⟩ := andB_eq_true hc
  obtain ⟨h1, h2⟩ := andB_eq_true hc
  obtain ⟨a, ha, hac⟩ := hexaL_enum.2.2 _ (Nat.blt_eq.mp hw)
  have haA := (hexaL_enum.2.1 a ha).1
  refine ⟨a, ha, fun hv => ?_, fun hv0 hv => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (impB_eq_true h1 ((oval_iff v).1 hv))
    exact Fin.ext ((apL_code haA 1).trans (by rw [hac]; exact e))
  · rcases orB_eq_true82 h2 with hk | h2
    · exact absurd ((oval_iff v).2 hk) hv
    rcases orB_eq_true82 h2 with h0 | h5
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true h0)) hv0
    · exact Fin.ext ((apL_code haA 5).trans (by rw [hac]; exact Nat.eq_of_beq_eq_true h5))

theorem oval_trans : ∀ h h', IsOvalVec h → IsOvalVec h' → ∃ a ∈ hexaL, a h = h' := by
  intro h h' hh hh'
  obtain ⟨a, ha, ha1, -⟩ := trans_at h
  obtain ⟨b, hb, hb1, -⟩ := trans_at h'
  refine ⟨b * a⁻¹, hexaL.mul_mem hb (hexaL.inv_mem ha), ?_⟩
  rw [Equiv.Perm.mul_apply, ← ha1 hh]
  simp [hb1 hh']

theorem five_trans : ∀ v, v ≠ 0 → ¬ IsOvalVec v → ∃ a ∈ hexaL, a 5 = v := by
  intro v hv0 hv
  obtain ⟨a, ha, -, ha5⟩ := trans_at v
  exact ⟨a, ha, ha5 hv0 hv⟩

theorem five_not_oval : ¬ IsOvalVec 5 := by decide

theorem orbit_oval_eq {X : Subgroup (Equiv.Perm (Fin 64))} (hXL : hexaL ≤ X) (hXM : X ≤ hexaM)
    {h : Fin 64} (hh : IsOvalVec h) : MulAction.orbit ↥X h = {v : Fin 64 | IsOvalVec v} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact oval_apply (hXM g.2) hh
  · intro hv
    obtain ⟨a, haL, hah⟩ := oval_trans h v hh hv
    exact ⟨⟨a, hXL haL⟩, by simpa using hah⟩

theorem orbit_C_eq {X : Subgroup (Equiv.Perm (Fin 64))} (hXL : hexaL ≤ X) (hXM : X ≤ hexaM)
    {v : Fin 64} (hv : v ≠ 0 ∧ ¬ IsOvalVec v) :
    MulAction.orbit ↥X v = {w : Fin 64 | w ≠ 0 ∧ ¬ IsOvalVec w} := by
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    have hg := hexaM_le_kSub (hXM g.2)
    have hg0 := apply_zero (hXM g.2)
    constructor
    · intro hzero
      have hzero' : (g : Equiv.Perm (Fin 64)) v = 0 := by
        simpa [Subgroup.smul_def] using hzero
      rw [← hg0] at hzero'
      exact hv.1 ((g : Equiv.Perm (Fin 64)).injective hzero')
    · intro hoval
      have h' : IsOvalVec ((g : Equiv.Perm (Fin 64)) v) := by
        simpa [Subgroup.smul_def] using hoval
      exact hv.2 ((hg v).1 h')
  · intro hw
    obtain ⟨a, haL, ha5⟩ := five_trans v hv.1 hv.2
    obtain ⟨b, hbL, hb5⟩ := five_trans w hw.1 hw.2
    refine ⟨⟨b * a⁻¹, hXL (hexaL.mul_mem hbL (hexaL.inv_mem haL))⟩, ?_⟩
    have ha_inv : a⁻¹ v = 5 := by
      rw [← ha5]
      simp
    have hba : (b * a⁻¹) v = w := by
      rw [Equiv.Perm.mul_apply, ha_inv, hb5]
    simpa using hba

theorem ncard_oval : ({v : Fin 64 | IsOvalVec v} : Set (Fin 64)).ncard = 18 := by
  rw [Set.ncard_eq_toFinset_card']
  decide +kernel

theorem ncard_C : ({v : Fin 64 | v ≠ 0 ∧ ¬ IsOvalVec v} : Set (Fin 64)).ncard = 45 := by
  rw [Set.ncard_eq_toFinset_card']
  decide +kernel

theorem card_stabSub_mul_ncard_orbit {X : Subgroup (Equiv.Perm (Fin 64))}
    {v : Fin 64} {s : Set (Fin 64)} (horbit : MulAction.orbit ↥X v = s) :
    Nat.card (stabSub X v) * s.ncard = Nat.card X := by
  have hstab : Nat.card (stabSub X v) = Nat.card (MulAction.stabilizer ↥X v) := by
    have hsub : (stabSub X v).subgroupOf X =
        (MulAction.stabilizer (Equiv.Perm (Fin 64)) v).subgroupOf X := by
      ext x
      simp [stabSub, Subgroup.mem_subgroupOf]
    calc Nat.card (stabSub X v)
        = Nat.card ((stabSub X v).subgroupOf X) :=
          (Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (inf_le_left : stabSub X v ≤ X)).toEquiv).symm
      _ = Nat.card ((MulAction.stabilizer (Equiv.Perm (Fin 64)) v).subgroupOf X) := by
            rw [hsub]
      _ = Nat.card (MulAction.stabilizer ↥X v) := by
            rw [MulAction.stabilizer_subgroupOf]
  rw [hstab, ← horbit, ← MulAction.index_stabilizer]
  exact Subgroup.card_mul_index (H := MulAction.stabilizer ↥X v) (G := ↥X)

theorem card_stab_oval : ∀ h, IsOvalVec h → Nat.card (stabSub hexaM h) = 120 := by
  intro h hh
  have hmul := card_stabSub_mul_ncard_orbit (orbit_oval_eq hexaL_le le_rfl hh)
  rw [ncard_oval, hexaM_enum.1] at hmul
  omega

theorem card_stab : ∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaM v) = 48 := by
  intro v hv0 hvK
  have hmul := card_stabSub_mul_ncard_orbit (orbit_C_eq hexaL_le le_rfl ⟨hv0, hvK⟩)
  rw [ncard_C, hexaM_enum.1] at hmul
  omega

theorem card_stabL_oval : ∀ h, IsOvalVec h → Nat.card (stabSub hexaL h) = 60 := by
  intro h hh
  have hmul := card_stabSub_mul_ncard_orbit (orbit_oval_eq le_rfl hexaL_le hh)
  rw [ncard_oval, hexaL_enum.1] at hmul
  omega

theorem card_stabL : ∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaL v) = 24 := by
  intro v hv0 hvK
  have hmul := card_stabSub_mul_ncard_orbit (orbit_C_eq le_rfl hexaL_le ⟨hv0, hvK⟩)
  rw [ncard_C, hexaL_enum.1] at hmul
  omega

theorem nv_one {x : Equiv.Perm (Fin 64)} (hx : x ∈ hexaM) (hx1 : x 1 = 1) (hne : x ≠ 1)
    (h16 : x ^ 16 = 1) : ∃ a ∈ hexaL, a 1 = 1 ∧ (x * (a * x * a⁻¹) ^ 15) ^ 16 ≠ 1 := by
  obtain ⟨hxA, k, hk, hxk⟩ := hexaM_enum.2.1 x hx
  have hchk := (allN_iff _ _).1 ch840002nv k hk
  simp only [nvAtOK, letB_eq] at hchk
  rw [← hxk] at hchk
  have hf : fixAtK 1 (codeL x) = true := by
    have h := apL_code hxA 1
    rw [hx1] at h
    have h' : apL (codeL ⇑x) 1 = 1 := h.symm
    unfold fixAtK
    rw [h']
    rfl
  have hn : negK (Nat.beq (codeL x) idK) = true := by
    cases h : Nat.beq (codeL x) idK
    · rfl
    · exact absurd (code_inj hxA addSub.one_mem (Nat.eq_of_beq_eq_true h)) hne
  have hp : Nat.beq (powL (codeL x) 16) idK = true := by
    rw [← codeL_pow hxA, h16, codeL_one]
    exact Nat.beq_refl _
  have hw := impB_eq_true hchk (by rw [hf, hn, hp]; rfl)
  simp only [nvWitOK, letB_eq] at hw
  obtain ⟨hw1, hw⟩ := andB_eq_true hw
  obtain ⟨hw2, hw⟩ := andB_eq_true hw
  obtain ⟨hw3, hw⟩ := andB_eq_true hw
  obtain ⟨hw4, hw5⟩ := andB_eq_true hw
  obtain ⟨a, haL, haA, hac, haic⟩ :=
    exists_hexaL_pair (Nat.blt_eq.mp hw1) (Nat.blt_eq.mp hw2) (Nat.eq_of_beq_eq_true hw4)
  refine ⟨a, haL, Fin.ext ((apL_code haA 1).trans (by rw [hac]; exact Nat.eq_of_beq_eq_true hw3)),
    fun hq16 => ?_⟩
  have hzA : a * x * a⁻¹ ∈ addSub :=
    addSub.mul_mem (addSub.mul_mem haA hxA) (addSub.inv_mem haA)
  have hqA : x * (a * x * a⁻¹) ^ 15 ∈ addSub := addSub.mul_mem hxA (addSub.pow_mem hzA 15)
  have hcode := codeL_pow hqA 16
  rw [hq16, codeL_one, codeL_mul hxA (addSub.pow_mem hzA 15), codeL_pow hzA,
    codeL_mul (addSub.mul_mem haA hxA) (addSub.inv_mem haA), codeL_mul haA hxA, hac,
    haic] at hcode
  have h := negK_eq_true hw5
  rw [← hcode, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem eq_bot_of_oval : ∀ h, IsOvalVec h → ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM →
    IsPGroup 2 B → (∀ b ∈ B, b h = h) → (∀ a ∈ hexaL, a h = h → ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
    B = ⊥ := by
  intro h hh B hB h2 hfix hnorm
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  obtain ⟨c, hcL, hc1, -⟩ := trans_at h
  have hch : c 1 = h := hc1 hh
  set g := c⁻¹ with hg
  have hgL : g ∈ hexaL := hexaL.inv_mem hcL
  have hgh : g h = 1 := by
    rw [hg, ← hch]
    simp
  let φ := MulAut.conj g
  have hφ : ∀ y, φ y = g * y * g⁻¹ := fun _ => rfl
  have hx : φ b ∈ hexaM := by
    rw [hφ]
    exact hexaM.mul_mem (hexaM.mul_mem (hexaL_le hgL) (hB hb)) (hexaM.inv_mem (hexaL_le hgL))
  have hx1 : φ b 1 = 1 := by
    rw [hφ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hgh]
    simp [hfix b hb]
  have hne : φ b ≠ 1 := fun e => hb1 ((map_eq_one_iff φ φ.injective).1 e)
  have h16 : φ b ^ 16 = 1 := by
    rw [← map_pow, pow16_of_two hB h2 hb, map_one]
  obtain ⟨a, haL, ha1, hq⟩ := nv_one hx hx1 hne h16
  have ha'L : g⁻¹ * a * g ∈ hexaL :=
    hexaL.mul_mem (hexaL.mul_mem (hexaL.inv_mem hgL) haL) hgL
  have ha'h : (g⁻¹ * a * g) h = h := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgh, ha1, ← hgh]
    simp
  have hz := hnorm _ ha'L ha'h b hb
  have hy : b * ((g⁻¹ * a * g) * b * (g⁻¹ * a * g)⁻¹) ^ 15 ∈ B :=
    B.mul_mem hb (B.pow_mem hz 15)
  have hy16 := pow16_of_two hB h2 hy
  have hφa : φ (g⁻¹ * a * g) = a := by
    rw [hφ]
    group
  have hφy : φ (b * ((g⁻¹ * a * g) * b * (g⁻¹ * a * g)⁻¹) ^ 15) =
      φ b * (a * φ b * a⁻¹) ^ 15 := by
    simp only [map_mul, map_pow, map_inv, hφa]
  apply hq
  rw [← hφy, ← map_pow, hy16, map_one]

theorem zeta_fix : ∀ v, heZeta v = v → v = 0 := by
  intro v hv
  obtain ⟨hz, hzv⟩ := andB_eq_true ch840002z
  obtain ⟨-, -, -, hval⟩ := permK_sound hz ch840002zc
  have hc := (allN_iff _ _).1 hzv v.val v.2
  rcases orB_eq_true82 hc with h0 | hm
  · exact Fin.ext (Nat.eq_of_beq_eq_true h0)
  · exfalso
    have e := hval v
    have e' : (permOfArr 64 heZetaArr v) = v := hv
    rw [e'] at e
    have h' := negK_eq_true hm
    rw [← e, Nat.beq_refl] at h'
    exact Bool.noConfusion h'

end CFSG.KD.Hall82A
