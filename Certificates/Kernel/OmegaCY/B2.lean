module

public import Certificates.Kernel.A45Cls.Glue107
public import Certificates.Kernel.SporSch.Co2M.ThirdGlue
public import Certificates.Certificate3042Base
public import Certificates.Certificate3055Base

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.BfsPin
  CFSG.KC.ConjOrb Certificates.OmegaS107

local notation "P45" => Equiv.Perm (Fin 45)

abbrev bzG (j : ℕ) : Subgroup P45 := closure (bg j '' {k | k < 4})

theorem bz_enum_of {j : ℕ} {BG BT BE BD BS : ℕ → ℕ}
    (hbcl : ∀ i < 16, closPtL 45 6 4 16 BG BT BE i = true)
    (hbtr : ∀ i < 16, treePt 4 16 0 BE BD i = true) (hb0 : BT 0 = pidn 45 6)
    (hbK : distinctK 16 (fun i => pkeyK 45 6 ps (BT i)) BS = true)
    (hbw : bindWs 45 6 3 KA.G BG (bW j) 0 = true) (hl : (bW j).length = 4) :
    ∃ cb : ℕ → P45, (∀ i < 16, PRep 45 6 (BT i) (cb i) ∧ cb i ∈ bzG j) ∧ Nat.card (bzG j) = 16 := by
  have hbg : ∀ k < 4, PRep 45 6 (BG k) (bg j k) := fun k hk => (prep_word hbw (by omega)).1
  obtain ⟨cb, hcb, -, hcard⟩ := enum_A hbg hbcl hbtr (by norm_num) hb0 hbK
  exact ⟨cb, hcb, hcard⟩

theorem bz_enum0 : ∃ cb : ℕ → P45, (∀ i < 16, PRep 45 6 (BZ0.T i) (cb i) ∧ cb i ∈ bzG 0) ∧
    Nat.card (bzG 0) = 16 :=
  bz_enum_of BZ0.cl BZ0.tr ids3.2.2.1 BZ0.k binds3.2.2.2.2.2.2.2.1 rfl

theorem bz_enum1 : ∃ cb : ℕ → P45, (∀ i < 16, PRep 45 6 (BZ1.T i) (cb i) ∧ cb i ∈ bzG 1) ∧
    Nat.card (bzG 1) = 16 :=
  bz_enum_of BZ1.cl BZ1.tr ids3.2.2.2.1 BZ1.k binds3.2.2.2.2.2.2.2.2.1 rfl

theorem bz_enum2 : ∃ cb : ℕ → P45, (∀ i < 16, PRep 45 6 (BZ2.T i) (cb i) ∧ cb i ∈ bzG 2) ∧
    Nat.card (bzG 2) = 16 :=
  bz_enum_of BZ2.cl BZ2.tr ids3.2.2.2.2 BZ2.k binds3.2.2.2.2.2.2.2.2.2.1 rfl

theorem bz_at
    {T : Subgroup P45} (hT0 : T0 ≤ T) (hTA : T ≤ A) (hT2 : IsPGroup 2 T) {j : ℕ} (hj : j < 3)
    (huT : wvA (uW.getD j []) ∈ T) (huT0 : wvA (uW.getD j []) ∉ T0)
    {BG BT BE BD BS : ℕ → ℕ} (hbcl : ∀ i < 16, closPtL 45 6 4 16 BG BT BE i = true)
    (hbtr : ∀ i < 16, treePt 4 16 0 BE BD i = true) (hb0 : BT 0 = pidn 45 6)
    (hbK : distinctK 16 (fun i => pkeyK 45 6 ps (BT i)) BS = true)
    (hbw : bindWs 45 6 3 KA.G BG (bW j) 0 = true)
    (hy : (isInvK 45 6 (y2P j) && Nat.beq (fixK 45 6 (y2P j)) 15 &&
      !inPts 45 6 64 TZ.T (y2P j)) = true)
    (hb2 : b2K 45 6 3 32 TZ.G QZ.T BT (uP j) (y2P j) = true) :
    bzG j ≤ T ∧ (∀ a ∈ bzG j, ∀ b ∈ bzG j, a * b = b * a) ∧ (∀ a ∈ bzG j, a * a = 1) ∧
      Nat.card (bzG j) = 16 ∧ (∀ g ∈ T, ∀ b ∈ bzG j, g * b * g⁻¹ ∈ bzG j) ∧ ¬ bzG j ≤ T0 := by
  obtain ⟨c0, hc0, hc0all⟩ := t0_enum
  obtain ⟨cq, hcq, hcqall⟩ := q_enum
  have hbwl : (bW j).length = 4 := by interval_cases j <;> rfl
  have hbg : ∀ k < 4, PRep 45 6 (BG k) (bg j k) := fun k hk => (prep_word hbw (by omega)).1
  obtain ⟨cb, hcb, hcball, hcard⟩ := enum_A hbg hbcl hbtr (by norm_num) hb0 hbK
  set B2 := closure (bg j '' {k | k < 4}) with hB2
  set u := wvA (uW.getD j []) with hu_def
  have hlet := PK.allN_iff.1 (Bool.and_eq_true _ _ ▸ binds3.2.2.2.2.2.2.2.2.2.2).2 j hj
  rw [Bool.and_eq_true] at hlet
  have hu : PRep 45 6 (uP j) u := (prep_wvA hlet.1).1
  have hyb : y2p j < 64 := witBounds.2.2.1 j hj
  set y2 := c0 (y2p j) * u with hy2_def
  have hy2 : PRep 45 6 (y2P j) y2 := prep_pcomp hn45 (hc0 _ hyb).1 hu
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy
  obtain ⟨-, hyout⟩ := hy
  have hy2T0 : y2 ∉ T0 := by
    intro h
    obtain ⟨i, hi, e⟩ := hc0all y2 h
    rw [inPts_of hi (e ▸ (hc0 i hi).1) hy2] at hyout
    exact absurd hyout (by decide)
  have hy2T : y2 ∈ T := T.mul_mem (hT0 (hc0 _ hyb).2) huT
  simp only [b2K, Bool.and_eq_true] at hb2
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb2
  have hmemB : ∀ b : P45, b ∈ B2 ↔
      (b ∈ Q0 ∧ b * y2 = y2 * b) ∨ ∃ c ∈ Q0, c * y2 = y2 * c ∧ c * y2 = b := by
    intro b
    constructor
    · intro hb
      obtain ⟨m, hm, rfl⟩ := hcball b hb
      have h := PK.allN_iff.1 h1 m hm
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hq, hc⟩ | h
      · obtain ⟨k, hk, e⟩ := inPts_spec (fun i hi => (hcq i hi).1) hq (hcb m hm).1
        exact Or.inl ⟨e ▸ (hcq k hk).2, eq22_sound hc (hcb m hm).1 hy2 hy2 (hcb m hm).1⟩
      · obtain ⟨k, hk, e⟩ := exN_spec h
        rw [Bool.and_eq_true] at e
        refine Or.inr ⟨cq k, (hcq k hk).2, eq22_sound e.1 (hcq k hk).1 hy2 hy2 (hcq k hk).1, ?_⟩
        simpa using eq22_sound e.2 (hcq k hk).1 hy2 (hcb m hm).1 prep_pid
    · intro hb
      have key : ∀ c ∈ Q0, c * y2 = y2 * c → c ∈ B2 ∧ c * y2 ∈ B2 := by
        intro c hc hcy
        obtain ⟨k, hk, rfl⟩ := hcqall c hc
        have h := PK.allN_iff.1 h2 k hk
        simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
        rcases h with h | ⟨ha, hb'⟩
        · rw [eq22_of_eq (hcq k hk).1 hy2 hy2 (hcq k hk).1 hcy] at h
          exact absurd h (by decide)
        · obtain ⟨m, hm, e⟩ := inPts_spec (fun i hi => (hcb i hi).1) ha (hcq k hk).1
          obtain ⟨m', hm', e'⟩ := inPts_spec (fun i hi => (hcb i hi).1) hb'
            (prep_pcomp hn45 (hcq k hk).1 hy2)
          exact ⟨e ▸ (hcb m hm).2, e' ▸ (hcb m' hm').2⟩
      rcases hb with ⟨hq, hc⟩ | ⟨c, hc, hcy, rfl⟩
      · exact (key b hq hc).1
      · exact (key c hc hcy).2
  have hcomm : ∀ a ∈ B2, ∀ b ∈ B2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, hm, rfl⟩ := hcball a ha
    obtain ⟨m', hm', rfl⟩ := hcball b hb
    have h := PK.allN_iff.1 h3 m hm
    rw [Bool.and_eq_true] at h
    exact eq22_sound (PK.allN_iff.1 h.2 m' hm') (hcb m hm).1 (hcb m' hm').1 (hcb m' hm').1
      (hcb m hm).1
  have hsq : ∀ a ∈ B2, a * a = 1 := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := hcball a ha
    have h := PK.allN_iff.1 h3 m hm
    rw [Bool.and_eq_true] at h
    exact (isIdK_iff (prep_pcomp hn45 (hcb m hm).1 (hcb m hm).1)).1 h.1
  have hle : B2 ≤ T := by
    intro b hb
    rcases (hmemB b).1 hb with ⟨hq, -⟩ | ⟨c, hc, -, rfl⟩
    · exact hT0 (q0_le hq)
    · exact T.mul_mem (hT0 (q0_le hc)) hy2T
  have hTle : T ≤ closure (t0g '' {k | k < 3} ∪ {u}) := by
    intro x hx
    by_cases hxT0 : x ∈ T0
    · rw [← closure_t0g] at hxT0
      exact closure_mono Set.subset_union_left hxT0
    · obtain ⟨a, ha, rfl⟩ :=
        CFSG.OddStandard.SmallF3.Omega.Mo107.exists_mul_over hT0 hTA hT2 huT huT0 hx hxT0
      have ha' : a ∈ closure (t0g '' {k | k < 3}) := by
        rw [closure_t0g]
        exact ha
      exact mul_mem (closure_mono Set.subset_union_left ha')
        (subset_closure (Set.mem_union_right _ rfl))
  have hconjB : ∀ {g : P45} {G : ℕ}, PRep 45 6 G g →
      (∀ m < 16, exN 16 (fun m' => eq22 45 6 (mask 6) G (BT m) (BT m') G) = true) →
      ∀ b ∈ B2, g * b * g⁻¹ ∈ B2 := by
    intro g G hG hc b hb
    obtain ⟨m, hm, rfl⟩ := hcball b hb
    obtain ⟨m', hm', e⟩ := exN_spec (hc m hm)
    have e' := eq22_sound e hG (hcb m hm).1 (hcb m' hm').1 hG
    rw [e', mul_inv_cancel_right]
    exact (hcb m' hm').2
  have hnorm : ∀ g ∈ T, ∀ b ∈ B2, g * b * g⁻¹ ∈ B2 := by
    refine fun g hg => conj_closed_A (O := (B2 : Set P45)) ?_ g (hTle hg)
    rintro s (⟨k, hk, rfl⟩ | rfl)
    · exact hconjB (prep_t0g k hk) fun m hm => by
        have h := PK.allN_iff.1 h4 m hm
        rw [Bool.and_eq_true] at h
        exact PK.allN_iff.1 h.1 k hk
    · exact hconjB hu fun m hm => by
        have h := PK.allN_iff.1 h4 m hm
        rw [Bool.and_eq_true] at h
        exact h.2
  refine ⟨hle, hcomm, hsq, hcard, hnorm, fun h => hy2T0 (h ((hmemB y2).2 ?_))⟩
  exact Or.inr ⟨1, Q0.one_mem, by simp, by simp⟩

theorem exists_bz
    {T : Subgroup P45} (hT0 : T0 ≤ T) (hTA : T ≤ A) (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T)
    (hw0 : w ∉ T0) : ∃ j < 3, wvA (uW.getD j []) ∈ T ∧ wvA (uW.getD j []) ∉ T0 := by
  obtain ⟨c0, hc0, hc0all⟩ := t0_enum
  have hnorm := CFSG.OddStandard.SmallF3.Omega.Mo107.normal_over hT0 hTA hT2 hw hw0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlet⟩ := binds3
  simp only [Bool.and_eq_true] at hlet
  obtain ⟨⟨hlc, hlci⟩, hlu⟩ := hlet
  set c := wvA czW
  have hcz : PRep 45 6 czP c := (prep_wvA hlc).1
  have hcA : c ∈ A := (prep_wvA hlc).2
  have hczi : PRep 45 6 cziP (wvA cziW) := (prep_wvA hlci).1
  have hci : wvA cziW = c⁻¹ := by
    have h := zFacts.2.1
    rw [isIdK_iff (prep_pcomp hn45 hcz hczi)] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [hci] at hczi
  have htA : PRep 45 6 (KA.T KA.r0) (Certificates.P43Twin.tA ()) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
    rw [← bt]
    exact prep_cOf _
  set z := Certificates.OmegaT0.z0 ()
  have hz : PRep 45 6 zP z := prep_cOf _
  have hzc : z = c * Certificates.P43Twin.tA () * c⁻¹ := by
    rw [mul_assoc]
    exact eqP_sound zFacts.1 hz (prep_pcomp hn45 hcz (prep_pcomp hn45 htA hczi))
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := fixC_conj (Certificates.P43Twin.tA ()) c
    rw [← hzc, h, fix_tA] at h2
    exact absurd h2 (by decide)
  have hzT0 : ∀ t ∈ T0, z * t = t * z := by
    intro t ht
    rw [← closure_t0g] at ht
    have hle : closure (t0g '' {k | k < 3}) ≤ centralizer ({z} : Set P45) := by
      rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact mem_centralizer_singleton_iff.2
        (eq22_sound (PK.allN_iff.1 zFacts.2.2.2.2.1 k hk) hz (prep_t0g k hk) (prep_t0g k hk) hz).symm
    exact (mem_centralizer_singleton_iff.1 (hle ht)).symm
  have hzin : z ∈ T0 := by
    obtain ⟨i, hi, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) zFacts.2.2.2.2.2.2.2 hz
    exact e ▸ (hc0 i hi).2
  have hwz : w * z = z * w := by
    have hz' : w * z * w⁻¹ ∈ T0 := hnorm w hw z hzin
    obtain ⟨i, hi, e⟩ := hc0all _ hz'
    have hcomm : ∀ k < 3, c0 i * t0g k = t0g k * c0 i := by
      intro k hk
      have ht : w⁻¹ * t0g k * w⁻¹⁻¹ ∈ T0 := hnorm _ (T.inv_mem hw) _ (t0g_mem hk)
      have h := hzT0 _ ht
      rw [e]
      calc w * z * w⁻¹ * t0g k = w * (z * (w⁻¹ * t0g k * w⁻¹⁻¹)) * w⁻¹ := by group
        _ = w * ((w⁻¹ * t0g k * w⁻¹⁻¹) * z) * w⁻¹ := by rw [h]
        _ = t0g k * (w * z * w⁻¹) := by group
    have h := PK.allN_iff.1 zFacts.2.2.2.1 i hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · have : allN 3 (fun k => eq22 45 6 (mask 6) (TZ.T i) (TZ.G k) (TZ.G k) (TZ.T i)) = true :=
        PK.allN_iff.2 fun k hk => eq22_of_eq (hc0 i hi).1 (prep_t0g k hk) (prep_t0g k hk)
          (hc0 i hi).1 (hcomm k hk)
      rw [this] at h
      exact absurd h (by decide)
    · rw [isIdK_iff (hc0 i hi).1, e] at h
      exfalso
      apply hz1
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = 1 := by rw [h]; group
    · have h' := eqP_sound h (hc0 i hi).1 hz
      rw [e] at h'
      calc w * z = w * z * w⁻¹ * w := by group
        _ = z * w := by rw [h']
  have hwA : w ∈ A := hTA hw
  have hmem : c⁻¹ * w * c ∈ A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45) := by
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hcA) hwA) hcA, mem_centralizer_singleton_iff.2 ?_⟩
    have htz : Certificates.P43Twin.tA () = c⁻¹ * z * c := by rw [hzc]; group
    rw [htz]
    calc c⁻¹ * w * c * (c⁻¹ * z * c) = c⁻¹ * (w * z) * c := by group
      _ = c⁻¹ * (z * w) * c := by rw [hwz]
      _ = c⁻¹ * z * c * (c⁻¹ * w * c) := by group
  obtain ⟨i, hi, hpi⟩ := centA_eq.2.2 _ hmem
  have hX : PRep 45 6 (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.T i) cziP)) w := by
    have h := prep_pcomp hn45 hcz (prep_pcomp hn45 hpi hczi)
    have e : c * (c⁻¹ * w * c * c⁻¹) = w := by group
    rwa [e] at h
  have hww : w * w ∈ T0 := by
    by_contra h
    obtain ⟨a, ha, e⟩ :=
      CFSG.OddStandard.SmallF3.Omega.Mo107.exists_mul_over hT0 hTA hT2 hw hw0 (T.mul_mem hw hw) h
    exact hw0 (mul_right_cancel e ▸ ha)
  have hcos := PK.allN_iff.1 cosets i hi
  unfold cosK at hcos
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcos
  rcases hcos with ((h | h) | h) | h
  · have : nrmP 45 6 3 64 TZ.G TZ.T
        (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.T i) cziP)) = true := by
      refine PK.allN_iff.2 fun k hk => ?_
      have ht : w * t0g k * w⁻¹ ∈ T0 := hnorm w hw _ (t0g_mem hk)
      obtain ⟨m, hm, e⟩ := hc0all _ ht
      exact exN_of hm (eq22_of_eq hX (prep_t0g k hk) (hc0 m hm).1 hX (by rw [e]; group))
    rw [this] at h
    exact absurd h (by decide)
  · obtain ⟨m, hm, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) h hX
    exact absurd (e ▸ (hc0 m hm).2) hw0
  · obtain ⟨m, hm, e⟩ := hc0all _ hww
    rw [inPts_of hm (e ▸ (hc0 m hm).1) (prep_pcomp hn45 hX hX)] at h
    exact absurd h (by decide)
  · obtain ⟨m, hm, hm'⟩ := exN_spec h
    obtain ⟨k, hk, e⟩ := exN_spec hm'
    have hlm := PK.allN_iff.1 hlu m hm
    rw [Bool.and_eq_true] at hlm
    have hum := (prep_wvA hlm.1).1
    have e' := eq22_sound e hX prep_pid (hc0 k hk).1 hum
    rw [mul_one] at e'
    have huw : wvA (uW.getD m []) = (c0 k)⁻¹ * w := by rw [e']; group
    refine ⟨m, hm, ?_, ?_⟩
    · rw [huw]
      exact T.mul_mem (T.inv_mem (hT0 (hc0 k hk).2)) hw
    · intro h0
      apply hw0
      rw [e']
      exact T0.mul_mem (hc0 k hk).2 h0

theorem b2_eq_bz
    {T B2 : Subgroup P45} {y2 : P45} (hT0 : T0 ≤ T) (hTA : T ≤ A) (hT2 : IsPGroup 2 T) {w : P45}
    (hw : w ∈ T) (hw0 : w ∉ T0) (hM : M107 T B2 y2) : ∃ j < 3, B2 = bzG j := by
  obtain ⟨j, hj, huT, huT0⟩ := exists_bz hT0 hTA hT2 hw hw0
  have hX : bzG j ≤ T ∧ (∀ a ∈ bzG j, ∀ b ∈ bzG j, a * b = b * a) ∧ (∀ a ∈ bzG j, a * a = 1) ∧
      Nat.card (bzG j) = 16 ∧ (∀ g ∈ T, ∀ b ∈ bzG j, g * b * g⁻¹ ∈ bzG j) ∧ ¬ bzG j ≤ T0 := by
    interval_cases j
    · exact bz_at hT0 hTA hT2 (by norm_num) huT huT0 BZ0.cl BZ0.tr ids3.2.2.1 BZ0.k
        binds3.2.2.2.2.2.2.2.1 tj0.1 tj0.2.1
    · exact bz_at hT0 hTA hT2 (by norm_num) huT huT0 BZ1.cl BZ1.tr ids3.2.2.2.1 BZ1.k
        binds3.2.2.2.2.2.2.2.2.1 tj1.1 tj1.2.1
    · exact bz_at hT0 hTA hT2 (by norm_num) huT huT0 BZ2.cl BZ2.tr ids3.2.2.2.2 BZ2.k
        binds3.2.2.2.2.2.2.2.2.2.1 tj2.1 tj2.2.1
  obtain ⟨hle, hcomm, hsq, hcard, hnorm, hout⟩ := hX
  exact ⟨j, hj, (hM.normal_elem _ hle hcomm hsq hcard hnorm hout).symm⟩

end CertificateChecks.KernelA45

end
