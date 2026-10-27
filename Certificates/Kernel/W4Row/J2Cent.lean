module

public import Certificates.Kernel.W4Row.J2CentK
public import Certificates.Kernel.LocalQT.SV.C4127
public import CFSG.Certificates.Kernel.W4Row.CentPairKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Perm
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.KD.W4C.J2Cent

open CFSG.KC.LQT.TC CFSG.KC.LQT.JX CFSG.KC.LQT.SV CFSG.KC.W4C CFSG.KC.W4E CFSG.KC.IntLines
  CFSG.KC.LQT.Cov CFSG.KD.LQT.C4127 CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor

theorem tabs : (∀ i < 256, ∀ j < 256, j2Mul i j = mtJ 8 IX.MR i j ∧ mtJ 8 IX.MR i j < 256) ∧
    (∀ s < 256, j2Inv s = IX.IT s ∧ IX.IT s < 256) ∧
    (∀ k < 256, isInvJ 8 IX.MR k = true ↔ k ≠ 0 ∧ mtJ 8 IX.MR k k = 0) :=
  idxJX_tab (b := 8) (gb := 12) (K := 8) (L := 32) (tab := j2Tab) (par := j2Par)
    (lab := j2Lab) (reps := j2Reps) (fun i hi => by rw [eP]; exact bindSV_spec bP i hi)
    (fun i hi => by rw [eL]; exact bindSV_spec bL i hi)
    (fun i hi => by rw [eT]; exact bindSV_spec bT i hi) (by norm_num) R.all

theorem parse {s : String} (hs : s.toList ∈ strsC) :
    CFSG.Quasithin.B45Exc.Tab.parseInts s = lineInts s.toList :=
  parseInts_str (List.all_eq_true.1 strs _ hs)

theorem pair_of {r : ℕ} (hr : r < 256) {sz sx : String} {prog : List (ℤ × ℤ)}
    (hsz : sz.toList ∈ strsC) (hsx : sx.toList ∈ strsC)
    (h : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E r)
      (lineInts sz.toList) (lineInts sx.toList) prog [J2P.S 0, J2P.S 1] = true) :
    centPairCheck 315 [j2A0P, j2A1P] j2Al[17]! j2Al[r]! (CFSG.Quasithin.B45Exc.Tab.parseInts sz)
      (CFSG.Quasithin.B45Exc.Tab.parseInts sx) prog [j2A0A, j2A1A] = true := by
  rw [parse hsz, parse hsx, sylAll.2 17 (by norm_num), sylAll.2 r hr, gens_eq, targ_eq]
  exact cpK_of h

theorem isInv_iff {k : ℕ} (hk : k < 256) : isInvF j2Mul k = true ↔ isInvJ 8 IX.MR k = true := by
  rw [isInvF_iff, tabs.2.2 k hk, (tabs.1 k hk k hk).1]

theorem zfacts : isInvF j2Mul 17 = true ∧ ∀ k < 256, j2Mul 17 k = j2Mul k 17 := by
  obtain ⟨hz, hzc⟩ := zcK_spec zc
  refine ⟨(isInv_iff (by norm_num)).2 hz, fun k hk => ?_⟩
  rw [(tabs.1 17 (by norm_num) k hk).1, (tabs.1 k hk 17 (by norm_num)).1]
  exact hzc k hk

theorem reps_eq : j2CentReps = [1, 2, 7, 54, 58, 165] := by
  simp only [j2CentReps, j2CentData, List.map_cons, List.map_nil]

theorem cov_spec : ∀ k < 256, isInvJ 8 IX.MR k = true → k ≠ 17 →
    ∃ s < 256, conjJ 8 IX.MR IX.IT s k ∈ [1, 2, 7, 54, 58, 165] :=
  covK_spec cov

theorem conj_eq {s k : ℕ} (hs : s < 256) (hk : k < 256) :
    conjF j2Mul j2Inv s k = conjJ 8 IX.MR IX.IT s k := by
  rw [conjF.eq_1, conjJ.eq_1, (tabs.1 s hs k hk).1, (tabs.2.1 s hs).1,
    (tabs.1 _ (tabs.1 s hs k hk).2 _ (tabs.2.1 s hs).2).1]

theorem cover : ∀ k < 256, isInvF j2Mul k = true → k ≠ 17 →
    ∃ s < 256, conjF j2Mul j2Inv s k ∈ j2CentReps := by
  intro k hk hk' hk17
  obtain ⟨s, hs, hmem⟩ := cov_spec k hk ((isInv_iff hk).1 hk') hk17
  refine ⟨s, hs, ?_⟩
  rw [reps_eq, conj_eq hs hk]
  exact hmem

theorem pairs : ∀ d ∈ j2CentData, centPairCheck 315 [j2A0P, j2A1P] j2Al[17]! j2Al[d.1]!
    d.2.1 d.2.2.1 d.2.2.2 [j2A0A, j2A1A] = true := by
  · intro d hd
    simp only [j2CentData, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pair_of (by norm_num) (by simp [strsC]) (by simp [strsC]) cp1
    · exact pair_of (by norm_num) (by simp [strsC]) (by simp [strsC]) cp2
    · exact pair_of (by norm_num) (by simp [strsC]) (by simp [strsC]) cp7
    · exact pair_of (by norm_num) (by simp [strsC]) (by simp [strsC]) cp54
    · exact pair_of (by norm_num) (by simp [strsC]) (by simp [strsC]) cp58
    · exact pair_of (by norm_num) (by simp [strsC]) (by simp [strsC]) cp165

theorem facts : isInvF j2Mul 17 = true ∧ (∀ k < 256, j2Mul 17 k = j2Mul k 17) ∧
    (∀ k < 256, isInvF j2Mul k = true → k ≠ 17 →
      ∃ s < 256, conjF j2Mul j2Inv s k ∈ j2CentReps) ∧
    (∀ d ∈ j2CentData, centPairCheck 315 [j2A0P, j2A1P] j2Al[17]! j2Al[d.1]!
      d.2.1 d.2.2.1 d.2.2.2 [j2A0A, j2A1A] = true) :=
  ⟨zfacts.1, zfacts.2, cover, pairs⟩

theorem j2z_facts {E gp : ℕ → Equiv.Perm (Fin 315)} {Sy : Subgroup (Equiv.Perm (Fin 315))}
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy) :
    E 17 * E 17 = 1 ∧ E 17 ≠ 1 ∧ ∀ y ∈ Sy, E 17 * y = y * E 17 := by
  have hf := facts
  refine ⟨j2_sq_of_isInv hM (by norm_num) hf.1, ?_, ?_⟩
  · intro h
    have := hM.inj 17 (by norm_num) 0 (by norm_num) (by rw [h, hM.one])
    norm_num at this
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := (hM.mem_Sy y).1 hy
    rw [← (j2_mul_spec' hM 17 (by norm_num) k hk).2,
      ← (j2_mul_spec' hM k hk 17 (by norm_num)).2, hf.2.1 k hk]

theorem mem_of_elemAbelian_card_sixteen
    {B' : Subgroup (Equiv.Perm (Fin 315))} {z : Equiv.Perm (Fin 315)}
    (hB'R : B' ≤ j2R) (hzR : z ∈ j2R) (hB'comm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x)
    (hB'sq : ∀ x ∈ B', x * x = 1) (hcard : Nat.card B' = 16)
    (hzc : ∀ x ∈ B', x * z = z * x) (hz2 : z * z = 1) (hz1 : z ≠ 1) : z ∈ B' := by
  by_contra hzB
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzpow : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  have hcardinf : Nat.card ↥(B' ⊓ Subgroup.zpowers z) = 1 := by
    have hdvd : Nat.card ↥(B' ⊓ Subgroup.zpowers z) ∣ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : B' ⊓ Subgroup.zpowers z ≤ Subgroup.zpowers z)
      rwa [hzpow] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exfalso
      apply hzB
      have heq : B' ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hzpow, h])
      have hzmem : z ∈ B' ⊓ Subgroup.zpowers z := by
        rw [heq]; exact Subgroup.mem_zpowers z
      exact hzmem.1
  have hdisj : B' ⊓ Subgroup.zpowers z = ⊥ := Subgroup.eq_bot_of_card_eq _ hcardinf
  have hzc' : ∀ x ∈ B', ∀ y ∈ Subgroup.zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (show Commute x z from hzc x hx).zpow_right n |>.eq
  have hsupcard : Nat.card ↥(B' ⊔ Subgroup.zpowers z) = 32 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B' (Subgroup.zpowers z) hzc').1
    rw [hdisj, Subgroup.card_bot, hcard, hzpow] at h
    omega
  have hsup : CFSG.Open.IsElemAbelian 2 (B' ⊔ Subgroup.zpowers z) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      ⟨⟨⟨fun a b => Subtype.ext (hB'comm a a.2 b b.2)⟩⟩,
        fun x hx => by rw [pow_two]; exact hB'sq x hx⟩
      (CFSG.Open.isElemAbelian_zpowers hz2) hzc'
  have hleR : B' ⊔ Subgroup.zpowers z ≤ j2R :=
    sup_le hB'R (Subgroup.zpowers_le.2 hzR)
  have hrank := j2_rank_R ((B' ⊔ Subgroup.zpowers z).subgroupOf j2R)
    (fun x hx y hy => by
      have hx' : (x : Equiv.Perm (Fin 315)) ∈ B' ⊔ Subgroup.zpowers z :=
        Subgroup.mem_subgroupOf.1 hx
      have hy' : (y : Equiv.Perm (Fin 315)) ∈ B' ⊔ Subgroup.zpowers z :=
        Subgroup.mem_subgroupOf.1 hy
      exact Subtype.ext (hsup.comm hx' hy'))
    (fun x hx => by
      have hx' : (x : Equiv.Perm (Fin 315)) ∈ B' ⊔ Subgroup.zpowers z :=
        Subgroup.mem_subgroupOf.1 hx
      have h := hsup.2 (x : Equiv.Perm (Fin 315)) hx'
      exact Subtype.ext (by simpa [pow_two] using h))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleR).toEquiv, hsupcard] at hrank
  omega

theorem centPairCheck_sound {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))} {gens : List PArr}
    {zA xA : Array ℕ} {gz gx : Equiv.Perm (Fin n)}
    (hK : RegIn n K gens) (hz : Rep n zA gz) (hx : Rep n xA gx)
    {wz wx : List ℤ} {prog : List (ℤ × ℤ)} {targets : List (Array ℕ)}
    (hc : centPairCheck n gens zA xA wz wx prog targets = true) :
    ∃ u ∈ K ⊓ Subgroup.centralizer ({gz} : Set (Equiv.Perm (Fin n))),
      ∃ v ∈ K ⊓ Subgroup.centralizer ({gx} : Set (Equiv.Perm (Fin n))),
      ∀ A ∈ targets, ∀ a : Equiv.Perm (Fin n), Rep n A a →
        a ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin n))) := by
  obtain ⟨u, huK, hurep⟩ := hK.word wz
  obtain ⟨v, hvK, hvrep⟩ := hK.word wx
  simp only [centPairCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hc
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
  have hzu : u * gz = gz * u :=
    (eqA_iff (rep_compA hurep.1 hz) (rep_compA hz hurep.1)).1 hc1
  have hxv : v * gx = gx * v :=
    (eqA_iff (rep_compA hvrep.1 hx) (rep_compA hx hvrep.1)).1 hc2
  refine ⟨u, Subgroup.mem_inf.2 ⟨huK, ?_⟩, v, Subgroup.mem_inf.2 ⟨hvK, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]; exact hzu
  · rw [Subgroup.mem_centralizer_singleton_iff]; exact hxv
  · intro A hA a hAa
    set K' : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin n)))
    have hreg : RegIn n K' [pWord n gens wz, pWord n gens wx] := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨u, Subgroup.subset_closure (by simp), hurep⟩
      · exact ⟨v, Subgroup.subset_closure (by simp), hvrep⟩
    have hrun := hreg.run prog
    obtain ⟨r, hrmem, hrA⟩ := hc3 A hA
    obtain ⟨g', hg', hrep⟩ := hrun r hrmem
    have : g' = a := (eqA_iff hrep.1 hAa).1 hrA
    rw [← this]
    exact hg'

theorem j2_conj_B_sylow
    {E gp : ℕ → Equiv.Perm (Fin 315)} {Sy : Subgroup (Equiv.Perm (Fin 315))}
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy)
    {B : Subgroup (Equiv.Perm (Fin 315))} (hBR : B ≤ j2R)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 16) :
    ∃ (g : Equiv.Perm (Fin 315)) (B' : Subgroup (Equiv.Perm (Fin 315))),
      g ∈ j2R ∧ B' = B.map (MulAut.conj g).toMonoidHom ∧ B' ≤ Sy ∧
      (∀ x ∈ B', x * x = 1) ∧ (∀ x ∈ B', ∀ y ∈ B', x * y = y * x) ∧
      Nat.card B' = 16 := by
  obtain ⟨g, hgR, hgsy⟩ := exists_conj_mem_Sy (a := 8) (m := 4725) hM.Sy_le
    (by rw [hM.card_Sy]; norm_num) (by rw [card_j2R]; norm_num) (by decide) hBR hsq
  refine ⟨g, B.map (MulAut.conj g).toMonoidHom, hgR, rfl, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hgsy b hb
  · rintro _ ⟨a, ha, rfl⟩
    show g * a * g⁻¹ * (g * a * g⁻¹) = 1
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
      _ = _ := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem j2_e16_exists_e'
    {E gp : ℕ → Equiv.Perm (Fin 315)} {Sy : Subgroup (Equiv.Perm (Fin 315))}
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy)
    {B' : Subgroup (Equiv.Perm (Fin 315))} (hB'Sy : ∀ x ∈ B', x ∈ Sy)
    (hB'sq : ∀ x ∈ B', x * x = 1) (h16 : Nat.card B' = 16)
    (hz2 : E 17 * E 17 = 1) (hz1 : E 17 ≠ 1) :
    ∃ (e' : Equiv.Perm (Fin 315)) (k : ℕ), e' ∈ B' ∧ e' = E k ∧ e' ≠ 1 ∧ k < 256 ∧
      isInvF j2Mul k = true ∧ k ≠ 17 := by
  classical
  have hne : B' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h16
    norm_num at h16
  obtain ⟨⟨a, haB⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have a1 : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hex : ∃ e' ∈ B', e' ≠ 1 ∧ e' ≠ E 17 := by
    by_cases haz : a = E 17
    · have hzle : Subgroup.zpowers (E 17) ≤ B' := by
        rw [← haz]
        exact Subgroup.zpowers_le.2 haB
      have hzcard : Nat.card ↥(Subgroup.zpowers (E 17)) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1]
      have hnot : ¬ B' ≤ Subgroup.zpowers (E 17) := by
        intro hle
        have hle' := Subgroup.card_le_of_le hle
        rw [h16, hzcard] at hle'
        omega
      obtain ⟨b, hbB, hbz⟩ : ∃ b, b ∈ B' ∧ b ∉ Subgroup.zpowers (E 17) := by
        by_contra h
        push Not at h
        exact hnot (fun x hx => h x hx)
      refine ⟨b, hbB, ?_, ?_⟩
      · intro hb1; exact hbz (by rw [hb1]; exact Subgroup.one_mem _)
      · intro hbz'; exact hbz (by rw [hbz']; exact Subgroup.mem_zpowers _)
    · exact ⟨a, haB, a1, haz⟩
  obtain ⟨e', he'B, he'1, he'z⟩ := hex
  have he'Sy : e' ∈ Sy := hB'Sy e' he'B
  obtain ⟨k, hk, hkEq⟩ := (hM.mem_Sy e').1 he'Sy
  have hksq : E k * E k = 1 := by rw [← hkEq]; exact hB'sq e' he'B
  have hk1 : E k ≠ 1 := by rw [← hkEq]; exact he'1
  have hkz : E k ≠ E 17 := by rw [← hkEq]; exact he'z
  have hkinv : isInvF j2Mul k = true := by
    rw [isInvF_iff]
    refine ⟨fun h0 => hk1 (by rw [h0, hM.one]), ?_⟩
    apply hM.inj _ (j2_mul_spec' hM k hk k hk).1 0 (by norm_num)
    rw [(j2_mul_spec' hM k hk k hk).2, hksq, hM.one]
  exact ⟨E k, k, by rw [← hkEq]; exact he'B, rfl, hk1, hk, hkinv,
    fun h17 => hkz (by rw [h17])⟩

theorem j2_e16_pair_data
    {E gp : ℕ → Equiv.Perm (Fin 315)} {Sy : Subgroup (Equiv.Perm (Fin 315))}
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy)
    {k : ℕ} (hk : k < 256) (hinv : isInvF j2Mul k = true) (hk17 : k ≠ 17) :
    ∃ (s r : ℕ) (d : ℕ × List ℤ × List ℤ × List (ℤ × ℤ)) (u v : Equiv.Perm (Fin 315)),
      s < 256 ∧ r = conjF j2Mul j2Inv s k ∧ d ∈ j2CentData ∧ d.1 = r ∧
      E r = E s * E k * (E s)⁻¹ ∧
      u ∈ j2P ⊓ Subgroup.centralizer ({E 17} : Set (Equiv.Perm (Fin 315))) ∧
      v ∈ j2P ⊓ Subgroup.centralizer ({E r} : Set (Equiv.Perm (Fin 315))) ∧
      j2P ≤ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 315))) := by
  obtain ⟨s, hs, hcont⟩ := facts.2.2.1 k hk hinv hk17
  have hcont' : conjF j2Mul j2Inv s k ∈ j2CentData.map Prod.fst := by
    simpa only [j2CentReps] using hcont
  obtain ⟨d, hd, hdr⟩ := List.mem_map.1 hcont'
  obtain ⟨hlt, heq⟩ := conjF_spec (j2_mul_spec' hM) (j2_inv_spec hM) hs hk
  have hpd := facts.2.2.2 d hd
  have hrep : Rep 315 j2Al[d.1]! (E (conjF j2Mul j2Inv s k)) := by
    rw [hdr]
    exact hM.rep _ hlt
  obtain ⟨u, hu, v, hv, hgen⟩ :=
    centPairCheck_sound regIn_j2P (hM.rep 17 (by norm_num)) hrep hpd
  refine ⟨s, conjF j2Mul j2Inv s k, d, u, v, hs, rfl, hd, hdr, heq, hu, hv, ?_⟩
  rw [j2P]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (rfl | rfl)
  · exact hgen j2A0A (by simp) _ rep_j2A0
  · exact hgen j2A1A (by simp) _ rep_j2A1

theorem j2_e16_conj_back
    {B : Subgroup (Equiv.Perm (Fin 315))} {g z es er e' u v : Equiv.Perm (Fin 315)}
    (hgR : g ∈ j2R) (hesR : es ∈ j2R)
    (hzB : ∃ b ∈ B, g * b * g⁻¹ = z) (heB : ∃ b ∈ B, g * b * g⁻¹ = e')
    (hz1 : z ≠ 1) (he1 : e' ≠ 1) (hzc : z * es = es * z) (her : er = es * e' * es⁻¹)
    (huP : u ∈ j2P) (huz : u * z = z * u)
    (hvP : v ∈ j2P) (hve : v * er = er * v)
    (hgen : j2P ≤ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 315)))) :
    ∃ d ∈ B, ∃ e ∈ B, d ≠ 1 ∧ e ≠ 1 ∧ j2P ≤ Subgroup.closure
      (((j2P ⊓ Subgroup.centralizer {d} : Subgroup (Equiv.Perm (Fin 315))) :
        Set (Equiv.Perm (Fin 315))) ∪ (j2P ⊓ Subgroup.centralizer {e} :
          Subgroup (Equiv.Perm (Fin 315)))) := by
  obtain ⟨b, hbB, hbz⟩ := hzB; obtain ⟨b', hb'B, hbe⟩ := heB
  set w : Equiv.Perm (Fin 315) := es * g with hw
  have hwR : w ∈ j2R := j2R.mul_mem hesR hgR
  have hEs : es⁻¹ * z * es = z := by
    rw [mul_assoc, hzc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hd_eq : w⁻¹ * z * w = b := by
    calc w⁻¹ * z * w = (g⁻¹ * es⁻¹) * z * (es * g) := by rw [hw, mul_inv_rev]
      _ = g⁻¹ * (es⁻¹ * z * es) * g := by group
      _ = g⁻¹ * z * g := by rw [hEs]
      _ = b := by rw [← hbz]; group
  have he_eq : w⁻¹ * er * w = b' := by
    calc w⁻¹ * er * w = (g⁻¹ * es⁻¹) * er * (es * g) := by rw [hw, mul_inv_rev]
      _ = (g⁻¹ * es⁻¹) * (es * e' * es⁻¹) * (es * g) := by rw [her]
      _ = g⁻¹ * e' * g := by group
      _ = b' := by rw [← hbe]; group
  have hxu : w⁻¹ * u * w ∈ j2P ⊓ Subgroup.centralizer ({w⁻¹ * z * w} : Set _) := by
    refine Subgroup.mem_inf.2 ⟨j2_normal' w hwR u huP, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (w⁻¹ * u * w) * (w⁻¹ * z * w) = w⁻¹ * (u * z) * w := by group
      _ = (w⁻¹ * z * w) * (w⁻¹ * u * w) := by rw [huz]; group
  have hxv : w⁻¹ * v * w ∈ j2P ⊓ Subgroup.centralizer ({w⁻¹ * er * w} : Set _) := by
    refine Subgroup.mem_inf.2 ⟨j2_normal' w hwR v hvP, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (w⁻¹ * v * w) * (w⁻¹ * er * w) = w⁻¹ * (v * er) * w := by group
      _ = (w⁻¹ * er * w) * (w⁻¹ * v * w) := by rw [hve]; group
  have hxgen : j2P ≤ Subgroup.closure ({w⁻¹ * u * w, w⁻¹ * v * w} : Set _) := by
    intro p hp
    have hpR : w * p * w⁻¹ ∈ j2P := j2_normal w hwR p hp
    have hpM : w * p * w⁻¹ ∈ Subgroup.closure ({u, v} : Set _) := hgen hpR
    have hconj := conj_mem_closure_pair (s := w) (x := w⁻¹ * u * w) (y := w⁻¹ * v * w)
      hpM (by group) (by group)
    have hp' : w⁻¹ * (w * p * w⁻¹) * w = p := by group
    rwa [hp'] at hconj
  refine ⟨w⁻¹ * z * w, ?_, w⁻¹ * er * w, ?_, ?_, ?_, ?_⟩
  · rw [hd_eq]; exact hbB
  · rw [he_eq]; exact hb'B
  · rw [hd_eq]; intro hb1; exact hz1 (by rw [← hbz, hb1]; group)
  · rw [he_eq]; intro hb'1
    exact he1 (by rw [← hbe, hb'1]; group)
  · refine hxgen.trans (Subgroup.closure_mono ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hxu
    · exact Or.inr hxv

theorem holds : ∀ B : Subgroup (Equiv.Perm (Fin 315)), B ≤ j2R →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B = 16 →
    ∃ d ∈ B, ∃ e ∈ B, d ≠ 1 ∧ e ≠ 1 ∧ j2P ≤ Subgroup.closure
      (((j2P ⊓ Subgroup.centralizer {d} : Subgroup (Equiv.Perm (Fin 315))) :
        Set (Equiv.Perm (Fin 315))) ∪ (j2P ⊓ Subgroup.centralizer {e} :
          Subgroup (Equiv.Perm (Fin 315)))) := by
  intro B hBR hcomm hsq hcard
  obtain ⟨E, gp, Sy, hM⟩ := sylModel regIn_j2SylGens j2_syl_check
  obtain ⟨hz2, hz1, hzcent⟩ := j2z_facts hM
  obtain ⟨g, B', hgR, hB'eq, hB'Sy, hB'sq, hB'comm, h16⟩ :=
    j2_conj_B_sylow hM hBR hcomm hsq hcard
  have hB'Sy' : ∀ x ∈ B', x ∈ Sy := fun x hx => hB'Sy hx
  have hzR : E 17 ∈ j2R := hM.Sy_le ((hM.mem_Sy _).2 ⟨17, by norm_num, rfl⟩)
  have hzB' : E 17 ∈ B' :=
    mem_of_elemAbelian_card_sixteen (z := E 17) (fun x hx => hM.Sy_le (hB'Sy' x hx)) hzR
      hB'comm hB'sq h16 (fun x hx => (hzcent x (hB'Sy' x hx)).symm) hz2 hz1
  obtain ⟨e', k, he'B', he'k, he'1, hk, hkinv, hk17⟩ :=
    j2_e16_exists_e' hM hB'Sy' hB'sq h16 hz2 hz1
  obtain ⟨s, r, d, u, v, hs, hr, hd, hdr, hEr, hu, hv, hgen⟩ :=
    j2_e16_pair_data hM hk hkinv hk17
  have hesR : E s ∈ j2R := hM.Sy_le ((hM.mem_Sy (E s)).2 ⟨s, hs, rfl⟩)
  have hEsZ : E 17 * E s = E s * E 17 := hzcent (E s) ((hM.mem_Sy _).2 ⟨s, hs, rfl⟩)
  have hEr' : E r = E s * e' * (E s)⁻¹ := by rw [he'k]; exact hEr
  have hzB : ∃ b ∈ B, g * b * g⁻¹ = E 17 := by
    have h := hzB'
    rw [hB'eq] at h
    exact Subgroup.mem_map.1 h
  have heB : ∃ b ∈ B, g * b * g⁻¹ = e' := by
    have h := he'B'
    rw [hB'eq] at h
    exact Subgroup.mem_map.1 h
  have huz : u * E 17 = E 17 * u :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).2
  have hve : v * E r = E r * v :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hv).2
  exact j2_e16_conj_back hgR hesR hzB heB hz1 he'1 hEsZ hEr'
    (Subgroup.mem_inf.1 hu).1 huz (Subgroup.mem_inf.1 hv).1 hve hgen

end CFSG.KD.W4C.J2Cent

end
