module

public import Certificates.Kernel.Sporadic.Co1Row26683.Checks
public import Certificates.Kernel.Sporadic.Co1Row26683.ChecksZ
public import Certificates.Kernel.Co1B.Prim2045
public import CFSG.Certificates.Kernel.Spor.Co1Row26683Sound
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Sporadic.Co1Block.TwoBComp

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits CFSG.KS.Raw.Orb
  CertificateChecks.KernelCo1B.Tri2045 CFSG.KS.Co1Row26683


theorem twoBQ_valid : ValidSchreier twoBQ :=
  (valid_ofArrays twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK).1

theorem twoBD_eq_of_base {g h : Equiv.Perm (Fin 1365)} (hg : g ∈ twoBD) (hh : h ∈ twoBD)
    (e0 : g 0 = h 0) (e1 : g 1 = h 1) (e2 : g 2 = h 2) : g = h := by
  have hm : h⁻¹ * g ∈ twoBQ.originalSubgroup := by
    rw [twoBQ_original]
    exact mul_mem (inv_mem hh) hg
  have h1 := twoBQ.eq_one_of_fixes_base twoBQ_valid hm fun i => by
    obtain ⟨i, hi⟩ := i
    have hi3 : i < 3 := hi
    interval_cases i
    · change (h⁻¹ * g) 0 = 0
      simp [Equiv.Perm.mul_apply, e0]
    · change (h⁻¹ * g) 1 = 1
      simp [Equiv.Perm.mul_apply, e1]
    · change (h⁻¹ * g) 2 = 2
      simp [Equiv.Perm.mul_apply, e2]
  exact (inv_mul_eq_one.1 h1).symm

theorem twoBD_orbit2 {T : Finset (Fin 1365)} (hT : T.card = 180)
    (hsub : ∀ p ∈ T, ∃ g ∈ twoBD, g 0 = 0 ∧ g 1 = 1 ∧ g 2 = p) {g : Equiv.Perm (Fin 1365)}
    (hg : g ∈ twoBD) (h0 : g 0 = 0) (h1 : g 1 = 1) : g 2 ∈ T := by
  have hsz := (valid_ofArrays (hn := (by norm_num : 1 ≤ 1365)) (hk := twoBStrong_two_le)
    (hb := twoB_nodup) (W := twoBW) twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK).2
  have hbc : twoBQ.baseCount = 3 := rfl
  let i2 : Fin twoBQ.baseCount := ⟨2, by rw [hbc]; norm_num⟩
  have hcard : Nat.card (twoBQ.orbitPoints i2) = 180 := by
    rw [← twoBQ.orbitSize_eq_card, hsz, twoB_baseArr]
    exact levelSize_of_orbitSizes orbits (by norm_num : 2 < 3)
  have hb2 : twoBQ.base.toList.take 2 = [0, 1] := rfl
  have hmem : ∀ k ∈ twoBD, k 0 = 0 → k 1 = 1 → k 2 ∈ twoBQ.orbitPoints i2 := by
    intro k hk k0 k1
    have hkl : k ∈ twoBQ.levelSubgroup 2 := by
      refine (twoBQ.mem_levelSubgroup_iff twoBQ_valid 2 (by rw [hbc]; norm_num) k).2 ⟨?_, ?_⟩
      · rw [twoBQ_original]
        exact hk
      · rw [hb2]
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact k0
        · rw [List.mem_singleton.1 hb]
          exact k1
    rw [twoBQ.orbitPoints_eq_orbit]
    exact ⟨⟨k, hkl⟩, rfl⟩
  have hsubset : (T : Set (Fin 1365)) ⊆ twoBQ.orbitPoints i2 := by
    intro p hp
    obtain ⟨k, hk, k0, k1, k2⟩ := hsub p hp
    rw [← k2]
    exact hmem k hk k0 k1
  have heq := Set.eq_of_subset_of_ncard_le hsubset
    (by rw [Set.ncard_coe_finset, hT, ← Nat.card_coe_set_eq, hcard]) (Set.toFinite _)
  have := hmem g hg h0 h1
  rw [← heq] at this
  exact this

theorem prep_one {P Q : Nat} {g : Equiv.Perm (Fin 1365)} (hP : PRep 1365 11 P g)
    (h : CFSG.KS.Prim.invEqK 1365 11 (CFSG.KS.mask 11) (1365 * 11) P Q = true) :
    PRep 1365 11 Q g⁻¹ :=
  prep_of_rep (rep_inv_of_isInvA (rep_unpack hP) (CFSG.KS.Prim.invEqK_sound h).2)

theorem prep_x : PRep 1365 11 (TB.P (nat_lit 10)) xBar := by
  apply prep_of_rep
  rw [← okX.2]
  exact rep_x

theorem prep_y : PRep 1365 11 (TB.P (nat_lit 11)) yBar := by
  apply prep_of_rep
  rw [← okY.2]
  exact rep_y

theorem prep_xi : PRep 1365 11 (TB.PI (nat_lit 10)) xBar⁻¹ :=
  prep_one prep_x (PP.all 10 (by norm_num))

theorem prep_yi : PRep 1365 11 (TB.PI (nat_lit 11)) yBar⁻¹ :=
  prep_one prep_y (PP.all 11 (by norm_num))

theorem bG5_mem : bG 5 ∈ GA ⊓ Subgroup.centralizer {A₁} := twoBE_le (bG_mem 5)

abbrev c5 : C₁ := liftC (bG 5) bG5_mem

theorem prep_b5 : PRep 1365 11 (TB.P (nat_lit 5)) (triHom c5) := by
  apply prep_of_rep
  rw [← (okB (j := 5) (by norm_num)).2]
  exact rep_triHom (c := c5) (bG_rep (by norm_num)) (okB (by norm_num)).1

theorem triHom_c5_not_mem : triHom c5 ∉ twoBD := by
  have hT : tree2K (TB.P (nat_lit 10)) (TB.P (nat_lit 11)) (TB.PI (nat_lit 10))
      (TB.PI (nat_lit 11)) (TB.P (nat_lit 5)) C26683.H2 C26683.T2R C26683.U0 C26683.U1
      C26683.A2 = true := by
    have h := ch26683T2
    simp only [withXY, CFSG.KC.Pack.strictB_eq] at h
    exact h
  obtain ⟨hfix, htr, hwit, hm0', hbit'⟩ := tree2K_sound hT
  obtain ⟨hpts, hinj⟩ := trMask_sound hm0'
  have hxD : xBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyD : yBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hwv := wv_eq prep_x prep_y prep_xi prep_yi
  have hfx := fixK_sound hfix
  have hle : Subgroup.closure {g | ∃ w ∈ C26683.H2, wP xBar yBar w = g} ≤
      twoBD ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) (0 : Fin 1365) ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 1365)) (1 : Fin 1365) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨wP_mem hxD hyD w, ?_⟩, ?_⟩
    · refine MulAction.mem_stabilizer_iff.2 ?_
      rw [Equiv.Perm.smul_def]
      exact Fin.ext ((hwv w 0).symm.trans (hfx w hw 0 (by simp)))
    · refine MulAction.mem_stabilizer_iff.2 ?_
      rw [Equiv.Perm.smul_def]
      exact Fin.ext ((hwv w 1).symm.trans (hfx w hw 1 (by simp)))
  have htree := trOK_sound prep_x prep_y prep_xi prep_yi (root := 2) htr
  let pt : Fin 180 → Fin 1365 := fun k => ⟨tpt C26683.T2R k, (hpts k k.2).1⟩
  have hptinj : Function.Injective pt := fun a b e =>
    Fin.ext (hinj a a.2 b b.2 (congrArg Fin.val e))
  have hTc : (Finset.univ.image pt).card = 180 := by
    rw [Finset.card_image_of_injective _ hptinj, Finset.card_univ, Fintype.card_fin]
  have hsub : ∀ p ∈ Finset.univ.image pt, ∃ g ∈ twoBD, g 0 = 0 ∧ g 1 = 1 ∧ g 2 = p := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨g, hg, e⟩ := htree k k.2
    obtain ⟨⟨hgD, hg0⟩, hg1⟩ := hle hg
    have hg0' : g • (0 : Fin 1365) = 0 := MulAction.mem_stabilizer_iff.1 hg0
    have hg1' : g • (1 : Fin 1365) = 1 := MulAction.mem_stabilizer_iff.1 hg1
    rw [Equiv.Perm.smul_def] at hg0' hg1'
    exact ⟨g, hgD, hg0', hg1', Fin.ext e⟩
  obtain ⟨w1, w2, w3, hA2, w5⟩ := witK_sound hwit
  intro hmem
  set u0 := wP xBar yBar C26683.U0
  set u1 := wP xBar yBar C26683.U1
  set F := triHom c5
  let a2 : Fin 1365 := ⟨C26683.A2, hA2⟩
  have e1 : u0 0 = F 0 :=
    Fin.ext ((hwv C26683.U0 0).symm.trans (w1.trans (ap_prep prep_b5 0)))
  have e2 : u1 0 = 0 := Fin.ext ((hwv C26683.U1 0).symm.trans w2)
  have e3 : u0 (u1 1) = F 1 := by
    have i2 := hwv C26683.U0 (u1 1)
    rw [← hwv C26683.U1 1] at i2
    exact Fin.ext (i2.symm.trans (w3.trans (ap_prep prep_b5 1)))
  have e5 : u0 (u1 a2) = F 2 := by
    have i2 := hwv C26683.U0 (u1 a2)
    rw [← hwv C26683.U1 a2] at i2
    exact Fin.ext (i2.symm.trans (w5.trans (ap_prep prep_b5 2)))
  have hd : u1⁻¹ * u0⁻¹ * F ∈ twoBD :=
    mul_mem (mul_mem (inv_mem (wP_mem hxD hyD _)) (inv_mem (wP_mem hxD hyD _))) hmem
  have hd0 : (u1⁻¹ * u0⁻¹ * F) 0 = 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e1]
    have e0 : u0⁻¹ (u0 0) = 0 := by simp
    rw [e0, Equiv.Perm.inv_eq_iff_eq]
    exact e2.symm
  have hd1 : (u1⁻¹ * u0⁻¹ * F) 1 = 1 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e3]
    simp
  have hd2 : (u1⁻¹ * u0⁻¹ * F) 2 = a2 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e5]
    simp
  have ha := twoBD_orbit2 hTc hsub hd hd0 hd1
  rw [hd2] at ha
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 ha
  have hk' : tpt C26683.T2R k = C26683.A2 := congrArg Fin.val hk
  have := (hpts k k.2).2
  rw [hk', hbit'] at this
  exact absurd this (by decide)

theorem co1_exists_not_mem_K : ∃ c : C₁, triHom c ∉ twoBD := ⟨c5, triHom_c5_not_mem⟩

theorem co1_moved_K (j : Fin 3) : ∃ h ∈ twoBH, h (twoBXs j) ≠ twoBXs j := by
  have hr : twoBSubReps[(j : ℕ)]! ∈ twoBSubReps := by fin_cases j <;> simp [twoBSubReps]
  obtain ⟨i, hi2, hi6, hne⟩ :=
    CFSG.KS.Co1Row26683Z.movedK_sound (CFSG.KS.Co1Row26683Z.primK_sound ch26683P _ hr)
  have hst := CertificateChecks.KernelCo1B.Prim2045.hst
  have hjs : i - 2 < twoBHSteps.size := by rw [hst.1]; omega
  refine ⟨permOfArr 1365 twoBHSteps[i - 2]!, Subgroup.subset_closure ?_, fun heq => hne ?_⟩
  · refine List.mem_map.2 ⟨twoBHSteps[i - 2], Array.mem_toList_iff.2 (Array.getElem_mem hjs), ?_⟩
    rw [getElem!_pos twoBHSteps (i - 2) hjs]
  · have hv : ((twoBXs j : Fin 1365) : ℕ) = twoBSubReps[(j : ℕ)]! := by fin_cases j <;> rfl
    have h1 := twoBHSteps_rep hjs (twoBXs j)
    rw [heq, hst.2 (i - 2) (by omega) _ (twoBXs j).2] at h1
    unfold CertificateChecks.KernelCo1B.Prim2045.stp at h1
    have e : Nat.add (i - 2) 2 = i := by
      change i - 2 + 2 = i
      omega
    rw [e, hv] at h1
    exact h1

theorem co1_centralizer_trivial_K {y : Equiv.Perm (Fin 1365)}
    (hy : ∀ d ∈ twoBD, y * d = d * y) : y = 1 := by
  have hfix : ∀ h ∈ twoBH, h (y 0) = y 0 := by
    intro h hh
    have h1 := congrArg (fun f : Equiv.Perm (Fin 1365) => f 0) (hy h (twoBH_le hh))
    simp only [Equiv.Perm.mul_apply] at h1
    rw [twoBH_fix h hh] at h1
    exact h1.symm
  have hy0 : y 0 = 0 := by
    by_contra hne
    obtain ⟨j, h, hh, hhj⟩ := twoB_cover (y 0) hne
    obtain ⟨h', hh', hne'⟩ := co1_moved_K j
    apply hne'
    have h2 : h⁻¹ (y 0) = y 0 := hfix h⁻¹ (Subgroup.inv_mem _ hh)
    have h3 : twoBXs j = y 0 := by
      calc twoBXs j = h⁻¹ (h (twoBXs j)) := by simp
        _ = h⁻¹ (y 0) := by rw [hhj]
        _ = y 0 := h2
    rw [h3]
    exact hfix h' hh'
  refine Equiv.ext fun z => ?_
  obtain ⟨g, hg, hgz⟩ := twoBD_exists_apply z
  have h1 := congrArg (fun f : Equiv.Perm (Fin 1365) => f 0) (hy g hg)
  simp only [Equiv.Perm.mul_apply, hy0, hgz] at h1
  rw [Equiv.Perm.one_apply]
  exact h1

end CertificateChecks.KernelSpor.Co1Row26683

end
