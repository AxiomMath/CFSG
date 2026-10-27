module

public import Certificates.Kernel.Sp6Insp443.CentGlue
public import Certificates.Kernel.Sp6Insp443.Six
public import CFSG.Certificates.Kernel.Sp6Insp443.SixPack
public import CFSG.Certificates.Kernel.A45Cls.DefsSound
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KC.A45Cls CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim
  CFSG.KS.Sp6I CFSG.KS.SporSch.MOC CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.EvenSmallLie.Sp6
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CertificateChecks.KernelLC.Sp6J

theorem shr36 (p q : Nat) : pcomp 36 6 (mask 6) p q >>> (36 * 6) = 0 :=
  PackFld.pcomp_shr (by norm_num) (by norm_num)

theorem map_conj_closure_le {G : Type*} [Group G] {k : Nat} {w : Fin k → G} {g : G}
    (h : ∀ i, ∃ c, g * w i * g⁻¹ = eElt w c) :
    (Subgroup.closure (Set.range w)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (Set.range w) := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  obtain ⟨c, hc⟩ := h i
  change g * w i * g⁻¹ ∈ _
  rw [hc]
  exact eElt_mem_closure w c

theorem sixTest_of
    {t : Nat} (ht : t < 3) (hs : ch725106s t = true)
    {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36) {T : Table} (hT : Rep 36 T g) :
    sixTestS 36 (cands5.getD (sixW t) []) (spanTabs 36 (cands5.getD (sixW t) [])) (sixDs t)
      ((sixDs t).map (spanTabs 36)) T = false := by
  unfold ch725106s at hs
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hs
  rw [← sp6Q_originalSubgroup] at hg
  have h32 : (2 : Nat) ^ 5 = 32 := by norm_num
  obtain ⟨c, hcH, hc⟩ := wordNK_prep (by norm_num) prepOne prepGen prepGenInv genMem _ h1
  rw [Nat.eq_of_beq_eq_true h2] at hc
  have hci := prep_inv_of_permOK h3 hc
  obtain ⟨x, hx⟩ := exists_lanes_inv h6
  have hlW : (cands5.getD (sixW t) []).length = 5 := by
    rw [← lenT_eq]
    exact Nat.eq_of_beq_eq_true h5
  have hxp : ∀ j < 5, PRep 36 6 (laneK (36 * 6) (D.wT.getD (sixW t) 0) j) (x j) :=
    fun j hj => (hx j hj).1
  have hxsq : ∀ j < 5, x j * x j = 1 := fun j hj => (hx j hj).2
  have hxc := commute_of_commPK (by norm_num) (by norm_num) hxp h7
  have hws := forall₂_of_tabsPK h4 hlW hxp
  have hspW := spanPK_prep (by norm_num) prepOne h8 hxp
  have hsd : ∀ r < 6, tabsPK 36 6 (mask 6) (36 * 6) (E.dT.getD (6 * t + r) 0)
      ((sixDs t).getD r []) 0 = true ∧ Nat.beq (lenT ((sixDs t).getD r [])) 4 = true ∧
      allN 4 (fun i => permOK 36 6 (mask 6) (36 * 6) (laneK (36 * 6) (E.dT.getD (6 * t + r) 0) i)
        (laneK (36 * 6) (E.dT.getD (6 * t + r) 0) i)) = true ∧
      allN 4 (fun i => commPK 36 6 (mask 6) (36 * 6) (E.dT.getD (6 * t + r) 0) 4
        (laneK (36 * 6) (E.dT.getD (6 * t + r) 0) i)) = true ∧
      spanPK 36 6 (mask 6) (36 * 6) One36 (E.dT.getD (6 * t + r) 0) (E.dS.getD (6 * t + r) 0) 4 =
        true := by
    intro r hr
    have := Orb.allN_iff.1 h9 r hr
    unfold sixD at this
    simpa only [Orb.bAnd_eq, Bool.and_eq_true] using this
  have hD0 : ∀ r, ∃ y : Nat → Equiv.Perm (Fin 36), r < 6 → ∀ j < 4,
      PRep 36 6 (laneK (36 * 6) (E.dT.getD (6 * t + r) 0) j) (y j) ∧ y j * y j = 1 := by
    intro r
    by_cases hr : r < 6
    · obtain ⟨y, hy⟩ := exists_lanes_inv (hsd r hr).2.2.1
      exact ⟨y, fun _ => hy⟩
    · exact ⟨fun _ => 1, fun h => absurd h hr⟩
  choose y hy using hD0
  have hyp : ∀ r < 6, ∀ j < 4, PRep 36 6 (laneK (36 * 6) (E.dT.getD (6 * t + r) 0) j) (y r j) :=
    fun r hr j hj => (hy r hr j hj).1
  have hysq : ∀ r < 6, ∀ j < 4, y r j * y r j = 1 := fun r hr j hj => (hy r hr j hj).2
  have hyc : ∀ r < 6, ∀ i < 4, ∀ j < 4, Commute (y r i) (y r j) := fun r hr =>
    commute_of_commPK (by norm_num) (by norm_num) (hyp r hr) (hsd r hr).2.2.2.1
  have hds : ∀ r < 6, List.Forall₂ (Rep 36) ((sixDs t).getD r [])
      (List.ofFn fun i : Fin 4 => y r i) := fun r hr =>
    forall₂_of_tabsPK (hsd r hr).1 (by rw [← lenT_eq]; exact Nat.eq_of_beq_eq_true (hsd r hr).2.1)
      (hyp r hr)
  have hmemD : ∀ r < 6, ∀ {G : Nat} {a : Equiv.Perm (Fin 36)}, PRep 36 6 G a →
      G >>> (36 * 6) = 0 → (memPK (36 * 6) (E.dS.getD (6 * t + r) 0) 16 G = true ↔
        a ∈ Subgroup.closure (Set.range fun i : Fin 4 => y r i)) :=
    fun r hr _ _ hG sG => memPK_span_iff (c := 4) (by norm_num) (by norm_num) prepOne (hyp r hr)
      (hysq r hr) (hyc r hr) (hsd r hr).2.2.2.2 hG sG
  set S₀ : Set (Equiv.Perm (Fin 36)) := {u | ∃ j < 5, u = c * sp6CentGens1.getD j 1 * c⁻¹}
    with hS₀
  have hlen1 : sp6CentGens1.length = 5 := rfl
  have hgen : ∀ j < 5, PRep 36 6 (C1Q.S j) (sp6CentGens1.getD j 1) := fun j hj =>
    prep_of_imageList (chainC1.2.2.2.1 j (by rw [hlen1]; exact hj))
  have hS : ∀ u ∈ S₀, ∀ r < 6, ∃ s < 6,
      (Subgroup.closure (Set.range fun i : Fin 4 => y r i)).map (MulAut.conj u).toMonoidHom =
        Subgroup.closure (Set.range fun i : Fin 4 => y s i) := by
    rintro _ ⟨j, hj, rfl⟩ r hr
    have hgj := Orb.allN_iff.1 h13 j hj
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hgj
    obtain ⟨hpj, hsig⟩ := hgj
    have hxj := hgen j hj
    have hxji := prep_inv_of_permOK hpj hxj
    have hY := prep_pcomp (by norm_num) hc (prep_pcomp (by norm_num) hxj hci)
    have hYI := prep_pcomp (by norm_num) hc (prep_pcomp (by norm_num) hxji hci)
    have hG := Orb.allN_iff.1 hsig r hr
    unfold sixG at hG
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at hG
    obtain ⟨hs6, hA, hB⟩ := hG
    have hs6' : E.sig.getD (6 * (5 * t + j) + r) 0 < 6 := Nat.blt_eq.mp hs6
    refine ⟨_, hs6', le_antisymm ?_ ?_⟩
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have hm := Orb.allN_iff.1 hA i i.2
      have hP := prep_pcomp (by norm_num) hY (prep_pcomp (by norm_num) (hyp r hr i i.2) hYI)
      have hm' := (hmemD _ hs6' hP (shr36 _ _)).1 hm
      have e : c * (sp6CentGens1.getD j 1 * c⁻¹) * (y r i * (c * ((sp6CentGens1.getD j 1)⁻¹ *
          c⁻¹))) = MulAut.conj (c * sp6CentGens1.getD j 1 * c⁻¹) (y r i) := by
        rw [MulAut.conj_apply]
        group
      rw [e] at hm'
      exact hm'
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      have hm := Orb.allN_iff.1 hB i i.2
      have hP := prep_pcomp (by norm_num) hYI (prep_pcomp (by norm_num) (hyp _ hs6' i i.2) hY)
      have hm' := (hmemD r hr hP (shr36 _ _)).1 hm
      refine ⟨_, hm', ?_⟩
      change MulAut.conj (c * sp6CentGens1.getD j 1 * c⁻¹) _ = _
      rw [MulAut.conj_apply]
      group
  have hr1 := prepRep (i := 0) (by norm_num)
  have hzm : E.zM.getD t 0 < 2 ^ 5 := by
    rw [h32]
    exact Nat.blt_eq.mp h10
  have hzx : mprod x (E.zM.getD t 0) 5 = c * (sp6InvReps.getD 0 1 * c⁻¹) := by
    refine SporSch.MOC.prep_unique (hspW _ hzm) ?_
    rw [Nat.eq_of_beq_eq_true h11]
    exact prep_pcomp (by norm_num) hc (prep_pcomp (by norm_num) hr1 hci)
  have hfix : ∀ s < 2 ^ 5, fixK 36 6 (laneK (36 * 6) (E.sW.getD t 0) s) = 16 →
      s = E.zM.getD t 0 := by
    intro s hs h
    have := Orb.allN_iff.1 h12 s (h32 ▸ hs)
    rw [Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact h)] at this
    exact Nat.eq_of_beq_eq_true this
  have hfz : fixK 36 6 (laneK (36 * 6) (E.sW.getD t 0) (E.zM.getD t 0)) = 16 := by
    have := Orb.allN_iff.1 h12 _ (h32 ▸ hzm)
    rw [Orb.bIf_eq] at this
    by_contra hne
    rw [if_neg (by rw [Nat.beq_eq]; exact hne), Orb.bIf_eq, if_pos (by rw [Nat.beq_eq])] at this
    exact Bool.false_ne_true this
  have hK : ∀ g ∈ sp6Q.originalSubgroup,
      (∀ i, ∃ e, g * (fun i : Fin 5 => x i) i * g⁻¹ = eElt (fun i : Fin 5 => x i) e) →
        g ∈ Subgroup.closure S₀ := by
    intro g hg hN
    have hgz : g * mprod x (E.zM.getD t 0) 5 * g⁻¹ ∈
        Subgroup.closure (Set.range fun i : Fin 5 => x i) :=
      map_conj_closure_le hN ⟨_, mprod_mem_closure x _ 5, rfl⟩
    obtain ⟨s, hs, hsz⟩ := exists_mprod_of_mem_closure hxsq hxc hgz
    have hfs : fixK 36 6 (laneK (36 * 6) (E.sW.getD t 0) s) = 16 := by
      rw [fixK_eq (hspW s hs), hsz, fixC_conj, ← fixK_eq (hspW _ hzm)]
      exact hfz
    rw [hfix s hs hfs, hzx] at hsz
    have hcomm : g * (c * (sp6InvReps.getD 0 1 * c⁻¹)) = c * (sp6InvReps.getD 0 1 * c⁻¹) * g := by
      calc g * (c * (sp6InvReps.getD 0 1 * c⁻¹))
          = g * (c * (sp6InvReps.getD 0 1 * c⁻¹)) * g⁻¹ * g := by group
        _ = c * (sp6InvReps.getD 0 1 * c⁻¹) * g := by rw [← hsz]
    have hyC : c⁻¹ * g * c ∈ centralizerIn sp6Q.originalSubgroup (sp6InvReps.getD 0 1) := by
      refine mem_centralizerIn.2 ⟨sp6Q.originalSubgroup.mul_mem
        (sp6Q.originalSubgroup.mul_mem (sp6Q.originalSubgroup.inv_mem hcH) hg) hcH, ?_⟩
      calc c⁻¹ * g * c * sp6InvReps.getD 0 1
          = c⁻¹ * (g * (c * (sp6InvReps.getD 0 1 * c⁻¹))) * c := by group
        _ = c⁻¹ * (c * (sp6InvReps.getD 0 1 * c⁻¹) * g) * c := by rw [hcomm]
        _ = sp6InvReps.getD 0 1 * (c⁻¹ * g * c) := by group
    rw [sp6_cent_spec₁.1, sp6CentQ1, certificate_originalSubgroup] at hyC
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hyC
    rw [MonoidHom.map_closure] at hmap
    have e : (MulAut.conj c).toMonoidHom (c⁻¹ * g * c) = g := by
      change MulAut.conj c (c⁻¹ * g * c) = g
      rw [MulAut.conj_apply]
      group
    rw [e] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (Set.mem_setOf_eq ▸ hu)
    refine ⟨j, hlen1 ▸ hj, ?_⟩
    change MulAut.conj c _ = _
    rw [MulAut.conj_apply, List.getD_eq_getElem _ _ hj]
  have hpat : ∀ s < 2 ^ 5,
      Nat.beq ((E.pat.getD t []).getD s 0) (sixPat t (laneK (36 * 6) (E.sW.getD t 0) s)) = true ∧
        allN s (fun s' => bIf(Nat.beq ((E.pat.getD t []).getD s 0)
          ((E.pat.getD t []).getD s' 0), false, true)) = true := by
    intro s hs
    have := Orb.allN_iff.1 h14 s (h32 ▸ hs)
    simpa only [Orb.bAnd_eq, Bool.and_eq_true] using this
  have hne : ∀ s < 2 ^ 5, ∀ s' < s, (E.pat.getD t []).getD s 0 ≠ (E.pat.getD t []).getD s' 0 := by
    intro s hs s' hs' he
    have := Orb.allN_iff.1 (hpat s hs).2 s' hs'
    rw [Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact he)] at this
    exact Bool.false_ne_true this
  have hsep : ∀ a b : Equiv.Perm (Fin 36),
      a ∈ Subgroup.closure (Set.range fun i : Fin 5 => x i) →
      b ∈ Subgroup.closure (Set.range fun i : Fin 5 => x i) →
      (∀ r < 6, a ∈ Subgroup.closure (Set.range fun i : Fin 4 => y r i) ↔
        b ∈ Subgroup.closure (Set.range fun i : Fin 4 => y r i)) → a = b := by
    intro a b ha hb hab
    obtain ⟨s, hs, rfl⟩ := exists_mprod_of_mem_closure hxsq hxc ha
    obtain ⟨s', hs', rfl⟩ := exists_mprod_of_mem_closure hxsq hxc hb
    have hp : sixPat t (laneK (36 * 6) (E.sW.getD t 0) s) =
        sixPat t (laneK (36 * 6) (E.sW.getD t 0) s') := by
      unfold sixPat
      refine patK_congr 6 fun r hr => ?_
      rw [Bool.eq_iff_iff, hmemD r hr (hspW s hs) (laneK_shr _ _ _),
        hmemD r hr (hspW s' hs') (laneK_shr _ _ _)]
      exact hab r hr
    have hpq : (E.pat.getD t []).getD s 0 = (E.pat.getD t []).getD s' 0 := by
      rw [Nat.eq_of_beq_eq_true (hpat s hs).1, Nat.eq_of_beq_eq_true (hpat s' hs').1, hp]
    rcases lt_trichotomy s s' with h | h | h
    · exact absurd hpq.symm (hne s' hs' s h)
    · rw [h]
    · exact absurd hpq (hne s hs s' h)
  have hk6 : sixW t < 6 := by interval_cases t <;> decide
  have hidx : [1, 1, 3, 3, 4, 4].getD (sixW t) 0 = sixW t := by interval_cases t <;> rfl
  have hcent : ∀ g ∈ sp6Q.originalSubgroup, ∀ T, Rep 36 T g →
      (∀ i, g * (fun i : Fin 5 => x i) i = (fun i : Fin 5 => x i) i * g) →
        ∃ e, eElt (fun i : Fin 5 => x i) e = g := by
    intro g hg T hT hcomm
    have hc5 := cands5_centTest hk6 (sp6Q_originalSubgroup ▸ hg) hT
    rw [hidx] at hc5
    unfold centTestS at hc5
    rw [(commAllT_iff hws hT).2 hcomm, Bool.true_and, Bool.not_eq_false', inSp_spanTabs,
      inSpanT_iff (by norm_num) hws hT] at hc5
    exact hc5
  have hdl : (sixDs t).length = 6 := by interval_cases t <;> rfl
  exact sixTestS_false_of_gens (by norm_num) hws hdl (k := fun _ => 4) (d := fun r i => y r i)
    hds (fun r hr i => hysq r hr i i.2) (fun r hr i j => hyc r hr i i.2 j j.2) hS hK hsep hcent hg
    hT

theorem cands5_sixTest
    {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36) {T : Table}
    (hT : Rep 36 T g) :
    sixTestS 36 (cands5.getD 1 []) (spanTabs 36 (cands5.getD 1 [])) ds1 (ds1.map (spanTabs 36))
        T = false ∧
      sixTestS 36 (cands5.getD 3 []) (spanTabs 36 (cands5.getD 3 [])) ds3
        (ds3.map (spanTabs 36)) T = false ∧
      sixTestS 36 (cands5.getD 4 []) (spanTabs 36 (cands5.getD 4 [])) ds4
        (ds4.map (spanTabs 36)) T = false :=
  ⟨sixTest_of (t := 0) (by norm_num) ch725106s0 hg hT,
    sixTest_of (t := 1) (by norm_num) ch725106s1 hg hT,
    sixTest_of (t := 2) (by norm_num) ch725106s2 hg hT⟩

end CertificateChecks.KernelS6I

end
