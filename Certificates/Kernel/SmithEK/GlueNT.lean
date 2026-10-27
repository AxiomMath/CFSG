module

public import Certificates.Kernel.SmithEK.ChecksNT
public import Certificates.Kernel.SmithEK.GlueN
public import Certificates.Kernel.SmithEK.GlueOU
public import CFSG.Certificates.Kernel.SmithEK.NTSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73 CFSG.LargeExtraspecial.SMod20

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

@[expose] noncomputable def ivFL : List Nat := (List.range 21).flatMap fun y0 => pn.R.getD y0 []

theorem ivFL_facts : ivFL.length = 675 ∧ ∀ v, at' 105 pt.FP v = ivFL.getD v 0 :=
  ivFP_sound c21275fp_0

theorem collI_eq_FL : collI = (ivFL.map ivUnpack).toArray := by
  unfold collI
  rw [collInvs_eq, ivFL, List.map_flatMap]

theorem collI_get {v : Nat} (hv : v < 675) : collI[v]! = ivUnpack (at' 105 pt.FP v) := by
  have hl : v < ivFL.length := by rw [ivFL_facts.1]; exact hv
  rw [collI_eq_FL, getElem!_pos _ v (by rw [List.size_toArray, List.length_map]; exact hl),
    List.getElem_toArray, List.getElem_map, ivFL_facts.2 v, List.getD_eq_getElem _ _ hl]

theorem ivUnpack_get {p k : Nat} (hk : k < 21) : (ivUnpack p)[k]! = at' 5 p k := by
  unfold ivUnpack
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hk]

theorem collI_facts : collI.size = 675 ∧
    ∀ v < 675, collI[v]!.size = 21 ∧ ∀ k < 21, (collI[v]!)[k]! < 21 := by
  refine ⟨by rw [collI_eq_FL, List.size_toArray, List.length_map, ivFL_facts.1],
    fun v hv => ⟨by rw [collI_get hv, ivUnpack, Array.size_ofFn], fun k hk => ?_⟩⟩
  rw [collI_get hv, ivUnpack_get hk]
  exact ivLt_sound c21275lt_0 hv hk

theorem swr_get {g : Nat} (hg : g < 34) :
    pt.SWR.getD g 0 = stabWords[g]!.2 + 1024 * stabWords[g]!.1 := by
  have e := eqLN_true c21275swr_0
  have hl : g < po.SW.length := by rw [← c21262sw, List.length_map]; simpa using sw_lt.1 ▸ hg
  obtain ⟨h1, h2⟩ := sw_lt.2 _ (sw_mem hg)
  rw [e, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hl, sw_get hg]
  change (stabWords[g]!.1 + 1024 * stabWords[g]!.2) / 1024 +
    1024 * ((stabWords[g]!.1 + 1024 * stabWords[g]!.2) % 1024) = _
  omega

theorem srSig_get {g : Nat} (hg : g < 34) {k : Nat} (hk : k < 21) :
    (stabSig tvTabs uaPts[0]! (stabWords[g]!.2, stabWords[g]!.1))[k]! =
      (pt.SR.getD g []).getD k 0 := by
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts (i := 0) (by omega)
  have hsw : pt.SWR.length = 34 := by
    rw [eqLN_true c21275swr_0, List.length_map, ← c21262sw, List.length_map, Array.length_toList,
      sw_lt.1]
  have hs := sgK_sound c21275sr_0 g (by rw [hsw]; exact hg)
  have hsk : (pt.SR.getD g []).getD k 0 < 21 := hs.2.1 _ (getD_mem (by rw [hs.1]; exact hk))
  have e1 := hs.2.2 k hk
  obtain ⟨h1, h2⟩ := sw_lt.2 _ (sw_mem hg)
  have e2 : (stabWords[g]!.2 + 1024 * stabWords[g]!.1) % 1024 = stabWords[g]!.2 := by omega
  have e3 : (stabWords[g]!.2 + 1024 * stabWords[g]!.1) / 1024 = stabWords[g]!.1 := by omega
  rw [swr_get hg, e2, e3, pl0_get hk, pl0_get hsk] at e1
  have hb := ap_tvTabs_TP h1 (hlt k hk)
  have ha := ap_tvTabs_TP h2 hb.2
  unfold stabSig
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hk]
  change uaPos uaPts[0]! (stabAp tvTabs (stabWords[g]!.2, stabWords[g]!.1) (uaPts[0]!)[k]!) = _
  unfold stabAp
  rw [hb.1, ha.1, ← e1, ← CFSG.LargeExtraspecial.SMod20.wPt_val (by omega) hsk,
    CFSG.LargeExtraspecial.SMod20.uaPos_wPt (by omega) hsk]

theorem ntMap_get! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {g : Nat}
    (hg : g < a.size) : (a.map f)[g]! = f a[g]! := by
  rw [getElem!_pos (a.map f) g (by rw [Array.size_map]; exact hg), Array.getElem_map,
    getElem!_pos a g hg]

theorem reachI : CFSG.SmithL6.K.Reach 675 34 (ivRootK pt.RT pt.FP)
    (fun g u v => collComp (collComp (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! collI[u]!)
      (stabWords.map fun w => stabSig tvTabs uaPts[0]! (w.2, w.1))[g]! == collI[v]!) := by
  refine (CFSG.SmithL6.K.reach_of_treeK c21275tree_0).mono fun g hg u hu v hv he =>
    ⟨g, hg, ?_⟩
  have hs : g < stabWords.size := sw_lt.1 ▸ hg
  have hsw : pt.SWR.length = 34 := by
    rw [eqLN_true c21275swr_0, List.length_map, ← c21262sw, List.length_map, Array.length_toList,
      sw_lt.1]
  have hsr := sgK_sound c21275sr_0 g (by rw [hsw]; exact hg)
  rw [beq_iff_eq, ntMap_get! _ _ hs, ntMap_get! _ _ hs]
  refine array_ext_getElem! (collComp_size _ _) ?_ fun k hk => ?_
  · rw [collI_get hv, ivUnpack, Array.size_ofFn]
  have hr : (pt.SR.getD g []).getD k 0 < 21 := hsr.2.1 _ (getD_mem (by rw [hsr.1]; exact hk))
  have hu' := ivLt_sound c21275lt_0 hu hr
  rw [collComp_get hk, srSig_get hg hk, collComp_get hr, collI_get hu, ivUnpack_get hr,
    stabSig_get hg hu', collI_get hv, ivUnpack_get hk, ivEdgeK_sound he hk]

end CertificateChecks.KernelSmithEK
