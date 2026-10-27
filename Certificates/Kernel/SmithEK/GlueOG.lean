module

public import Certificates.Kernel.SmithEK.GlueOU
public import Certificates.Kernel.SmithEK.PinsOG

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

theorem tvGens_eq_L : tvGens = (pts.L.filter (fun c => weightC c == 2) ++ [85]).toArray := by
  unfold tvGens
  rw [uPts_eq, List.filter_toArray, List.push_toArray]

theorem gen_get {g : Nat} (hg : g < 46) : tvGens[g]! = pts.L.getD (po.G.getD g 0) 0 := by
  have hlen : po.G.length = 46 := poG_lt.1
  rw [tvGens_eq_L, ← c21262gen, getElem!_pos _ g (by simp [hlen, hg]), List.getElem_toArray,
    List.getElem_map, List.getD_eq_getElem po.G 0 (by omega)]

theorem genPt_eq {g : Nat} (hg : g < 46) : uPos[tvGens[g]!]! = po.G.getD g 0 := by
  have H := CFSG.KC.Misc.Lines.Pts.of CFSG.KD.Misc.T46.pts CFSG.KD.Misc.Lines.pos
  have hq := poG_lt.2 g hg
  have hlen : pts.L.length = 693 := pts_length
  have hc : pts.L.getD (po.G.getD g 0) 0 < 4096 := by
    rw [ptsL_eq]
    exact H.lt _ hq
  have hnd : pts.L.Nodup := ptsL_eq ▸ H.nodup
  rw [gen_get hg, uPos_get hc, uPts_eq, List.toList_toArray,
    List.getD_eq_getElem pts.L 0 (by omega), hnd.idxOf_getElem]

theorem img46_gen : ∀ g < 46, ∀ j < 891, ∃ j' < 891, ∀ m < 21,
    uaMem uaPts[j']! (ap tvTabs[uPos[tvGens[g]!]!]! (uaPts[j]!)[m]!) = true := by
  intro g hg j hj
  rw [genPt_eq hg]
  exact ⟨_, (img46 hg hj).1, (img46 hg hj).2⟩

theorem reach46_gen : CFSG.SmithL6.K.Reach 891 46 (· == 0) (fun g j' j => allIn 0 21 fun m =>
    uaMem uaPts[j]! (ap tvTabs[uPos[tvGens[g]!]!]! (uaPts[j']!)[m]!)) :=
  reach46.mono fun g hg _ _ _ _ he => ⟨g, hg, by rw [genPt_eq hg]; exact he⟩

end CertificateChecks.KernelSmithEK
