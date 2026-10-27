module

public import Certificates.Kernel.SmithEK.GlueOStab

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab

theorem ptsL_eq : pts.L = CFSG.KD.Misc.Unitary.UL :=
  List.toArray_inj (uPts_eq.symm.trans CFSG.KD.Misc.Unitary.hU)

theorem getD_mem {l : List Nat} {k : Nat} (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem pl0_lt {k : Nat} (hk : k < 21) : (po.PL.getD 0 []).getD k 0 < 693 := by
  have h := plK_sound c21262pl_0 0 (by rw [pb_len]; omega)
  exact h.2.1 _ (getD_mem (by rw [h.1]; exact hk))

theorem pl0_get {k : Nat} (hk : k < 21) : (po.PL.getD 0 []).getD k 0 = (uaPts[0]!)[k]! := by
  have H := CFSG.KC.Misc.Lines.Pts.of CFSG.KD.Misc.T46.pts CFSG.KD.Misc.Lines.pos
  have h := List.all_eq_true.1 c21262pl0 k (List.mem_range.2 hk)
  rw [beq_iff_eq] at h
  have hq := pl0_lt hk
  have e : (uaPts[0]!)[k]! = uPos[normC (uaVec (wB 0) uaAl[k]!)]! := by
    unfold uaPts
    rw [CFSG.SmithL6.Kernel.ofFn_get! _ (by omega : 0 < 891), CFSG.SmithL6.Kernel.ofFn_get! _ hk]
    rfl
  have hlen : pts.L.length = 693 := pts_length
  have hc : pts.L.getD ((po.PL.getD 0 []).getD k 0) 0 < 4096 := by
    rw [ptsL_eq]
    exact H.lt _ hq
  have hnd : pts.L.Nodup := ptsL_eq ▸ H.nodup
  have hql : (po.PL.getD 0 []).getD k 0 < pts.L.length := by omega
  rw [e, ← h, uPos_get hc, uPts_eq, List.toList_toArray, List.getD_eq_getElem pts.L 0 hql,
    hnd.idxOf_getElem]

theorem sw_get {g : Nat} (hg : g < 34) :
    po.SW.getD g 0 = stabWords[g]!.1 + 1024 * stabWords[g]!.2 := by
  have hs : g < stabWords.size := sw_lt.1 ▸ hg
  rw [← c21262sw, List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map,
    getElem!_pos stabWords g hs, Array.getElem_toList]

theorem stabSig_get {g : Nat} (hg : g < 34) {k : Nat} (hk : k < 21) :
    (stabSig tvTabs uaPts[0]! stabWords[g]!)[k]! = (po.SG.getD g []).getD k 0 := by
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts (i := 0) (by omega)
  have hs := sgK_sound c21262sg_0 g (by rw [← c21262sw, List.length_map]; simpa using sw_lt.1 ▸ hg)
  have hsk : (po.SG.getD g []).getD k 0 < 21 := hs.2.1 _ (getD_mem (by rw [hs.1]; exact hk))
  have e1 := hs.2.2 k hk
  rw [sw_get hg, pl0_get hk, pl0_get hsk] at e1
  unfold stabSig
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hk]
  change uaPos uaPts[0]! (stabAp tvTabs stabWords[g]! (uaPts[0]!)[k]!) = _
  rw [(stabAp_TP (sw_mem hg) (hlt k hk)).1, ← e1,
    ← CFSG.LargeExtraspecial.SMod20.wPt_val (by omega) hsk,
    CFSG.LargeExtraspecial.SMod20.uaPos_wPt (by omega) hsk]

theorem collAmatN_eq {s : Array Nat} {sl : List Nat} (hs : ∀ j < 9, s[j]! = sl.getD j 0)
    (a : Nat) : ∀ n ≤ 9, collAmatN s a n = Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Nat.xor acc (bif bitK a j then po.CO.getD (sl.getD j 0) 0 else 0)) n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [collAmatN, collAmatN_eq hs a n (by omega)]
    change _ = Nat.xor _ _
    rw [bitK_eq, hs n (by omega), co_get]
    cases a.testBit n <;> rfl

theorem collAmat_eq {g : Nat} (hg : g < 34) (u : Nat) :
    collAmat (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! u = amK po.CO (po.SG.getD g []) u := by
  have hs : g < stabWords.size := sw_lt.1 ▸ hg
  rw [getElem!_pos _ g (by rw [Array.size_map]; exact hs), Array.getElem_map,
    ← getElem!_pos stabWords g hs]
  exact collAmatN_eq (fun j hj => stabSig_get hg (by omega)) u 9 le_rfl

theorem uaRoot_eq : ∀ c, uaRoot c = rootU c
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

theorem reachU : CFSG.SmithL6.K.Reach 512 34 (fun v => v == uaRoot (uaCls collS2 v))
    (fun g u v => uaCls collS2 u == uaCls collS2 v &&
      collAmat (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! u == v) := by
  have h := CFSG.SmithL6.K.reach_of_treeK c21262utree_0
  intro Q hroot hstep
  refine h Q (fun v hv hr => hroot v hv ?_) (fun g hg u hu v hv he hQ => hstep g hg u hu v hv ?_ hQ)
  · unfold rootUK at hr
    rw [beq_iff_eq, uaRoot_eq, uaCls_eq hv, ← Nat.beq_eq]
    exact hr
  · unfold edgeU at he
    rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at he
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, uaCls_eq hu, uaCls_eq hv, collAmat_eq hg]
    exact he

end CertificateChecks.KernelSmithEK
