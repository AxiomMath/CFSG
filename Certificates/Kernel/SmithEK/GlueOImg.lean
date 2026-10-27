module

public import Certificates.Kernel.SmithEK.GlueO
public import Certificates.Kernel.SmithEK.ChecksO
public import Certificates.Kernel.Misc.TvTabs
public import Certificates.Kernel.Misc.Lines
public import Certificates.Kernel.Misc.T46
public import Certificates.Certificate21263
public import CFSG.Certificates.Kernel.Misc.XiTab
public import CFSG.Certificates.Kernel.SmithL6KSound
public import CFSG.LargeExtraspecial.SMod20UaCert
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Misc.XiBits
public import CFSG.Certificates.Kernel.SmithEK.OSound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option exponentiation.threshold 1000

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

#kc_forall_tree img_all (fun g => genImgK (packK pb.P) (CFSG.KD.Misc.Xi.TP (po.G.getD g 0)) po.PL
  (po.J.getD g []) = true) 46 CertificateChecks.KernelSmithEK.c21262img_

theorem tvTabs_eq_G : tvTabs = CFSG.KC.Misc.Lines.tvTabsG CFSG.KD.Misc.Unitary.UL.toArray := by
  unfold tvTabs CFSG.KC.Misc.Lines.tvTabsG tvTable CFSG.KC.Misc.T46.tvTableG uPos
    CFSG.KC.Misc.T46.uPosG
  rw [CFSG.KD.Misc.Unitary.hU]

theorem ap_tvTabs_TP {f x : Nat} (hf : f < 693) (hx : x < 693) :
    ap tvTabs[f]! x = at' 10 (CFSG.KD.Misc.Xi.TP f) x ∧ at' 10 (CFSG.KD.Misc.Xi.TP f) x < 693 := by
  have H := CFSG.KC.Misc.Lines.Pts.of CFSG.KD.Misc.T46.pts CFSG.KD.Misc.Lines.pos
  have h := CFSG.KC.Misc.Xi.tvTabs_TR H CFSG.KD.Misc.Xi.tabAll hf
  rw [tvTabs_eq_G, (h.2 x hx).1, CFSG.KS.PK.at'_eq]
  exact ⟨rfl, (h.2 x hx).2⟩

theorem poPL_len : po.PL.length = 891 := by
  decide +kernel

theorem pb_lt {j : Nat} (hj : j < 891) : pb.P.getD j 0 < 2 ^ 693 := by
  rw [pb_get hj, ← pts_length]
  exact ptBits_lt _ _

theorem pb_all_lt : ∀ m ∈ pb.P, m < 2 ^ 693 := by
  intro m hm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
  have hj' : j < 891 := pb_len ▸ hj
  have := pb_lt hj'
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem uaPts_mem_pl {j m : Nat} (hj : j < 891) (hm : m < 21) :
    (uaPts[j]!)[m]! ∈ po.PL.getD j [] := by
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts hj
  have h := plK_sound c21262pl_0 j (by rw [pb_len]; exact hj)
  rw [← maskK_testBit, h.2.2, ← uaMem_pb hj (hlt m hm)]
  unfold uaMem
  exact anyIn_eq_true.2 ⟨m, hm, beq_self_eq_true _⟩

theorem poG_lt : po.G.length = 46 ∧ ∀ g < 46, po.G.getD g 0 < 693 := by
  refine ⟨by decide +kernel, ?_⟩
  have h : (List.range 46).all (fun g => decide (po.G.getD g 0 < 693)) = true := by decide +kernel
  intro g hg
  simpa using List.all_eq_true.1 h g (List.mem_range.2 hg)

theorem img46 {g : Nat} (hg : g < 46) {j : Nat} (hj : j < 891) :
    (po.J.getD g []).getD j 0 < 891 ∧ ∀ m < 21,
      uaMem uaPts[(po.J.getD g []).getD j 0]! (ap tvTabs[po.G.getD g 0]! (uaPts[j]!)[m]!) = true := by
  have h := genImgK_sound (img_all g hg) j (by rw [poPL_len]; exact hj)
  refine ⟨h.1, fun m hm => ?_⟩
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts hj
  have hT := ap_tvTabs_TP (poG_lt.2 g hg) (hlt m hm)
  have hb := h.2 _ (uaPts_mem_pl hj hm)
  rw [at'_packK _ pb_all_lt] at hb
  rw [hT.1, uaMem_pb h.1 hT.2]
  exact hb

theorem poJ_len : po.J.length = 46 ∧ ∀ g < 46, (po.J.getD g []).length = 891 := by
  refine ⟨by decide +kernel, ?_⟩
  have h : (List.range 46).all (fun g => Nat.beq (lenK (po.J.getD g [])) 891) = true := by
    decide +kernel
  intro g hg
  have := List.all_eq_true.1 h g (List.mem_range.2 hg)
  rwa [Nat.beq_eq, lenK_eq] at this

theorem reach46 : CFSG.SmithL6.K.Reach 891 46 (· == 0) (fun g j' j => allIn 0 21 fun m =>
    uaMem uaPts[j]! (ap tvTabs[po.G.getD g 0]! (uaPts[j']!)[m]!)) := by
  refine (CFSG.SmithL6.K.reach_of_treeK c21262tree_0).mono fun g hg u hu v hv he => ⟨g, hg, ?_⟩
  have hJ : ∀ x ∈ po.J.getD g [], x < 1024 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
    have hp' : p < 891 := (poJ_len.2 g hg) ▸ hp
    have := (img46 hg hp').1
    rw [List.getD_eq_getElem _ _ hp] at this
    omega
  rw [edgeJ_eq c21262jp_0 (by rw [poJ_len.1]; exact hg) hJ] at he
  subst he
  exact allIn_eq_true.2 fun m _ hm => (img46 hg hu).2 m hm

end CertificateChecks.KernelSmithEK
