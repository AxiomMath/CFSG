module

public import Certificates.Kernel.LocalComp.HeldFixGraph.All
public import Certificates.Kernel.LocalComp.L34Cert
public import Certificates.Kernel.Sporadic.OddCore.HLF

public section

namespace CertificateChecks.KernelLC.HeldFixGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.Sporadic.SmallOddCore

theorem hD : heDGens = DD := by
  apply Array.ext (by simp [heDGens, DD])
  intro i h1 h2
  have hi : i < 5 := by simpa [DD] using h2
  rw [← getElem!_pos heDGens i h1, ← getElem!_pos DD i h2,
    CertificateChecks.KernelSpor.HeL.dgens_get hi]
  unfold DD
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem hS : gensS = SS := by
  apply Array.ext (by simp [gensS, SS])
  intro i h1 h2
  have hi : i < 3 := by simpa [SS] using h2
  rw [← getElem!_pos gensS i h1, ← getElem!_pos SS i h2, L34Cert.bindS.2 i hi]
  unfold SS
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem gens_eq : heldFixGraphGens = hgg := by
  unfold heldFixGraphGens hgg
  rw [hD, hS]

theorem hd3 : HFG.k = 8 ∧ HFG.cnt = 20160 ∧
    penumHdK (pidn 147 8) HFG.cnt 20160 HFG.T HFG.PL = true := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using k_hd :
    Nat.beq HFG.k 8 = true ∧ Nat.beq HFG.cnt 20160 = true ∧ _)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3⟩

theorem pt : ∀ i < HFG.cnt, penumPtK 147 8 (mask 8) (147 * 8) false HFG.G HFG.GI 8 HFG.cnt HFG.T
    HFG.PL HFG.POS HFG.SRT HFG.SRI i = true := by
  intro i hi
  have hi' : i < 20160 := hd3.2.1 ▸ hi
  have hs : i / 32 < 630 := by omega
  exact penumSl_spec (HFG.all (i / 32) hs) i (by change i / 32 * 32 ≤ i; omega)
    (by change i < i / 32 * 32 + 32; omega) hi

theorem enc : enumBFS 147 hgg 20160 = penumRec 147 8 HFG.cnt HFG.T HFG.PL ∧
    enumOK 147 hgg (penumRec 147 8 HFG.cnt HFG.T HFG.PL) = true :=
  penumK_left_sound (by decide) (gensOK_of k_gens) hd3.2.2 pt

theorem graph_true : enumOK 147 heldFixGraphGens heldFixGraphEnum = true ∧
    heldFixGraphEnum.tabs.size = 20160 := by
  unfold heldFixGraphEnum
  rw [gens_eq, enc.1]
  refine ⟨enc.2, ?_⟩
  rw [penumRec_eq, Array.size_ofFn, hd3.2.1]

end CertificateChecks.KernelLC.HeldFixGraph

end
