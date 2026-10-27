module

public import CFSG.Timmesfeld.Exceptional.DeepQInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermSound
public import CFSG.Certificates.Kernel.Misc.Coset.ActSound
public import Certificates.Kernel.Misc.Coset.XQAB
public import Certificates.Kernel.Misc.Coset.XQC3
public import Certificates.Kernel.Misc.Coset.XQP.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Timmesfeld.Exceptional.DeepQData
import CFSG.Timmesfeld.Exceptional.DeepQTabInputs
import CFSG.Certificates.PresentationLetters
import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Timmesfeld.Exceptional.DeepQWalk

public section

namespace CertificateChecks.KernelMiscCoset.C8054

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Timmesfeld.Moufang.Deep CFSG.Certificates

set_option maxRecDepth 100000

theorem tAB : relsAB.map encW = CFSG.KBRoute.XQAB.rels := by decide +kernel
theorem tQC3 : (relsQ ++ [wQC3]).map encW = CFSG.KBRoute.XQC3.rels := by decide +kernel

theorem card_AB : Finite (PG (subsetOf 3 [0, 1]).length relsAB) ∧
    Nat.card (PG (subsetOf 3 [0, 1]).length relsAB) ≤ 360 := by
  have h := XQAB.t1
  unfold CFSG.KBRoute.XQAB.T1.ok at h
  exact card_le_of_tableOk relsAB tAB h (by decide) CFSG.KBRoute.XQAB.top rfl

theorem card_QC3 : Finite (PG 3 (relsQ ++ [wQC3])) ∧ Nat.card (PG 3 (relsQ ++ [wQC3])) ≤ 1 := by
  have h := XQC3.t1
  unfold CFSG.KBRoute.XQC3.T1.ok at h
  exact card_le_of_tableOk _ tQC3 h (by norm_num) CFSG.KBRoute.XQC3.top rfl

theorem tabs : ∀ x : Fin 162,
    CFSG.KAct.XQP.A (x.val * 6) = tabA[x.val]! % 162 ∧
    CFSG.KAct.XQP.A (x.val * 6 + 1) = tabAi[x.val]! % 162 ∧
    CFSG.KAct.XQP.A (x.val * 6 + 2) = tabB[x.val]! % 162 ∧
    CFSG.KAct.XQP.A (x.val * 6 + 3) = tabBi[x.val]! % 162 ∧
    CFSG.KAct.XQP.A (x.val * 6 + 4) = tabQ[x.val]! % 162 ∧
    CFSG.KAct.XQP.A (x.val * 6 + 5) = tabQi[x.val]! % 162 := by
  decide +kernel

theorem rep : Act.Rep CFSG.KAct.XQP.A 3 162 psi := by
  intro g x
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := tabs x
  fin_cases g
  · exact ⟨h0, h1⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h4, h5⟩

theorem hrels : (relsQ ++ [wQC6]).map Act.revCodes = CFSG.KAct.XQP.rels := by decide +kernel
theorem hws : ((List.finRange 360).map w3).map Act.revCodes = CFSG.KAct.XQP.ws := by
  decide +kernel

theorem relsAll : Act.allR 0 162 (Act.relsAt CFSG.KAct.XQP.A (Nat.add 3 3) CFSG.KAct.XQP.rels) =
    true := by quickRfl

theorem distinct : Act.distinctOK CFSG.KAct.XQP.A (Nat.add 3 3) 162 CFSG.KAct.XQP.ws
    CFSG.KAct.XQP.base CFSG.KAct.XQP.ord = true := by quickRfl

theorem perm_facts :
    (∀ r ∈ relsQ, signedProd psi r = 1) ∧ signedProd psi wQC6 = 1 ∧
      ∀ i j : Fin 360, signedProd psi (w3 i) = signedProd psi (w3 j) → i = j := by
  have hr := Act.relsAt_sound rep (relsQ ++ [wQC6]) hrels
    (fun x hx => Act.allR_spec relsAll x (Nat.zero_le x) (by omega))
  refine ⟨fun r h => hr r (List.mem_append_left _ h), hr _ (by simp), ?_⟩
  intro i j hij
  have hd := Act.distinctOK_sound rep ((List.finRange 360).map w3) hws distinct i.val j.val
    (by simp) (by simp) (by simpa using hij)
  exact Fin.ext hd

end CertificateChecks.KernelMiscCoset.C8054

end
