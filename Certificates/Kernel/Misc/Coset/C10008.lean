module

public import CFSG.LieType.Multipliers.Sz8BridgeInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XSz8R
public import Certificates.Kernel.Misc.Coset.C10008M
public import Certificates.Kernel.Misc.Coset.C10008G0
public import Certificates.Kernel.Misc.Coset.C10008G1
public import Certificates.Kernel.Misc.Coset.C10008G2
public import Certificates.Kernel.Misc.Coset.C10008G3
public import Certificates.Kernel.Misc.Coset.C10008G4
public import Certificates.Kernel.Misc.Coset.C10008G5
public import Certificates.Kernel.Misc.Coset.C10008G6
public import Certificates.Kernel.Misc.Coset.C10008G7
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMiscCoset.C10008

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8

set_option maxRecDepth 100000

theorem genCheck_eq_true : genCheck = true := by
  refine List.all_eq_true.2 fun c hc => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi8 : i < 8 := by simpa [allF8] using hi
  interval_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7

theorem tR : rels.map encW = CFSG.KBRoute.XSz8R.rels := by decide +kernel
theorem wR : CFSG.KBRoute.XSz8R.T1.words = [encW [((1 : Fin 2), true)]] := by decide +kernel
theorem pR : (List.replicate 4 [((1 : Fin 2), true)]).flatten ∈ rels := by decide +kernel

theorem card_le : Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 29120 := by
  have h := XSz8R.t1
  unfold CFSG.KBRoute.XSz8R.T1.ok at h
  have hi := zpowers_index_le_of_tableOk rels tR h (by norm_num) CFSG.KBRoute.XSz8R.top _ wR
  exact card_le_of_zpowers_index rels _ (by norm_num) pR hi

end CertificateChecks.KernelMiscCoset.C10008

end
