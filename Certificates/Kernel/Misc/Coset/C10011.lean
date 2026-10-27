module

public import CFSG.LieType.Multipliers.U42Data
public import CFSG.Certificates.Kernel.Spor.RelSound
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XU42R
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Fischer.Classification.PartIII.Beta.Data
import Certificates.Data.CFSGNative.Th.Tables
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelMiscCoset.C10011

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers.U42

set_option maxRecDepth 100000 in
theorem relK_eq : CFSG.KS.Rel.relK 45 6 (tauTab 0) (tauTab 0) (seqTab bIdx)
    (seqTab bIdx.reverse) checkWords = true := by
  quickRfl

theorem t : rels.map encW = CFSG.KBRoute.XU42R.rels := by decide +kernel
theorem w : CFSG.KBRoute.XU42R.T1.words = [encW [((0 : Fin 2), true), (1, true)]] := by
  decide +kernel
theorem hp : (List.replicate 9 [((0 : Fin 2), true), (1, true)]).flatten ∈ rels := by
  decide +kernel

theorem card_le : Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 25920 := by
  have h := XU42R.t1
  unfold CFSG.KBRoute.XU42R.T1.ok at h
  have hi := zpowers_index_le_of_tableOk rels t h (by norm_num) CFSG.KBRoute.XU42R.top _ w
  exact card_le_of_zpowers_index rels _ (by norm_num) hp hi

end CertificateChecks.KernelMiscCoset.C10011

end
