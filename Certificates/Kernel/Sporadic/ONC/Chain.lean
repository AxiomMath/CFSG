
module

public import Certificates.Kernel.Sporadic.ONC.ChainBase

public import Certificates.Kernel.Sporadic.ONC.Group
public import Certificates.Kernel.Sporadic.ONC.Defs
public import CFSG.Certificates.Kernel.Spor.ONCSound
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.TabWords
import Certificates.Kernel.Sporadic.ONC.Slp
import Certificates.Kernel.Sporadic.ONC.Let0
import Certificates.Kernel.Sporadic.ONC.Let1
import Certificates.Kernel.Sporadic.ONC.Let2
import Certificates.Kernel.Sporadic.ONC.Let3
import Certificates.Kernel.Sporadic.ONC.Let4
import Certificates.Kernel.Sporadic.ONC.Let5
import Certificates.Kernel.Sporadic.ONC.Let6
import Certificates.Kernel.Sporadic.ONC.Let7
import Certificates.Kernel.Sporadic.ONC.Inv0
import Certificates.Kernel.Sporadic.ONC.Inv1
import Certificates.Kernel.Sporadic.ONC.T0a
import Certificates.Kernel.Sporadic.ONC.T0b
import Certificates.Kernel.Sporadic.ONC.T0c
import Certificates.Kernel.Sporadic.ONC.T0d
import Certificates.Kernel.Sporadic.ONC.T1
import Certificates.Kernel.Sporadic.ONC.Hd
import Certificates.Kernel.Sporadic.ONC.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open Matrix CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.ONC
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt)

theorem letters_card : Nat.card (Subgroup.closure (Set.range fun l : Fin 8 => permOfT nPts lettersT[l.val]!)) ≤
    ((List.range 3).map TCNT).prod := by
  obtain ⟨c0, c1, c2⟩ := tcnt_chain
  have hprod : ((List.range 3).map TCNT).prod = 460815505920 := by
    simp [List.range_succ, c0, c1, c2]
  rw [hprod]
  have hle : Subgroup.closure (Set.range fun l : Fin 8 => permOfT nPts lettersT[l.val]!) ≤
      (MulAction.toPermHom J0 (Fin nPts)).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨l, hl⟩, rfl⟩
    rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
    · exact ⟨gs0 j, (permOfT_rep (rep_even (by omega))).symm⟩
    · exact ⟨(gs0 j)⁻¹, (permOfT_rep (rep_odd (by omega))).symm⟩
  calc _ ≤ Nat.card (MulAction.toPermHom J0 (Fin nPts)).range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card J0 := Nat.card_le_card_of_surjective _
        (MulAction.toPermHom J0 (Fin nPts)).rangeRestrict_surjective
    _ ≤ 460815505920 := card_J0_le

theorem chain_eq : chainTrees nPts lettersT chainBase =
      Array.ofFn (n := 3) (fun i => tbfsRec 245520 (TCNT i.val) (TPTS i.val) (TPOS i.val)
        (TPAR i.val) (TLAB i.val)) ∧
    ∀ chunks, chainOK nPts lettersT chainBase chainQ chainQb
      (chainTrees nPts lettersT chainBase) chunks = true :=
  pchain_of_card chain_hyp letters_card

end CertificateChecks.KernelSpor.ONC

end
