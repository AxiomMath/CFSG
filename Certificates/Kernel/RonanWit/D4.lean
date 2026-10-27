module

public import Certificates.Kernel.RonanWit.D4Check
public import CFSG.Certificates.Kernel.Wit3KSound
public import CFSG.RankThree.PartTwo.Sec4.RonanK432D4TwoData
public import Certificates.Kernel.D4.Facts
public import Certificates.Kernel.D4.ChainAD
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import Certificates.Certificate8166

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelRonanWit.D4

open CFSG.KC.Wit3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.RonanK432 CFSG.RankThree.PartTwo.Sec4.Item434D42
open CertificateChecks.KernelD4

theorem gsEq : allN 2 (fun k => Nat.beq (CA.S k) (GS k)) = true := by quickRfl

theorem binds :
    d4WitData.gens.size = 2 ∧ ∀ k < 2, d4WitData.gens[k]! = unpack 2457 12 (GS k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec gsEq k hk)
  interval_cases k
  · change d4ChainAArrs[0]! = _
    rw [bindsA.2.2.2.2.1 0 (by norm_num), e]
  · change d4ChainAArrs[1]! = _
    rw [bindsA.2.2.2.2.1 1 (by norm_num), e]

theorem good : P.Good 2457 12 2 2 GS where
  head := head
  ps := by decide
  word k hk := by
    have := allN_spec wordsP k hk
    rwa [Bool.and_eq_true] at this
  pt := CFSG.KC.Misc.Clos.forall_of_chunks 27 3 _ ptS
  key i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 27 3 _ kyS i hi
    rw [Bool.and_eq_true] at this
    exact this.1
  ord i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 27 3 _ kyS i hi
    rw [Bool.and_eq_true] at this
    exact this.2

theorem fact : WitFact d4WitData := by
  have hy := wordsY
  rw [Bool.and_eq_true] at hy
  exact witK_sound (n := 2457) (w := 12) (by quickRfl) binds permS le_rfl good good
    (ny := 1) (YS := YS) (yws := yws) (fun l hl => by
      obtain rfl : l = 0 := by omega
      exact hy)
    (W := W) (CFSG.KC.Misc.Clos.forall_of_chunks 27 3 _ wtS)

end CertificateChecks.KernelRonanWit.D4

end
