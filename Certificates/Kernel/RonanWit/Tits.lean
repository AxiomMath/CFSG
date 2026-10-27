module

public import Certificates.Kernel.RonanWit.TitsCheck
public import CFSG.Certificates.Kernel.Wit3KSound
public import CFSG.RankThree.PartTwo.Sec4.RonanK432TitsData
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import Certificates.Kernel.Sporadic.Tits.ChainD
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

namespace CertificateChecks.KernelRonanWit.Tits

open CFSG.KC.Wit3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.RonanK432 CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264

theorem gsEq : allN 2 (fun k => Nat.beq (TitsD.S k) (GS k)) = true := by quickRfl

theorem binds :
    titsWitData.gens.size = 2 ∧ ∀ k < 2, titsWitData.gens[k]! = unpack 1755 11 (GS k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec gsEq k hk)
  interval_cases k
  · change titsDerivedArrs[0]! = _
    rw [der_eq (by norm_num), e]
  · change titsDerivedArrs[1]! = _
    rw [der_eq (by norm_num), e]

theorem good : P.Good 1755 11 2 2 GS where
  head := head
  ps := by decide
  word k hk := by
    have := allN_spec wordsP k hk
    rwa [Bool.and_eq_true] at this
  pt := CFSG.KC.Misc.Clos.forall_of_chunks 27 1 _ ptS
  key i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 27 1 _ kyS i hi
    rw [Bool.and_eq_true] at this
    exact this.1
  ord i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 27 1 _ kyS i hi
    rw [Bool.and_eq_true] at this
    exact this.2

theorem fact : WitFact titsWitData := by
  have hy := wordsY
  rw [Bool.and_eq_true] at hy
  exact witK_sound (n := 1755) (w := 11) (by quickRfl) binds permS le_rfl good good
    (ny := 1) (YS := YS) (yws := yws) (fun l hl => by
      obtain rfl : l = 0 := by omega
      exact hy)
    (W := W) (CFSG.KC.Misc.Clos.forall_of_chunks 27 1 _ wtS)

end CertificateChecks.KernelRonanWit.Tits

end
