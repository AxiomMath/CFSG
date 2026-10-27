module

public import Certificates.Kernel.RonanWit.OmegaCheck
public import CFSG.Certificates.Kernel.Wit3KSound
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OmegaData
public import Certificates.Kernel.OmegaEight.Aut
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.Common.Harness
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

namespace CertificateChecks.KernelRonanWit.Omega

open CFSG.KC.Wit3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.RonanK432 CertificateChecks.KernelO8

theorem gsEq : allN 10 (fun k => Nat.beq (AP.S k) (GS k)) = true := by quickRfl

theorem binds :
    omWitData.gens.size = 10 ∧ ∀ k < 10, omWitData.gens[k]! = unpack 360 9 (GS k) :=
  ⟨genAP.1, fun k hk => by
    change CFSG.EvenSmallLie.OmegaEight.genArrs[k]! = _
    rw [genAP.2 k hk, Nat.eq_of_beq_eq_true (allN_spec gsEq k hk)]⟩

theorem goodP : P.Good 360 9 10 10 GS where
  head := headP
  ps := by decide
  word k hk := by
    have := allN_spec wordsP k hk
    rwa [Bool.and_eq_true] at this
  pt := CFSG.KC.Misc.Clos.forall_of_chunks 81 9 _ ptS
  key i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 81 9 _ kyS i hi
    rw [Bool.and_eq_true] at this
    exact this.1
  ord i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 81 9 _ kyS i hi
    rw [Bool.and_eq_true] at this
    exact this.2

theorem goodQ : Q.Good 360 9 10 8 GS where
  head := headQ
  ps := by decide
  word k hk := by
    have := allN_spec wordsQ k hk
    rwa [Bool.and_eq_true] at this
  pt := CFSG.KC.Misc.Clos.forall_of_chunks 81 3 _ qptS
  key i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 81 3 _ qkyS i hi
    rw [Bool.and_eq_true] at this
    exact this.1
  ord i hi := by
    have := CFSG.KC.Misc.Clos.forall_of_chunks 81 3 _ qkyS i hi
    rw [Bool.and_eq_true] at this
    exact this.2

theorem fact : WitFact omWitData :=
  witK_sound (n := 360) (w := 9) (by quickRfl) binds permS (by decide) goodP goodQ
    (ny := 2) (YS := YS) (yws := yws) (fun l hl => by
      have := allN_spec wordsY l hl
      rwa [Bool.and_eq_true] at this)
    (W := W) (CFSG.KC.Misc.Clos.forall_of_chunks 81 9 _ wtS)

end CertificateChecks.KernelRonanWit.Omega

end
