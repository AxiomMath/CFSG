module

public import Certificates.Kernel.SuzA17321.Chain
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzA17321

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexFlat
open CFSG.HardMathSupport.Dickson.I271.TabSuzA CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem arr_eq (j : ℕ) (hj : j < 11) : arr j = unpack 1782 11 (SAP.F j) := by
  rw [arr, SAP.eq]
  exact hexTable_sound SAP.all j hj

theorem binds : Binds 1782 11 SAC.S 11 6 SAC.BP (aStrong ()) aBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [aStrong], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← Nat.eq_of_beq_eq_true (allN_spec SAC.FS j hj), ← arr_eq j hj]
  unfold aStrong
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem words_eq : aWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 11 SAD := by
  decide +kernel

theorem chain_ok :
    rawChainOK 1782 ((aStrong ()).extract 0 3) (aStrong ()) aBase aWords 1 = true := by
  rw [words_eq]
  exact rawChainK_sound (chunks := 1) binds SAC.head SAC.hl (by decide) SAC.hs

theorem eqA_self (t : Array Nat) : eqA 1782 t t = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem case_chain : CFSG.RankThree.PartOne.caseChainOK3 1782 (aStrong ()) aBase aWords
    (aStrong ())[0]! (aStrong ())[1]! (aStrong ())[2]! = true := by
  rw [CFSG.RankThree.PartOne.caseChainOK3, chain_ok, eqA_self, eqA_self, eqA_self]
  rfl

theorem orbits : rawOrbitSizes 1782 (aStrong ()) aBase = [162, 56, 10, 9, 4, 3] := by
  rw [rawOrbitSizesK_sound binds SAC.perm SAC.hl]
  decide +kernel

end CertificateChecks.KernelSuzA17321

end
