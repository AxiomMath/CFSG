module

public import Certificates.Kernel.Q8Wit.J2Checks
public import CFSG.Certificates.Kernel.Q8WitSound

public section

namespace CertificateChecks.KernelQ8W.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit CFSG.KC.E81K Certificates.TwinPerpSmSp1
open CFSG.ComponentClassification.J2Cover (sylowStrong)

@[expose] noncomputable def pinQ : Pin 315 9 j2Wit.syl.qKeys :=
  ⟨Q.ng, Q.N, Q.G, Q.T, Q.E, Q.S, SK, Q.ok, keys⟩

theorem pgE : j2Wit.syl.pg.size = 3 ∧ ∀ j < 3, j2Wit.syl.pg[j]! = unpack 315 9 (PG j) := by
  have h := bindPG
  rw [Bool.and_eq_true] at h
  have hs : sylowStrong.size = 5 := Nat.eq_of_beq_eq_true h.1
  have e : j2Wit.syl.pg = sylowStrong.extract 0 3 := rfl
  have hsz : (sylowStrong.extract 0 3).size = 3 := by
    rw [Array.size_extract, hs]
    rfl
  refine ⟨by rw [e, hsz], fun j hj => ?_⟩
  have e2 : (sylowStrong.extract 0 3)[j]! = sylowStrong[j]! := by
    rw [getElem!_pos _ j (by rw [hsz]; exact hj), Array.getElem_extract,
      getElem!_pos sylowStrong j (by omega)]
    simp only [Nat.zero_add]
  rw [e, e2]
  exact unpack_eq_of_bindArrK (allN_spec h.2 j hj)

theorem q8Wit_true : q8WitCheck j2Wit = true := by
  have bX := binds_of_check bindXG
  exact q8WitCheck_of_pins j2Wit rfl hw PG pgE.1 pgE.2 (allN_spec permPG) (by decide)
    lettersQ pinQ wordsQ rfl (by decide) XG bX.1 bX.2 (allN_spec permXG) lettersC C wordsC
    SQ I CI tabs invs free

end CertificateChecks.KernelQ8W.J2

end
