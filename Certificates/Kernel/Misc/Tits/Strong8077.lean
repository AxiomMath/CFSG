
module

public import Certificates.Kernel.Misc.Tits.Strong8077Base

public import CFSG.Quasithin.Recognition.CertTitsBase
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsSimpleInputs
public import Certificates.Certificate8072
public import Certificates.Kernel.Misc.Tits.Prim8077
public import Certificates.Kernel.TitsW.Alg
public import Certificates.Kernel.Sporadic.Tits.GroupT2264
public import CFSG.Certificates.Kernel.Spor.StrongOfSound
public import CFSG.Certificates.Kernel.Spor.Co2ChainSound
public import CFSG.Certificates.Kernel.Spor.DecLinesRead
public import CFSG.Certificates.Kernel.YModel.Sound
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate8071Base

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelMisc CertificateChecks.KernelTitsW CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelMisc.TitsPrim8077

namespace CertificateChecks.TitsStrong8077

theorem gens_get : titsGens.size = 2 ∧ ∀ j < 2, titsGens[j]! = unpack 1755 11 (DS j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [← derived_get (by omega)]
  interval_cases j
  · exact Certificates.certificate8072.1
  · exact Certificates.certificate8072.2

theorem word_eq {k : Nat} (hl : lettersOK 2 (titsAbWords.getD k []) = true) :
    wordA 1755 titsGens (rawInvs 1755 titsGens) (titsAbWords.getD k []) =
      unpack 1755 11 (WD (abW.getD k [])) := by
  have hl' : lettersK 2 (titsAbWords.getD k []) = true := by
    rw [CFSG.KS.Co2SShape.lettersK_eq]
    exact hl
  have e := wordArr_pk (wd := titsAbWords.getD k []) gens_get perm2 hl'
  rw [words_eq] at e ⊢
  exact e

theorem a_eq : CFSG.Quasithin.titsA = unpack 1755 11 A := word_eq letters₀

theorem b_eq : CFSG.Quasithin.titsB = unpack 1755 11 B := word_eq letters₁

theorem pair_get : titsPairO.size = 2 ∧
    ∀ j < 2, titsPairO[j]! = unpack 1755 11 (TitsPCh.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · rw [s_eq.1]
    exact a_eq
  · rw [s_eq.2]
    exact b_eq

theorem strong_get : titsPairStrong.size = 12 ∧
    ∀ j < 12, titsPairStrong[j]! = unpack 1755 11 (TitsPCh.S j) := by
  rw [titsPairStrong, pwords_eq]
  exact strongOf_bind pair_get TitsPCh.head

theorem binds : Binds 1755 11 TitsPCh.S 12 7 TitsPCh.BP titsPairStrong
    (titsPairBase.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, strong_get.1, strong_get.2, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 baseOK t ht)⟩

end CertificateChecks.TitsStrong8077

end
