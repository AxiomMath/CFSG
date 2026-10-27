module

public import Certificates.Kernel.Sporadic.OddCore.ON2120F
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2120

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore

theorem head : headP CLit LLit = true := by quickRfl

@[expose] noncomputable def recK (k : Nat) : Bool :=
  candCheckP (CLit.records.getD k default) (LLit.lw.getD k []) (LLit.cands.getD k []) k

theorem rec0 : recK 0 = true := by quickRfl
theorem rec1 : recK 1 = true := by quickRfl
theorem rec2 : recK 2 = true := by quickRfl
theorem rec3 : recK 3 = true := by quickRfl
theorem rec4 : recK 4 = true := by quickRfl
theorem rec5 : recK 5 = true := by quickRfl
theorem rec6 : recK 6 = true := by quickRfl
theorem rec7 : recK 7 = true := by quickRfl
theorem rec8 : recK 8 = true := by quickRfl
theorem rec9 : recK 9 = true := by quickRfl
theorem rec10 : recK 10 = true := by quickRfl
theorem rec11 : recK 11 = true := by quickRfl

theorem facts2120 :
    candidatesCheck (wordArrs Data.MWords) = true :=
  candidatesCheck_of head fun k hk => by
    change recK k = true
    interval_cases k
    exacts [rec0, rec1, rec2, rec3, rec4, rec5, rec6, rec7, rec8, rec9, rec10, rec11]

end CertificateChecks.KernelSpor.ON2120

end
