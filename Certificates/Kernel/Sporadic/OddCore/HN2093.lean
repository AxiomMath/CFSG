
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.OddCore.LinesCmd
public import CFSG.Certificates.Kernel.Spor.DecLinesRead
public import CFSG.Sporadic.HNOddCore.WCheckInputs
public import CFSG.Sporadic.Schreier.ONPermArr
meta import CFSG.Sporadic.HNOddCore.WCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.ClsT CFSG.Sporadic.HNOddCore.InvData.clsText

#ks_lines CertificateChecks.KernelSpor.ClsT CFSG.Sporadic.HNOddCore.InvData.clsLists

namespace CertificateChecks.KernelSpor.HN2093

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native

theorem clsLists_eq : InvData.clsLists = (ClsT.E.map List.toArray).toArray := by
  unfold InvData.clsLists
  rw [ClsT.eq]
  exact CFSG.KS.DecLines.linesOf_of_chk ClsT.ok

theorem allBelowN_eq (n : Nat) (p : Nat → Bool) : allBelowN n p = (List.range n).all p := by
  apply Bool.eq_iff_iff.2
  simp [allBelowN_iff, List.all_eq_true]

theorem facts2093 : witCoverChecks = true := by
  unfold witCoverChecks pReps
  rw [clsLists_eq]
  simp only [allBelowN_eq]
  decide +kernel

end CertificateChecks.KernelSpor.HN2093

end
