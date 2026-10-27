module

public import Certificates.Kernel.Sporadic.OddCore.McLTwo
public import Certificates.Data.Kernel.Ivk8TwoN
public import Certificates.Data.GH74.McLWeights
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelIvk8McLWt

open CFSG.KC.Ivk8N CFSG.KC.YoshQ CFSG.Sporadic.Recognition.McLAS
  CertificateChecks.KernelSpor

@[expose] noncomputable def wtGs : List Nat := (List.range 6).map fun i => McLTwoS.T wtIdx[i]!

@[expose] noncomputable def wtGis : List Nat := wtGs.map (invN 275 9)

@[expose] noncomputable def wtRelsN (R : List (List Int × List Int)) : Bool :=
  R.all fun r => eqN 275 9 (evalN 275 9 wtGs wtGis r.1) (evalN 275 9 wtGs wtGis r.2)

@[expose] noncomputable def wtNeN (R : List (List Int × List Int × Nat)) : Bool :=
  R.all fun r => decide (r.2.2 < 275) &&
    CFSG.Sporadic.Th.Native.ap (tabN 275 9 (evalN 275 9 wtGs wtGis r.1)) r.2.2 !=
      CFSG.Sporadic.Th.Native.ap (tabN 275 9 (evalN 275 9 wtGs wtGis r.2.1)) r.2.2

theorem wtRelsN_ok : wtRelsN wtRels = true := by
  quickRfl

theorem wtNeN_ok : wtNeN wtNe = true := by
  quickRfl

end CertificateChecks.KernelIvk8McLWt

end
