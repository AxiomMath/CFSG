
module

public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public import CFSG.Sporadic.Schreier.Co1QuotData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Stab

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.KS.SporSch.M24
open CertificateChecks.KernelSporSch.Co1Packed

@[expose] def PH0 : Nat :=
  40584372574752461558315032334763544499848355601370546653061007492290883240327371597262711795126445042701922541064472474686813628768024629068435326096629713250008096481230603

@[expose] def PH1 : Nat :=
  204015709521279255658856852960877788325435225079138605254574853718776266918459600320638142556223065995085203512093514651307490346883232707148022015834703987339151471097052026

theorem k0 : wordEqK PA PB Data.stabWord0 PH0 = true := by quickRfl
theorem k1 : wordEqK PA PB Data.stabWord1 PH1 = true := by quickRfl
theorem b0 : CFSG.KS.Raw.bindListK 24 24 PH0 Data.subRows0 = true := by quickRfl
theorem b1 : CFSG.KS.Raw.bindListK 24 24 PH1 Data.subRows1 = true := by quickRfl

theorem h0_eq : hRows0 = Data.subRows0.toArray := by
  unfold hRows0
  rw [aR_u, bR_u, wordEqK_sound k0, rows_of b0]

theorem h1_eq : hRows1 = Data.subRows1.toArray := by
  unfold hRows1
  rw [aR_u, bR_u, wordEqK_sound k1, rows_of b1]

end CertificateChecks.KernelSporSch.Co1Stab

end
