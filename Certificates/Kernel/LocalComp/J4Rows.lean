module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4ActionInputs
public import CFSG.Certificates.Kernel.LocalCompM1Sound
public import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.J4R.JA CFSG.Blueprint.NativeSporadic.J4Seed1
#lc_m1 CertificateChecks.KernelLC.J4R.JA CFSG.Blueprint.NativeSporadic.J4Seed1 112
#ks_chars CertificateChecks.KernelLC.J4R.JB CFSG.Blueprint.NativeSporadic.J4Seed2
#lc_m1 CertificateChecks.KernelLC.J4R.JB CFSG.Blueprint.NativeSporadic.J4Seed2 112

namespace CertificateChecks.KernelLC.J4R

open CFSG.KC.M1F2 CFSG.SectionRank.J4Order

theorem rowsA_eq : rowsA = Array.ofFn (n := 112) fun i => rowF 112 JA.M i.val := by
  have h : CFSG.SectionRank.Native.j4Sylow3Data.seedA = String.ofList JA.chars :=
    (rfl : CFSG.SectionRank.Native.j4Sylow3Data.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans
      JA.eq
  rw [rowsA, h]
  exact j3RowsOfPayload_sound JA.bind

theorem rowsB_eq : rowsB = Array.ofFn (n := 112) fun i => rowF 112 JB.M i.val := by
  have h : CFSG.SectionRank.Native.j4Sylow3Data.seedB = String.ofList JB.chars :=
    (rfl : CFSG.SectionRank.Native.j4Sylow3Data.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans
      JB.eq
  rw [rowsB, h]
  exact j3RowsOfPayload_sound JB.bind

end CertificateChecks.KernelLC.J4R
