module

public import CFSG.Certificates.Kernel.Spor.RelSound
public import CFSG.Monster.Schur.TripleM12Data
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Range.Basic
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.TripleM12

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Monster.Schur CFSG.KS.Rel

theorem rels_K : relK 24 5 m12TabH1 (invT 24 m12TabH1) m12TabH2 (invT 24 m12TabH2)
    [m12R1, m12R2, m12R3] = true := by
  quickRfl

theorem inv_one : invOK 24 m12TabH1 (invT 24 m12TabH1) = true := by decide +kernel

theorem inv_two : invOK 24 m12TabH2 (invT 24 m12TabH2) = true := by decide +kernel

theorem moves : (ap m12TabH1 1 != 1) = true := by decide +kernel

theorem m12Check_true : m12Check = true := by
  unfold m12Check
  rw [relK_sound rels_K, inv_one, inv_two, moves]
  rfl

end CertificateChecks.KernelMisc.TripleM12

end
