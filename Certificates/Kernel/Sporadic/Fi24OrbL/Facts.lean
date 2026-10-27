module

public import Certificates.Kernel.Sporadic.Fi24OrbL.FactsPrelude
import all Certificates.Kernel.Sporadic.Fi24OrbL.FactsPrelude
public import CFSG.Sporadic.Fi24.Simple

public import Certificates.Kernel.Sporadic.Fi24OrbL.FactsBase
import all Certificates.Kernel.Sporadic.Fi24OrbL.FactsBase

public import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
public import Certificates.Kernel.Sporadic.Fi24Form.Final
import Certificates.Kernel.Sporadic.Fi24Orb.Small
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CertificateChecks.KernelFi24OrbL

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.KC.Fi24Orb CFSG.KD.Fi24Net CFSG.KS.Fi24Net
  CertificateChecks.KernelFi24Orb

theorem pairG_LN : ∀ l < 26, ∀ p < 306936, idx 306936 (pairG gs l) p = LN NW l p := by
  intro l hl p hp
  rw [← rep_pairG_all l (by rw [core_facts.letters_size]; exact hl) p hp]
  exact letters_LN l hl p hp

end CertificateChecks.KernelFi24OrbL
