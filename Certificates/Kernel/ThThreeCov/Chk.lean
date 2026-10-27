module

public import Certificates.Data.Kernel.ThThreeCov.Defs
public import Certificates.Kernel.ThThreeCov.Data
public import Certificates.Kernel.Th.Fam.K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThThreeCov

open CFSG.KC.Th CFSG.KC.ThThreeCov CFSG.KD.ThThreeCov CertificateChecks.KernelTh.Fam

theorem ch1023506L : andB (Nat.beq (lenR defs) 221) (Nat.beq (lenR cls) 3) = true := by quickRfl

theorem ch1023506S : seedsOK thK RB = true := by quickRfl

@[expose] noncomputable def ch1023506D (c : Nat) : Bool := defsChunk thK RB defs c

#kc_each ch1023506D 0 14

theorem ch1023506G : tabGlobal thK RB (5 + lenR defs) tb g1 g2 ord = true := by quickRfl

@[expose] noncomputable def ch1023506T (j : Nat) : Bool :=
  tabRow thK RB tb g1 g2 kv tpar tgen cl ord j

#kc_each ch1023506T 0 81

theorem ch1023506I : invsOK thK RB (5 + lenR defs) invs = true := by quickRfl

@[expose] noncomputable def ch1023506C (i : Nat) : Bool :=
  clsOK thK RB (5 + lenR defs) tb invs (cls.getD i (0, [], [], []))

#kc_each ch1023506C 0 3

end CertificateChecks.KernelThThreeCov

end
