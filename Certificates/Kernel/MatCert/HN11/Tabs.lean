module

public import Init
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.FactsVMeta
meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData7
import Certificates.Kernel.LocalComp.FactsVMeta
meta import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Attr
meta import Mathlib.Data.Fintype.Basic
meta import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CertificateChecks.KernelMC.HN11

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.KC.LocalComp.FactsVMeta

meta def targets : Array (Array Nat) :=
  targetsA hn_11_claims.nregs hn_11_claims.prog hn_11_claims.prog.length

meta def fin : Array (Array Nat) :=
  finalsA hn_11_claims.nregs hn_11_claims.prog hn_11_claims.prog.length

meta def hints : Array (Array Nat) := hintsA hn_11_claims.nregs hn_11_claims.prog hn_11_claims.facts

end CertificateChecks.KernelMC.HN11

#kmisc_packarrs CertificateChecks.KernelMC.HN11.TT CertificateChecks.KernelMC.HN11.targets 20
#kmisc_packarrs CertificateChecks.KernelMC.HN11.RF CertificateChecks.KernelMC.HN11.fin 20
#kmisc_packarrs CertificateChecks.KernelMC.HN11.HH CertificateChecks.KernelMC.HN11.hints 20
