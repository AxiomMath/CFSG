module

public import Certificates.Kernel.TwoHSLe4.SO5K
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGCore
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGCore
public import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

meta def p0M : Array (Array ℕ) := pgP0Code.toArray
meta def s0M : Array (Array ℕ) := pgS0Code.toArray
meta def cj1M : Array (Array ℕ) := (pgConjCode.map (·.1)).toArray
meta def cj2M : Array (Array ℕ) := (pgConjCode.map (·.2.1)).toArray
meta def cjiM : Array (Array ℕ) := #[(pgConjCode.map (·.2.2.val)).toArray]
meta def sgM : Array (Array ℕ) :=
  #[pgTau1C, pgTau2C, pgTau3C, pgTau4C, pgX15C, pgX13C, pgR0C, pgSf0C, pgS1C, pgF2C 1 0,
    pgF2C 1 1, pgF2C 3 0, pgF2C 3 1]

end CertificateChecks.KernelTwoHSLe4.SO5

#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.SO5.P0 CertificateChecks.KernelTwoHSLe4.SO5.p0M 3
#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.SO5.S0 CertificateChecks.KernelTwoHSLe4.SO5.s0M 3
#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.SO5.CJ1 CertificateChecks.KernelTwoHSLe4.SO5.cj1M 3
#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.SO5.CJ2 CertificateChecks.KernelTwoHSLe4.SO5.cj2M 3
#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.SO5.CJI CertificateChecks.KernelTwoHSLe4.SO5.cjiM 2
#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.SO5.SG CertificateChecks.KernelTwoHSLe4.SO5.sgM 3

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def P0L : List ℕ := (List.range 128).map P0

@[expose] noncomputable def S0L : List ℕ := (List.range 120).map S0

@[expose] noncomputable def CJL : List (ℕ × ℕ × ℕ) :=
  (List.range pgConjCode.length).map fun i => (CJ1 i, CJ2 i, pg 2 (mask 2) (CJI 0) i)

@[expose] noncomputable def rotK (k : ℕ) : ℕ := powK (SG 6) k

@[expose] noncomputable def reflK (k : ℕ) : ℕ := mulK (SG 7) (rotK k)

@[expose] noncomputable def D0L : List ℕ := (List.range 4).flatMap fun k => [rotK k, reflK k]

@[expose] noncomputable def CL : List ℕ := D0L.flatMap fun d => S0L.map (mulK d)

end CertificateChecks.KernelTwoHSLe4.SO5

end
