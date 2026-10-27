module

public import Certificates.Kernel.Tri.LeechShort
public import Certificates.Kernel.Tri.LeechTabs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.Short.AxisAction
public import CFSG.Monster.B.Short.OrbitCertBase
public import CFSG.Monster.B.Short.OrbitSpec

public section

namespace CertificateChecks.KernelLeech

open CFSG.KLie.CT CFSG.KC.Leech CFSG.Monster.Tri.Leech CertificateChecks.Short3014

@[expose] noncomputable def longT : ℕ → Bool := longAt memS 4600 12288 NB LGP LGL

@[expose] noncomputable def longBF (k : Nat) : Bool := allFrom (230 * k) 230 longT

#kc_each_unfold longBF 0 20 as CertificateChecks.KernelLeech.b

theorem long_all : allN 4600 longT = true := by
  refine of_blocks fun k hk => ?_
  interval_cases k
  exacts [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19]

theorem leechLong_ok : leechLongCheck = true := by
  have e := long_eq (klev := shortKlev) nbr_bind.1 nbr_bind.2 longPar_bind.2 longLev_bind.2 12288
  rw [shortHit_fun] at e
  exact e.trans long_all

end CertificateChecks.KernelLeech

end
