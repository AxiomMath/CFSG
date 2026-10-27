module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Schreier.RuArrays
meta import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Sporadic.Schreier.RuEnum
public import Mathlib.GroupTheory.Schreier
meta import CFSG.Sporadic.Schreier.RuEnum
meta import Mathlib.GroupTheory.Schreier

public section

namespace CertificateChecks.KernelSporSch.RuG

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def wz0M : Array Nat := compA 4060 ruWA ruZ0A

meta def wz0wiM : Array Nat := compA 4060 wz0M (ruInv ruWA)

meta def u3M : Array Nat := powA 4060 ruUA 3

meta def wiM : Array Nat := ruInv ruWA

meta def hiM : Array Nat := ruInv ruHA

meta def hn0M : Array Nat := compA 4060 ruHA ruN0A

meta def hn1M : Array Nat := compA 4060 ruHA ruN1A

meta def valsM (rows : List SlotRow) (t₁ t₂ : Array Nat) : Array (Array Nat) := Id.run do
  let mut s : List (Nat × Array Nat) := [(1, t₁), (2, t₂)]
  let mut vs : Array (Array Nat) := #[t₁, t₂]
  for r in rows do
    match r with
    | .mu i j k =>
      let v := compA 4060 (slotReadA 4060 s i) (slotReadA 4060 s j)
      vs := vs.push v
      s := (k, v) :: s
    | .iv i j =>
      let v := invCand 4060 (slotReadA 4060 s i)
      vs := vs.push v
      s := (j, v) :: s
    | .pwr e i j =>
      let v := powA 4060 (slotReadA 4060 s i) e
      vs := vs.push v
      s := (j, v) :: s
  return vs

meta def valsCM : Array (Array Nat) := valsM ruCProg ruA0A ruA1A

meta def valsNM : Array (Array Nat) := valsM ruNProg ruA0A ruA1A

meta def z0PM : Array (Array Nat) := (Array.range 22).map fun q =>
  wordA 4060 #[ruN0A, ruN1A] #[ruInv ruN0A, ruInv ruN1A] (ruNCenterWord.drop (10 * q))

meta def sgiM : Array (Array Nat) := ruSGensA.map ruInv

meta def a0iM : Array Nat := ruInv ruA0A

meta def a1iM : Array Nat := ruInv ruA1A

meta def c0iM : Array Nat := ruInv ruC0A

meta def c1iM : Array Nat := ruInv ruC1A

meta def n0iM : Array Nat := ruInv ruN0A

meta def n1iM : Array Nat := ruInv ruN1A

meta def ns0iM : Array Nat := ruInv ruNs0A

meta def ns1iM : Array Nat := ruInv ruNs1A

end CertificateChecks.KernelSporSch.RuG

#ks_perm CertificateChecks.KernelSporSch.RuG.A0I 12 CertificateChecks.KernelSporSch.RuG.a0iM
#ks_perm CertificateChecks.KernelSporSch.RuG.A1I 12 CertificateChecks.KernelSporSch.RuG.a1iM
#ks_perm CertificateChecks.KernelSporSch.RuG.C0I 12 CertificateChecks.KernelSporSch.RuG.c0iM
#ks_perm CertificateChecks.KernelSporSch.RuG.C1I 12 CertificateChecks.KernelSporSch.RuG.c1iM
#ks_perm CertificateChecks.KernelSporSch.RuG.N0I 12 CertificateChecks.KernelSporSch.RuG.n0iM
#ks_perm CertificateChecks.KernelSporSch.RuG.N1I 12 CertificateChecks.KernelSporSch.RuG.n1iM
#ks_perm CertificateChecks.KernelSporSch.RuG.Ns0I 12 CertificateChecks.KernelSporSch.RuG.ns0iM
#ks_perm CertificateChecks.KernelSporSch.RuG.Ns1I 12 CertificateChecks.KernelSporSch.RuG.ns1iM
#kss_perms CertificateChecks.KernelSporSch.RuG.SGI 12 CertificateChecks.KernelSporSch.RuG.sgiM
#kss_perms CertificateChecks.KernelSporSch.RuG.Z0P 12 CertificateChecks.KernelSporSch.RuG.z0PM
#kss_perms CertificateChecks.KernelSporSch.RuG.VC 12 CertificateChecks.KernelSporSch.RuG.valsCM
#kss_perms CertificateChecks.KernelSporSch.RuG.VN 12 CertificateChecks.KernelSporSch.RuG.valsNM
#ks_perm CertificateChecks.KernelSporSch.RuG.C0 12 CFSG.Sporadic.RuSchreier.ruC0A
#ks_perm CertificateChecks.KernelSporSch.RuG.C1 12 CFSG.Sporadic.RuSchreier.ruC1A
#ks_perm CertificateChecks.KernelSporSch.RuG.N0 12 CFSG.Sporadic.RuSchreier.ruN0A
#ks_perm CertificateChecks.KernelSporSch.RuG.N1 12 CFSG.Sporadic.RuSchreier.ruN1A
#ks_perm CertificateChecks.KernelSporSch.RuG.Z 12 CFSG.Sporadic.RuSchreier.ruZA
#ks_perm CertificateChecks.KernelSporSch.RuG.Z0 12 CFSG.Sporadic.RuSchreier.ruZ0A
#ks_perm CertificateChecks.KernelSporSch.RuG.W 12 CFSG.Sporadic.RuSchreier.ruWA
#ks_perm CertificateChecks.KernelSporSch.RuG.WI 12 CertificateChecks.KernelSporSch.RuG.wiM
#ks_perm CertificateChecks.KernelSporSch.RuG.WZ0 12 CertificateChecks.KernelSporSch.RuG.wz0M
#ks_perm CertificateChecks.KernelSporSch.RuG.WZ0WI 12 CertificateChecks.KernelSporSch.RuG.wz0wiM
#ks_perm CertificateChecks.KernelSporSch.RuG.U 12 CFSG.Sporadic.RuSchreier.ruUA
#ks_perm CertificateChecks.KernelSporSch.RuG.U3 12 CertificateChecks.KernelSporSch.RuG.u3M
#ks_perm CertificateChecks.KernelSporSch.RuG.H 12 CFSG.Sporadic.RuSchreier.ruHA
#ks_perm CertificateChecks.KernelSporSch.RuG.HI 12 CertificateChecks.KernelSporSch.RuG.hiM
#ks_perm CertificateChecks.KernelSporSch.RuG.HN0 12 CertificateChecks.KernelSporSch.RuG.hn0M
#ks_perm CertificateChecks.KernelSporSch.RuG.HN1 12 CertificateChecks.KernelSporSch.RuG.hn1M
#ks_perm CertificateChecks.KernelSporSch.RuG.Ns0 12 CFSG.Sporadic.RuSchreier.ruNs0A
#ks_perm CertificateChecks.KernelSporSch.RuG.Ns1 12 CFSG.Sporadic.RuSchreier.ruNs1A
#kss_perms CertificateChecks.KernelSporSch.RuG.SG 12 CFSG.Sporadic.RuSchreier.ruSGensA

end
