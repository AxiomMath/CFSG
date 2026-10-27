module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
meta import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuLB

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def tkM : Array (Array Nat) := (Array.range 19).map ruRepZA

meta def agOf (k : Nat) : Array Nat :=
  compA 4060 (compA 4060 (ruTEltInvA 64 (ruReps.getD k 0)) ruA0A) (ruTEltA 64 (ruReps.getD k 0))

meta def agM : Array (Array Nat) := (Array.range 19).map agOf

meta def r3 (t0 t1 t2 : Array Nat) (y : Nat) : Nat := t0[t1[t2[y]!]!]!

meta def itM (f : Nat → Nat) : Nat → Nat → Nat
  | 0, y => y
  | e + 1, y => f (itM f e y)

meta def fixBM (f : Nat → Nat) (e : Nat) : Bool := Nat.all 4 fun b _ => itM f e b == b

meta def pCM (ag : Array Nat) (f : Nat) (t0 t1 t2 : Array Nat) : Bool :=
  let sq := Nat.all 4060 fun x _ => r3 t0 t1 t2 (r3 t0 t1 t2 x) == ruZA[x]!
  if f == 0 then sq else
    sq && fixBM (fun y => ag[r3 t0 t1 t2 y]!) 13 &&
      fixBM (fun y => ag[r3 t0 t1 t2 (ag[r3 t0 t1 t2 (r3 t0 t1 t2 y)]!)]!) 29

meta def cntCOf (i : Nat) : Nat := Id.run do
  let f := i / 30
  let ag := agOf (if f == 1 then 3 else if f == 2 then 6 else 11)
  let C0 := ruLevC[0]!
  let C1 := ruLevC[1]!
  let C2 := ruLevC[2]!
  let mut s := 0
  for a in [64 * (i % 30):64 * (i % 30) + 64] do
    for b in [0:64] do
      for c in [0:2] do
        if pCM ag f C0.tr[a]! C1.tr[b]! C2.tr[c]! then s := s + 1
  return s

meta def cntCM : Array Nat := (Array.range 120).map cntCOf

end CertificateChecks.KernelSporSch.RuLB

#kss_perms CertificateChecks.KernelSporSch.RuLB.TK 12 CertificateChecks.KernelSporSch.RuLB.tkM
#kss_perms CertificateChecks.KernelSporSch.RuLB.AG 12 CertificateChecks.KernelSporSch.RuLB.agM
#ks_perm CertificateChecks.KernelSporSch.RuLB.CNTC 16 CertificateChecks.KernelSporSch.RuLB.cntCM

end
