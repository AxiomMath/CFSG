module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Schreier.RuOrbLInvInputs
meta import CFSG.Sporadic.Schreier.RuOrbLInvInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuLA

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def fixM (t : Array Nat) : Nat := (List.range 4060).countP fun x => t[x]! == x

meta def orbFixM (t : Array Nat) : Nat := Id.run do
  let L0 := ruLevL[0]!
  let L1 := ruLevL[1]!
  let mut s := 0
  for a in [0:1820] do
    for b in [0:64] do
      let q := (L1.tr[b]!)[0]!
      let p := (L0.tr[a]!)[q]!
      if t[p]! == p then s := s + 1
  return s

meta def invM (t : Array Nat) : Array Nat :=
  #[orbFixM t] ++ (Array.range 3).flatMap fun i =>
    let yt := compA 4060 (ruZLA i) t
    #[fixM yt, fixM (compA 4060 yt yt)]

meta def invsM : Array Nat := (Array.range 19).flatMap fun k => invM (ruRepZA k)

end CertificateChecks.KernelSporSch.RuLA

#ks_perm CertificateChecks.KernelSporSch.RuLA.INV 16 CertificateChecks.KernelSporSch.RuLA.invsM

end
