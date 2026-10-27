module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Th687.AutD
meta import Certificates.Data.Th687.AutD
meta import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.AutDG

open CFSG.PSL3Four.Native CFSG.Sporadic.Th.Recog

meta def letM : Array (Array Nat) := letArr

meta def letIM : Array (Array Nat) := letInv ()

meta def idM : Array Nat := idTab 51

meta def h0M : Array Nat := hTab 0

meta def x1M : Array Nat := x1Tab ()

meta def piM : Array (Array Nat) := (piArr.push iotaTab).map fun p => #[CFSG.KS.RawGen.pack 6 p]

meta def awIdx (_ : Unit) : Std.HashMap (Tab × Tab) Nat := Id.run do
  let E := (dEnum ()).tabs
  let EI := dEnumInv ()
  let F : Array (Tab × Tab) := ((twList ()).map fun f => (f.2.1, f.2.2)).toArray
  let mut idx : Std.HashMap (Tab × Tab) Nat := {}
  for f in [0:F.size] do
    for m in [0:E.size] do
      let key := (comp 51 (comp 51 E[m]! F[f]!.1) EI[m]!, comp 51 (comp 51 E[m]! F[f]!.2) EI[m]!)
      if !idx.contains key then
        idx := idx.insert key (1 + 4096 * f + m)
  return idx

meta def awPairs (_ : Unit) : Array (Option (Tab × Tab)) := Id.run do
  let E := (dEnum ()).tabs
  let EI := dEnumInv ()
  let xs := #[(hTab 0, hInv 0), (x1Tab (), x1Inv ())]
  let mut ps : Array (Option (Tab × Tab)) := #[]
  for i in [0:E.size] do
    for (x, xi) in xs do
      ps := ps.push <| if autTests.all (fun S => wTab #[x, E[i]!] #[xi, EI[i]!] S == idTab 51)
        then some (x, E[i]!) else none
  return ps

meta def awGo (_ : Unit) : Array (Array Nat) :=
  let idx := awIdx ()
  let ws := (awPairs ()).map fun p => match p with
    | some k => idx.getD k 0
    | none => 0
  (List.range ((ws.size + 15) / 16)).toArray.map fun j => ws.extract (16 * j) (16 * j + 16)

meta def awM : Array (Array Nat) := awGo ()

end CertificateChecks.KernelTh.AutDG

#kpenum CertificateChecks.KernelTh.ADE 51 6 false CertificateChecks.KernelTh.AutDG.letM
  CertificateChecks.KernelTh.AutDG.letM CertificateChecks.KernelTh.AutDG.idM 3456
#kpenum CertificateChecks.KernelTh.AOA 51 6 true CertificateChecks.KernelTh.AutDG.letM
  CertificateChecks.KernelTh.AutDG.letIM CertificateChecks.KernelTh.AutDG.h0M 3456
#kpenum CertificateChecks.KernelTh.AOB 51 6 true CertificateChecks.KernelTh.AutDG.letM
  CertificateChecks.KernelTh.AutDG.letIM CertificateChecks.KernelTh.AutDG.x1M 3456
#kmisc_packarrs CertificateChecks.KernelTh.AutDG.API CertificateChecks.KernelTh.AutDG.piM 306
#kmisc_packarrs CertificateChecks.KernelTh.AutDG.AWP CertificateChecks.KernelTh.AutDG.awM 16

end
