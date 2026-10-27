module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.McLAS.Meta
meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.McLAS.Meta

namespace CertificateChecks.KernelMcLAS.M

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

meta def yM : Array (Array Nat) := (List.range 10).toArray.map nM
meta def a3R : Array (Array Nat) := mulRec agM 200
meta def r3aR : Array (Array Nat) := conjRec pgM pgiM x3AM 31000
meta def conjN (g x : Table) : Table := conjT 275 g (invT 275 g) x
meta def naM : Array (Array Nat) :=
  (nrmN.toList.flatMap fun n => aGens3.toList.map fun a => natArr (conjN n a)).toArray
meta def pk (a : Array Nat) : Nat := CFSG.KS.RawGen.pack 9 a
meta def below (R : Array Nat) (x : Array Nat) : Nat :=
  let px := pk x
  (R.filter fun t => t < px).size
meta def r3aP : Array Nat := r3aR.map pk
meta def a3P : Array Nat := a3R.map pk
meta def brAM : Array Nat := a3R.map (below r3aP)
meta def id10M : Array Nat := idTab 10
meta def ids2M10 : Array (Array Nat) := #[id10M, id10M]
meta def nwM : Array (Array Nat) := nrmW.map natArr
meta def nwInvM : Array (Array Nat) := nwM.map (CFSG.Monster.B.Co2.Native.invCand 10)
meta def nwR : Array (Array Nat) :=
  (bfs (fun j t => conjTab 10 id10M nwM[j]! t) 2 id10M 800).tabs
meta def tripM : Array Nat := (List.range 1000).toArray.map fun t =>
  ((List.range nwR.size).find? fun i =>
    (nwR[i]!)[0]! == t / 100 && (nwR[i]!)[1]! == t / 10 % 10 && (nwR[i]!)[2]! == t % 10).getD 0
meta def a3Mem (x : Array Nat) : Bool := a3R.any (· == x)
meta def cwM : Array Nat := (List.range 100).toArray.map fun t =>
  let i := t / 10
  let j := t % 10
  if i == j then 0 else
    let img := fun (l : Nat) => natArr (conjT 275 (invT 275 nrmC[j]!) nrmC[j]!
      (conjT 275 nrmC[i]! (invT 275 nrmC[i]!) aGens3[l]!))
    let l := ((List.range 4).find? fun l => !a3Mem (img l)).getD 0
    l + 4 * below a3P (img l)

end CertificateChecks.KernelMcLAS.M

public section

#kmulh CertificateChecks.KernelMcLAS.A3 275 9 CertificateChecks.KernelMcLAS.M.ids4M
  CertificateChecks.KernelMcLAS.M.agM CertificateChecks.KernelMcLAS.M.idM 200
#kmulh CertificateChecks.KernelMcLAS.NW 10 4 CertificateChecks.KernelMcLAS.M.ids2M10
  CertificateChecks.KernelMcLAS.M.nwM CertificateChecks.KernelMcLAS.M.id10M 800
#kfind CertificateChecks.KernelMcLAS.YIn3A CertificateChecks.KernelMcLAS.M.r3aR
  CertificateChecks.KernelMcLAS.M.yM
#kfind CertificateChecks.KernelMcLAS.YInA CertificateChecks.KernelMcLAS.M.a3R
  CertificateChecks.KernelMcLAS.M.yM
#kfind CertificateChecks.KernelMcLAS.NAInA CertificateChecks.KernelMcLAS.M.a3R
  CertificateChecks.KernelMcLAS.M.naM
#kfind CertificateChecks.KernelMcLAS.AIn3A CertificateChecks.KernelMcLAS.M.r3aR
  CertificateChecks.KernelMcLAS.M.a3R
#krows CertificateChecks.KernelMcLAS.BrA CertificateChecks.KernelMcLAS.M.brAM
#krows CertificateChecks.KernelMcLAS.Trip CertificateChecks.KernelMcLAS.M.tripM
#krows CertificateChecks.KernelMcLAS.CW CertificateChecks.KernelMcLAS.M.cwM
#kmisc_packarrs CertificateChecks.KernelMcLAS.NWI CertificateChecks.KernelMcLAS.M.nwInvM 4

end
