module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.MixedCellChecks
meta import CFSG.Sporadic.SuzRecog.MixedCellChecks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzMc

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ModelGroupsCheck
  CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.MixedCellData
  CFSG.Sporadic.SuzRecog.MixedCell CFSG.Sporadic.SuzRecog.MixedCellCheck

meta def gM : Array (Array Nat) := mcGens

meta def giM : Array (Array Nat) := mcGens.map (invCand 1782)

meta def pad (n : Nat) (a : Array (Array Nat)) : Array (Array Nat) :=
  a ++ Array.replicate (n - a.size) (idA 1782)

meta def msOf (k : Nat) : Array (Array Nat) := ((boundW k).map mcWordA).toArray

meta def dsOf (k : Nat) : Array (Array Nat) := ((deltaW k).map mcWordA).toArray

meta def mM : Array (Array Nat) := pad 8 (msOf 0) ++ pad 8 (msOf 2)

meta def yM : Array (Array Nat) :=
  pad 8 ((msOf 0).map (conjInvA (cpA 0))) ++ pad 8 ((msOf 2).map (conjInvA (cpA 2)))

meta def yiM : Array (Array Nat) := yM.map (invCand 1782)

meta def dM : Array (Array Nat) := dsOf 0 ++ dsOf 2

meta def eM : Array (Array Nat) := #[eA 0, idA 1782, eA 2]

meta def eiM : Array (Array Nat) := eM.map (invCand 1782)

meta def wM : Array (Array Nat) := #[w1A, w2A]

meta def xM : Array (Array Nat) := #[mcWordA xW, invCand 1782 (mcWordA xW)]

meta def diffAt (e m : Array Nat) : Option Nat :=
  (List.range 1782).find? fun x => e[m[x]!]! != m[e[x]!]!

meta def kwOf (k : Nat) (e : Array Nat) : Nat :=
  let ms := msOf k
  let ds := dsOf k
  match (List.range ds.size).find? (fun j => eqA 1782 e ds[j]!) with
  | some j => 2 * j + 1
  | none =>
    ((List.range ms.size).filterMap fun j => (diffAt e ms[j]!).map fun x => 2 * (8 * x + j)).headD 0

meta def kwM : Array (Array Nat) :=
  (RootTwistCheck.kEls.map fun e => #[kwOf 0 e]) ++ (RootTwistCheck.kEls.map fun e => #[kwOf 2 e])

meta def vcL : Array Nat :=
  (Array.range 512).filter fun v => commA C1Model.v0Enum.tabs[v]! w1A

meta def vwOf (v : Nat) : Nat :=
  match diffAt C1Model.v0Enum.tabs[v]! w1A with
  | some x => 2 * x + 1
  | none => 2 * ((vcL.findIdx? (· == v)).getD 0)

meta def vwM : Array (Array Nat) := (Array.range 512).map fun v => #[vwOf v]

meta def vcM : Array (Array Nat) := vcL.map fun v => #[v]

meta def nM : Array (Array Nat) := #[#[vcL.size]]

end CertificateChecks.KernelSpor.SuzMc

#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcG CertificateChecks.KernelSpor.SuzMc.gM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcGI CertificateChecks.KernelSpor.SuzMc.giM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcM CertificateChecks.KernelSpor.SuzMc.mM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcY CertificateChecks.KernelSpor.SuzMc.yM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcYI CertificateChecks.KernelSpor.SuzMc.yiM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcD CertificateChecks.KernelSpor.SuzMc.dM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcE CertificateChecks.KernelSpor.SuzMc.eM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcEI CertificateChecks.KernelSpor.SuzMc.eiM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcW CertificateChecks.KernelSpor.SuzMc.wM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcX CertificateChecks.KernelSpor.SuzMc.xM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcKW CertificateChecks.KernelSpor.SuzMc.kwM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcVW CertificateChecks.KernelSpor.SuzMc.vwM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcVC CertificateChecks.KernelSpor.SuzMc.vcM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMcN CertificateChecks.KernelSpor.SuzMc.nM 32

end
