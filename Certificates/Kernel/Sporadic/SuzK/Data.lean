module

public import Certificates.Data.CFSGNative.Suz.Certificate
public import Certificates.Data.Kernel.Spor.F3Lane
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Data.CFSGNative.Suz.Certificate

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzK.SeedA CFSG.Sporadic.Suz.Native.seedA
#ks_chars CertificateChecks.KernelSpor.SuzK.SeedB CFSG.Sporadic.Suz.Native.seedB

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.Sporadic.Suz.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

meta def orbM : WOrbit := orbitData ()

meta def tabM (t : Table) : Array Nat := t.map (·.toNat)

meta def alM : Array Nat := tabM orbM.alpha
meta def beM : Array Nat := tabM orbM.beta
meta def paM : Array Nat := tabM orbM.par
meta def lbM : Array Nat := tabM orbM.lab

meta def dpM : Array Nat := Id.run do
  let mut r : Array Nat := #[0]
  for k in [1:paM.size] do
    r := r.push (r[paM[k]!]! + 1)
  return r

meta def lettersM : Array Table := chainLetters orbM
meta def ltM : Array Nat := (lettersM.map tabM).flatten
meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2
meta def lv3M : Array Nat := levelLetters lettersM chainBase 3

meta def symOf (z : Int) : Nat := if z = 2 then 1 else if z = -2 then 2 else 0

meta def replPair (a b s : Nat) : List Nat → List Nat
  | x :: y :: t => if x == a && y == b then s :: replPair a b s t else x :: replPair a b s (y :: t)
  | l => l

meta def topPair (ws : List (List Nat)) : (Nat × Nat) × Nat := Id.run do
  let mut m : Std.HashMap (Nat × Nat) Nat := {}
  for w in ws do
    for (x, y) in w.zip w.tail do
      m := m.insert (x, y) (m.getD (x, y) 0 + 1)
  let mut best : (Nat × Nat) × Nat := ((0, 0), 0)
  for (p, c) in m.toList do
    if c > best.2 || (c == best.2 && (p.1 < best.1.1 || (p.1 == best.1.1 && p.2 < best.1.2))) then
      best := (p, c)
  return best

meta def repairM : List (Nat × Nat) × List (List Nat) := Id.run do
  let mut ws : List (List Nat) := (chainWords ()).toList.map fun w => w.map symOf
  let mut rules : List (Nat × Nat) := []
  for _ in [0:200] do
    let (p, c) := topPair ws
    if c < 3 then break
    let s := 3 + rules.length
    rules := rules ++ [p]
    ws := ws.map (replPair p.1 p.2 s)
  return (rules, ws)

meta def rulesM : List Nat := repairM.1.flatMap fun p => [p.1, p.2]

meta def cwM : List Nat := repairM.2.flatMap fun w => w.length :: w

meta def symTab (rt : Array (Array Nat)) (s x : Nat) : Nat :=
  if s == 0 then alM[x]! else if s == 1 then beM[x]! else if s == 2 then beM[beM[x]!]!
  else rt[s - 3]![x]!

meta def ruleTabs : Array (Array Nat) := Id.run do
  let mut rt : Array (Array Nat) := #[]
  for (a, b) in repairM.1 do
    let T := (Array.range alM.size).map fun x => symTab rt a (symTab rt b x)
    rt := rt.push T
  return rt

meta def rtM : Array Nat := ruleTabs.flatten

meta def laneOf (X : Array V) : Array Nat :=
  #[(List.range 64).foldl (fun a i => a + X[i]!.p * 2 ^ (64 * i)) 0,
    (List.range 64).foldl (fun a i => a + X[i]!.m * 2 ^ (64 * i)) 0]

meta def lanesM : Array Nat :=
  laneOf matA ++ laneOf matB ++ laneOf (mul 64 matB matB) ++ laneOf (idM 64) ++ laneOf formF ++
    laneOf formP ++ laneOf formPinv ++ laneOf diagD ++ laneOf (rootRows ())

end CertificateChecks.KernelSpor.SuzK

#krows CertificateChecks.KernelSpor.SuzK.AL CertificateChecks.KernelSpor.SuzK.alM
#krows CertificateChecks.KernelSpor.SuzK.BE CertificateChecks.KernelSpor.SuzK.beM
#krows CertificateChecks.KernelSpor.SuzK.PA CertificateChecks.KernelSpor.SuzK.paM
#krows CertificateChecks.KernelSpor.SuzK.LB CertificateChecks.KernelSpor.SuzK.lbM
#krows CertificateChecks.KernelSpor.SuzK.DP CertificateChecks.KernelSpor.SuzK.dpM
#krows CertificateChecks.KernelSpor.SuzK.LT CertificateChecks.KernelSpor.SuzK.ltM
#krows CertificateChecks.KernelSpor.SuzK.RT CertificateChecks.KernelSpor.SuzK.rtM
#knatlist CertificateChecks.KernelSpor.SuzK.RULES CertificateChecks.KernelSpor.SuzK.rulesM
#knatlist CertificateChecks.KernelSpor.SuzK.CW CertificateChecks.KernelSpor.SuzK.cwM
#krowsw CertificateChecks.KernelSpor.SuzK.LN 4096 CertificateChecks.KernelSpor.SuzK.lanesM

#ktbfs CertificateChecks.KernelSpor.SuzK.CT0 22880 0 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv0M
#ktbfs CertificateChecks.KernelSpor.SuzK.CT1 22880 1 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv1M
#ktbfs CertificateChecks.KernelSpor.SuzK.CT2 22880 2 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv2M
#ktbfs CertificateChecks.KernelSpor.SuzK.CT3 22880 3 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv3M
#ktbfs CertificateChecks.KernelSpor.SuzK.ST0 22880 2 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv1M
#ktbfs CertificateChecks.KernelSpor.SuzK.ST1 22880 11 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv1M
#ktbfs CertificateChecks.KernelSpor.SuzK.ST2 22880 20 CertificateChecks.KernelSpor.SuzK.lettersM
  CertificateChecks.KernelSpor.SuzK.lv1M

end
