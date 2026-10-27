module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.RigidL2Tests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzRg

open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.RigidL2 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native

meta def findB (n : Nat) (p : Nat → Bool) : Nat := ((List.range n).find? p).getD 0

meta def uA : Array (Array Nat) := (List.range 16).toArray.map rigUTab

meta def tA : Array (Array Nat) := (List.range 8).toArray.map rigTTab

meta def ptA : Array (Array Nat) := rigProdTabs

meta def vA : Array (Array Nat) :=
  #[cWord rigX1, compA 1782 (rigSTab 0) (rigSTab 0), compA 1782 (rigSTab 1) (rigSTab 1),
    cWord ((rigGam.getD 0 []).getD 0 []), cWord ((rigGam.getD 0 []).getD 1 []),
    cWord ((rigGam.getD 1 []).getD 0 []), cWord ((rigGam.getD 1 []).getD 1 [])]

meta def mA : Array (Array Nat) := rigBfs.toArray.map fun u => matWord (rigExpand u)

meta def upL : List Nat := (List.range 16).map fun c =>
  findB 25920 fun i => matEnum.tabs[i]! == matWord (rigUWords.getD c [])

meta def nL : List Nat :=
  [(List.range 64).foldl (fun acc v => if rigBil v != 0 then acc ||| (1 <<< v) else acc) 0]

meta def bwA : Array (Array Nat) := (List.range 81).toArray.map fun s =>
  (List.range 320).toArray.map fun d =>
    let t := matEnum.tabs[320 * s + d]!
    if t[1]! == 1 then findB 60 fun k => rigAgree t mA[k]! else 0

meta def cellF (c j : Nat) : List Nat :=
  let R := rigRTab c j
  let w := w0Tab
  if !(rigComm R w) then [0, findB 1782 fun p => !(R[w[p]!]! == w[R[p]!]!)] else
    let m := findB 256 fun m => anyBelow 4 fun i => rigEqComp R rigProdTabs[m]! qElts[i]!
    let i := findB 4 fun i => rigEqComp R rigProdTabs[m]! qElts[i]!
    let x1 := vA[0]!
    let cx : List Nat := if c == 0 && j < 4 then [0, 0, 0, 0, 0, 0] else
      let ci := findB 8 fun i => !(rigComm R (rigTTab i))
      let T := rigTTab ci
      [ci, findB 1782 fun p => !(R[T[p]!]! == T[R[p]!]!)] ++
        (List.range 4).map fun v => findB 1782 fun z => !(R[x1[z]!]! == (qElts[v]!)[x1[R[z]!]!]!)
    let st := fun (s : Nat) =>
      let S := rigSTab s
      let S2 := vA[1 + s]!
      if !(eqA 1782 (compA 1782 R R) S2) then
        [1, findB 1782 fun p => !(R[R[p]!]! == S2[p]!), 0, 0, 0, 0]
      else
        let gi? := (List.range 2).find? fun gi => !(rigCommV vA[3 + 2 * s + gi]! R)
        match gi? with
        | some gi =>
          let G := vA[3 + 2 * s + gi]!
          [0, gi] ++ (List.range 4).map fun v =>
            findB 1782 fun z => !(G[R[z]!]! == (qElts[v]!)[R[G[z]!]!]!)
        | none => [2, findB 4 fun i => rigEqComp R S qElts[i]!, 0, 0, 0, 0]
    [1, m, i] ++ cx ++ st 0 ++ st 1

meta def cellRec (c j : Nat) : Nat :=
  (cellF c j).foldr (fun f acc => (acc <<< 11) ||| f) 0

meta def eA : Array (Array Nat) := (List.range 16).toArray.map fun c =>
  (List.range 128).toArray.map fun j => cellRec c j

meta def cqL : List Nat := (List.range 64).map fun p =>
  let A := rigTTab (p / 8)
  let B := rigTTab (p % 8)
  findB 4 fun q => allLt 1782 fun z => A[B[z]!]! == (qElts[q]!)[B[A[z]!]!]!

meta def sqL : List Nat := (List.range 2).map fun s =>
  findB 4 fun i => eqA 1782 vA[1 + s]! qElts[i]!

meta def gvL : List Nat := (List.range 4).map fun p =>
  let G := vA[3 + p]!
  let S := rigSTab (p / 2)
  findB 4 fun i => allLt 1782 fun z => G[S[z]!]! == (qElts[i]!)[S[G[z]!]!]!

meta def iwA : Array (Array Nat) :=
  let W := rigIrrWords.map fun u => matWord (rigExpand u)
  (List.range 64).toArray.map fun v =>
    let b := 1 :: W.map fun m => m[v]!
    (List.range 64).toArray.map fun u => findB 512 fun m => rigXor b m == u

end CertificateChecks.KernelSpor.SuzRg

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgU CertificateChecks.KernelSpor.SuzRg.uA 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgT CertificateChecks.KernelSpor.SuzRg.tA 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgPT CertificateChecks.KernelSpor.SuzRg.ptA 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgV CertificateChecks.KernelSpor.SuzRg.vA 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgM CertificateChecks.KernelSpor.SuzRg.mA 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgBW CertificateChecks.KernelSpor.SuzRg.bwA 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgE CertificateChecks.KernelSpor.SuzRg.eA 256
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRgIW CertificateChecks.KernelSpor.SuzRg.iwA 9

#knatlist CertificateChecks.KernelSpor.SuzRgUP CertificateChecks.KernelSpor.SuzRg.upL
#knatlist CertificateChecks.KernelSpor.SuzRgN CertificateChecks.KernelSpor.SuzRg.nL
#knatlist CertificateChecks.KernelSpor.SuzRgCQ CertificateChecks.KernelSpor.SuzRg.cqL
#knatlist CertificateChecks.KernelSpor.SuzRgSQ CertificateChecks.KernelSpor.SuzRg.sqL
#knatlist CertificateChecks.KernelSpor.SuzRgGV CertificateChecks.KernelSpor.SuzRg.gvL

end
