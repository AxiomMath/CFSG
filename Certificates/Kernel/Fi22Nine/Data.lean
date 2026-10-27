module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Monster.B.Fischer.Fi22IndexNineInputs
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Assembly.Defs
public meta import CFSG.Monster.B.Fischer.Fi22Cover
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrder
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
public meta import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

namespace CertificateChecks.KernelSpor.Fi22NineM

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Certificates.Native

meta def wordsM : Array (Array Nat) :=
  #[fi22NineXWord, fi22NineYWord, fi22NineAWord, fi22NineH0Word, fi22NineH1Word, fi22NineGWord,
    fi22NinePWord].map fun w => (w.map (· - 1)).toArray

meta def maskM (s : List Nat) : Nat := s.foldl (fun acc p => acc ||| (1 <<< p)) 0

meta def orbitM (start : List Nat) (n : Nat) : Array (Array Nat) := Id.run do
  let gens := (fi22CentStrong 1).extract 0 9
  let tg := (fi22OuterStrong3510 4).extract 0 9
  let (sets, par, lab) := translateSearch gens start n
  let mut de : Array Nat := #[0]
  for k in [1:sets.size] do
    de := de.push (de[par[k]!]! + 1)
  let order := (Array.range sets.size).qsort fun i j => maskM sets[i]! < maskM sets[j]!
  let mut pos : Array Nat := Array.replicate sets.size 0
  for r in [0:order.size] do
    pos := pos.set! order[r]! r
  let mut pts : Array Nat := #[]
  let mut pr : Array Nat := #[]
  let mut gn : Array Nat := #[]
  let mut dp : Array Nat := #[]
  let mut tw : Array Nat := #[]
  for r in [0:order.size] do
    let k := order[r]!
    pts := pts ++ sets[k]!.toArray
    pr := pr.push pos[par[k]!]!
    gn := gn.push lab[k]!
    dp := dp.push de[k]!
    let w := (List.range 9).find? fun s => imgSorted tg[s]! sets[k]! != sets[k]!
    tw := tw.push (w.getD 0)
  return #[pts, pr, gn, dp, tw, #[pos[0]!]]

meta def orbitsM : Array (Array Nat) := orbitM fi22NineX0 45 ++ orbitM fi22NineX1 135

meta def zIdxM : Array (Array Nat) :=
  #[#[idx3 fi22TLevels (coords3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] (fi22ExtArr 22))]]

end CertificateChecks.KernelSpor.Fi22NineM

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22NineD.W CertificateChecks.KernelSpor.Fi22NineM.wordsM 4

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22NineD.O CertificateChecks.KernelSpor.Fi22NineM.orbitsM 12

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22NineD.Z CertificateChecks.KernelSpor.Fi22NineM.zIdxM 17

end
