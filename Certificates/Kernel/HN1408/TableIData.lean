module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.HN1408.S2Data
meta import Certificates.Kernel.HN1408.RecGen
meta import Certificates.Kernel.HN1408.S2Data

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TIGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.RecGen CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def g1 : Array (Array Nat) := gensM nWords1
meta def g1I : Array (Array Nat) := g1.map invM
meta def i1 : Array (Array Nat) := idsOf g1
meta def r1 : Array (Array Nat) := recOf g1
meta def c1 : Array (Array Nat) := clOf g1
meta def g3 : Array (Array Nat) := gensM sWords3
meta def g3I : Array (Array Nat) := g3.map invM
meta def i3 : Array (Array Nat) := idsOf g3
meta def r3 : Array (Array Nat) := recOf g3
meta def c3 : Array (Array Nat) := clOf g3
meta def g4 : Array (Array Nat) := gensM nWords3
meta def g4I : Array (Array Nat) := g4.map invM
meta def i4 : Array (Array Nat) := idsOf g4
meta def r4 : Array (Array Nat) := recOf g4
meta def c4 : Array (Array Nat) := clOf g4

meta def labM (L : List CFSG.Sporadic.Th.Native.Table) : Array (Array Nat) := L.toArray.map natArr
meta def l1 : Array (Array Nat) := labM labs1
meta def l2 : Array (Array Nat) := labM labs2
meta def l3 : Array (Array Nat) := labM labs3
meta def l1J : Array (Array Nat) := l1.map (CFSG.Monster.B.Co2.Native.invCand 5)
meta def l2J : Array (Array Nat) := l2.map (CFSG.Monster.B.Co2.Native.invCand 8)
meta def l3J : Array (Array Nat) := l3.map (CFSG.Monster.B.Co2.Native.invCand 5)
meta def lS : Array (Array Nat) := labM CFSG.KD.HN1408.labsS2
meta def lSJ : Array (Array Nat) := lS.map (CFSG.Monster.B.Co2.Native.invCand 8)
meta def id5 : Array Nat := idTab 5
meta def id8 : Array Nat := idTab 8
meta def ids5 : Array (Array Nat) := Array.replicate 2 id5
meta def ids8 : Array (Array Nat) := Array.replicate 2 id8
meta def rl1 : Array (Array Nat) := recOfN 5 l1
meta def cl1 : Array (Array Nat) := clOfN 5 l1
meta def rl2 : Array (Array Nat) := recOfN 8 l2
meta def cl2 : Array (Array Nat) := clOfN 8 l2
meta def rl3 : Array (Array Nat) := recOfN 5 l3
meta def cl3 : Array (Array Nat) := clOfN 5 l3
meta def rlS : Array (Array Nat) := recOfN 8 lS
meta def clS : Array (Array Nat) := clOfN 8 lS

meta def blkM : Array (Array Nat) :=
  #[blkOfString blkStr1, blkOfString blkStr2, blkOfString blkStr3]

meta def ta : Array Nat := natArr (tabW wordA)
meta def tz : Array Nat := natArr (tabW wordZ)
meta def taz : Array Nat := natArr (tabW wordAZ)

meta def w1 : Array (Array Nat) := posOf r1 #[ta, tz]
meta def q1 : Array (Array Nat) :=
  let v := #[idM, ta, tz, taz]
  r1.map fun s => #[(v.findIdx? (· == comp 1408 s s)).getD 4]
meta def w3 : Array (Array Nat) := posOf r3 g4

end CFSG.KD.HN1408.TIGen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.TI1 1408 11 CFSG.KD.HN1408.TIGen.i1 CFSG.KD.HN1408.TIGen.g1
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.TI1Cl CFSG.KD.HN1408.TIGen.r1 CFSG.KD.HN1408.TIGen.c1
#kmisc_packarrs CFSG.KD.HN1408.TI1I CFSG.KD.HN1408.TIGen.g1I 11
#kmulh CFSG.KD.HN1408.TI3 1408 11 CFSG.KD.HN1408.TIGen.i3 CFSG.KD.HN1408.TIGen.g3
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.TI3Cl CFSG.KD.HN1408.TIGen.r3 CFSG.KD.HN1408.TIGen.c3
#kmisc_packarrs CFSG.KD.HN1408.TI3I CFSG.KD.HN1408.TIGen.g3I 11
#kmulh CFSG.KD.HN1408.TI4 1408 11 CFSG.KD.HN1408.TIGen.i4 CFSG.KD.HN1408.TIGen.g4
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.TI4Cl CFSG.KD.HN1408.TIGen.r4 CFSG.KD.HN1408.TIGen.c4
#kmisc_packarrs CFSG.KD.HN1408.TI4I CFSG.KD.HN1408.TIGen.g4I 11

#kmulh CFSG.KD.HN1408.TL1 5 4 CFSG.KD.HN1408.TIGen.ids5 CFSG.KD.HN1408.TIGen.l1
  CFSG.KD.HN1408.TIGen.id5 100000
#kfind CFSG.KD.HN1408.TL1Cl CFSG.KD.HN1408.TIGen.rl1 CFSG.KD.HN1408.TIGen.cl1
#kmisc_packarrs CFSG.KD.HN1408.TL1J CFSG.KD.HN1408.TIGen.l1J 4
#kmulh CFSG.KD.HN1408.TL2 8 4 CFSG.KD.HN1408.TIGen.ids8 CFSG.KD.HN1408.TIGen.l2
  CFSG.KD.HN1408.TIGen.id8 100000
#kfind CFSG.KD.HN1408.TL2Cl CFSG.KD.HN1408.TIGen.rl2 CFSG.KD.HN1408.TIGen.cl2
#kmisc_packarrs CFSG.KD.HN1408.TL2J CFSG.KD.HN1408.TIGen.l2J 4
#kmulh CFSG.KD.HN1408.TL3 5 4 CFSG.KD.HN1408.TIGen.ids5 CFSG.KD.HN1408.TIGen.l3
  CFSG.KD.HN1408.TIGen.id5 100000
#kfind CFSG.KD.HN1408.TL3Cl CFSG.KD.HN1408.TIGen.rl3 CFSG.KD.HN1408.TIGen.cl3
#kmisc_packarrs CFSG.KD.HN1408.TL3J CFSG.KD.HN1408.TIGen.l3J 4
#kmulh CFSG.KD.HN1408.TLS 8 4 CFSG.KD.HN1408.TIGen.ids8 CFSG.KD.HN1408.TIGen.lS
  CFSG.KD.HN1408.TIGen.id8 100000
#kfind CFSG.KD.HN1408.TLSCl CFSG.KD.HN1408.TIGen.rlS CFSG.KD.HN1408.TIGen.clS
#kmisc_packarrs CFSG.KD.HN1408.TLSJ CFSG.KD.HN1408.TIGen.lSJ 4

#ks_chars CFSG.KD.HN1408.TB1 CFSG.EvenSporadicStandard.HNRecog.blkStr1
#ks_chars CFSG.KD.HN1408.TB2 CFSG.EvenSporadicStandard.HNRecog.blkStr2
#ks_chars CFSG.KD.HN1408.TB3 CFSG.EvenSporadicStandard.HNRecog.blkStr3
#kmisc_packarrs CFSG.KD.HN1408.TB.F CFSG.KD.HN1408.TIGen.blkM 4

#kmisc_packarrs CFSG.KD.HN1408.TW1 CFSG.KD.HN1408.TIGen.w1 32
#kmisc_packarrs CFSG.KD.HN1408.TQ1 CFSG.KD.HN1408.TIGen.q1 8
#kmisc_packarrs CFSG.KD.HN1408.TW3 CFSG.KD.HN1408.TIGen.w3 32
