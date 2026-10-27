module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TextGz

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.Monster.B.Co2.Native

@[expose] def decodeHex (s : String) (rows : List Nat) (w : Nat) : Array (Array Nat) :=
  Id.run do
    let b := s.toUTF8
    let mut o := 0
    let mut out : Array (Array Nat) := #[]
    for r in rows do
      out := out.push (Array.ofFn (n := r) fun i => hexAt b (w * (o + i.val)) w)
      o := o + r
    return out

#kc_repo #kc_text_gz MStHex "Certificates/Kernel/Misc/Perm/data/c2/MStHex.txt.gz" 2662 1169676050588173031

@[expose] def MStArr : Array (Array Nat) := decodeHex MStHex (List.replicate 22 1) 121

#kc_repo #kc_text_gz AMtHex "Certificates/Kernel/Misc/Perm/data/c2/AMtHex.txt.gz" 9196 15698376441497928284

@[expose] def AMtArr : Array (Array Nat) := decodeHex AMtHex (List.replicate 76 1) 121

#kc_repo #kc_text_gz TMtHex "Certificates/Kernel/Misc/Perm/data/c2/TMtHex.txt.gz" 1089242 5238543299227820831

@[expose] def TMtArr : Array (Array Nat) := decodeHex TMtHex (List.replicate 9002 1) 121

#kc_repo #kc_text_gz LVtHex "Certificates/Kernel/Misc/Perm/data/c2/LVtHex.txt.gz" 354213 1829563869946387573

@[expose] def LVtArr : Array (Array Nat) := decodeHex LVtHex [2300, 2300, 2300, 2300, 50600,
  1408, 2300, 1408, 1408, 28160, 567, 2300, 567, 567, 9072, 192, 2300, 192, 192, 2688, 30, 2300,
  30, 30, 240, 4, 2300, 4, 4, 8] 3

#kc_repo #kc_text_gz SVtHex "Certificates/Kernel/Misc/Perm/data/c2/SVtHex.txt.gz" 13800 1455065586815639752

@[expose] def SVtArr : Array (Array Nat) := decodeHex SVtHex [2300] 6

#kc_repo #kc_text_gz SPtHex "Certificates/Kernel/Misc/Perm/data/c2/SPtHex.txt.gz" 6900 11953594627714128365

@[expose] def SPtArr : Array (Array Nat) := decodeHex SPtHex [2300] 3

#kc_repo #kc_text_gz CStHex "Certificates/Kernel/Misc/Perm/data/c2/CStHex.txt.gz" 22710 13970035373536560825

@[expose] def CStArr : Array (Array Nat) :=
  decodeHex CStHex [125, 125, 3000, 3000, 600, 600, 60, 60] 3

#kc_repo #kc_text_gz DItHex "Certificates/Kernel/Misc/Perm/data/c2/DItHex.txt.gz" 7260 16610178282835101200

@[expose] def DItArr : Array (Array Nat) := decodeHex DItHex (List.replicate 60 1) 121

#kc_repo #kc_text_gz SEtHex "Certificates/Kernel/Misc/Perm/data/c2/SEtHex.txt.gz" 363000 11281758932551521564

@[expose] def SEtArr : Array (Array Nat) := decodeHex SEtHex (List.replicate 3000 1) 121

#kc_repo #kc_text_gz SEPtHex "Certificates/Kernel/Misc/Perm/data/c2/SEPtHex.txt.gz" 9000 3724780286763464797

@[expose] def SEPtArr : Array (Array Nat) := decodeHex SEPtHex [3000] 3

#kc_repo #kc_text_gz WTtHex "Certificates/Kernel/Misc/Perm/data/c2/WTtHex.txt.gz" 531 2712126649148963233

@[expose] def WTtArr : Array (Array Nat) := decodeHex WTtHex [125, 31, 2, 4, 6, 9] 3

@[expose] def spanLists : List (List Nat) :=
  [[2, 4, 6, 9, 10, 13, 14, 18, 23, 28, 41], [0, 1, 6, 9, 10, 11, 12, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 41], [0, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 17, 18],
    [0, 8, 12, 14, 15, 18, 41], [1, 6, 7, 9, 11, 15, 17, 18, 23, 41, 61],
    [3, 4, 5, 6, 7, 8, 9, 14, 17, 18, 23], [0, 4, 5, 9, 13, 14, 15, 17, 18, 23, 41, 61],
    [0, 2, 3, 4, 7, 10, 13, 14, 17, 41], [1, 2, 3, 6, 8, 9, 10, 11, 13, 18, 28, 61],
    [0, 2, 7, 9, 13, 14, 15, 61], [0, 1, 2, 3, 6, 7, 10, 11, 17, 28, 41],
    [0, 3, 5, 8, 12, 13, 14, 17, 61], [2, 4, 6, 8, 9, 11, 12, 17, 23, 41],
    [4, 6, 11, 12, 13, 14, 15, 17, 18, 23, 28, 41, 61], [1, 3, 8, 10, 11, 12, 13, 15, 17, 18, 23, 61],
    [1, 2, 4, 7, 8, 9, 10, 11, 18, 61], [0, 1, 3, 8, 9, 12, 13, 15, 28],
    [0, 2, 4, 7, 8, 9, 17, 23, 28, 61], [2, 3, 5, 6, 9, 10, 11, 12, 18],
    [3, 4, 8, 10, 11, 12, 13, 14, 15, 17, 18, 41], [0, 3, 6, 10, 11, 12, 13, 15, 17, 28]]

@[expose] def fixZ : List Nat := [0, 1, 2, 3, 97, 1194, 1393, 1822, 1903, 1995]

end CertificateChecks.KernelMisc.Co2K

end
