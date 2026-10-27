module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24PairK
public import Certificates.Data.CFSGNative.Fi24Pair.Check

#kc_repo #kc_ktree CFSG.KD.Fi24PairK L13 "Certificates/Kernel/Sporadic/Fi24PairK/data/line13.bin" 65536 4 2424832 15886464734238263773
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L14 "Certificates/Kernel/Sporadic/Fi24PairK/data/line14.bin" 65536 4 2424832 4741927048051242643
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L15 "Certificates/Kernel/Sporadic/Fi24PairK/data/line15.bin" 65536 4 2424832 1317231666771233800
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L16 "Certificates/Kernel/Sporadic/Fi24PairK/data/line16.bin" 65536 4 2424832 15611378081685512723
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L17 "Certificates/Kernel/Sporadic/Fi24PairK/data/line17.bin" 65536 4 2424832 9964977837530073037
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L18 "Certificates/Kernel/Sporadic/Fi24PairK/data/line18.bin" 65536 4 2424832 8596715377222995414
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L19 "Certificates/Kernel/Sporadic/Fi24PairK/data/line19.bin" 65536 4 2424832 11196432571941109139
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L20 "Certificates/Kernel/Sporadic/Fi24PairK/data/line20.bin" 65536 4 2424832 1947477864222882764
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L21 "Certificates/Kernel/Sporadic/Fi24PairK/data/line21.bin" 65536 4 2424832 3444240987960590929
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L23 "Certificates/Kernel/Sporadic/Fi24PairK/data/line23.bin" 65536 4 2424832 15461485476369640223
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L27 "Certificates/Kernel/Sporadic/Fi24PairK/data/line27.bin" 65536 4 2424832 224993206430217607
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L28 "Certificates/Kernel/Sporadic/Fi24PairK/data/line28.bin" 65536 4 2424832 13843133815050907719
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L75 "Certificates/Kernel/Sporadic/Fi24PairK/data/line75.bin" 65536 4 2424832 3389171741105386994
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L76 "Certificates/Kernel/Sporadic/Fi24PairK/data/line76.bin" 65536 4 2424832 8902758530975231770
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L77 "Certificates/Kernel/Sporadic/Fi24PairK/data/line77.bin" 65536 4 2424832 5505429324333307867
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L78 "Certificates/Kernel/Sporadic/Fi24PairK/data/line78.bin" 65536 4 2424832 16070370991284230779
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L79 "Certificates/Kernel/Sporadic/Fi24PairK/data/line79.bin" 65536 4 2424832 16372305721961470867
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L80 "Certificates/Kernel/Sporadic/Fi24PairK/data/line80.bin" 65536 4 2424832 16301821846798521585
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L81 "Certificates/Kernel/Sporadic/Fi24PairK/data/line81.bin" 65536 4 2424832 6047503001391997548
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L82 "Certificates/Kernel/Sporadic/Fi24PairK/data/line82.bin" 65536 4 2424832 12516248349931933763
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L83 "Certificates/Kernel/Sporadic/Fi24PairK/data/line83.bin" 65536 4 2424832 15633547227775759121
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L84 "Certificates/Kernel/Sporadic/Fi24PairK/data/line84.bin" 65536 4 2424832 9454591081597532658
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L85 "Certificates/Kernel/Sporadic/Fi24PairK/data/line85.bin" 65536 4 2424832 4127340033189267186
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L86 "Certificates/Kernel/Sporadic/Fi24PairK/data/line86.bin" 65536 4 2424832 7319231728353534960
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L87 "Certificates/Kernel/Sporadic/Fi24PairK/data/line87.bin" 65536 4 2424832 9281157960925134897
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L88 "Certificates/Kernel/Sporadic/Fi24PairK/data/line88.bin" 65536 4 2424832 6685457648022541664
#kc_repo #kc_ktree CFSG.KD.Fi24PairK L89 "Certificates/Kernel/Sporadic/Fi24PairK/data/line89.bin" 65536 4 2424832 7907464065531771841

public section

namespace CFSG.KD.Fi24PairK

open CFSG.KC CFSG.KC.Fi24Net CFSG.KC.Fi24PairK CFSG.Sporadic.Fi24Pair.Native

@[expose] noncomputable def NVb (j l : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 23), L23 l, nIf(Nat.beq j (nat_lit 24), L17 l,
    nIf(Nat.beq j (nat_lit 25), L18 l, nIf(Nat.beq j (nat_lit 26), L19 l,
      nIf(Nat.beq j (nat_lit 27), L27 l, nIf(Nat.beq j (nat_lit 28), L28 l, nat_lit 0))))))

@[expose] noncomputable def NVa (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 23),
    nIf(Nat.blt j (nat_lit 18),
      nIf(Nat.beq j (nat_lit 13), L13 l, nIf(Nat.beq j (nat_lit 14), L14 l,
        nIf(Nat.beq j (nat_lit 15), L15 l, nIf(Nat.beq j (nat_lit 16), L16 l, L17 l)))),
      nIf(Nat.beq j (nat_lit 18), L18 l, nIf(Nat.beq j (nat_lit 19), L19 l,
        nIf(Nat.beq j (nat_lit 20), L20 l, nIf(Nat.beq j (nat_lit 21), L21 l, L15 l))))),
    NVb j l)

@[expose] noncomputable def NVc (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 80),
    nIf(Nat.beq j (nat_lit 75), L75 l, nIf(Nat.beq j (nat_lit 76), L76 l,
      nIf(Nat.beq j (nat_lit 77), L77 l, nIf(Nat.beq j (nat_lit 78), L78 l, L79 l)))),
    nIf(Nat.blt j (nat_lit 85),
      nIf(Nat.beq j (nat_lit 80), L80 l, nIf(Nat.beq j (nat_lit 81), L81 l,
        nIf(Nat.beq j (nat_lit 82), L82 l, nIf(Nat.beq j (nat_lit 83), L83 l, L84 l)))),
      nIf(Nat.beq j (nat_lit 85), L85 l, nIf(Nat.beq j (nat_lit 86), L86 l,
        nIf(Nat.beq j (nat_lit 87), L87 l, nIf(Nat.beq j (nat_lit 88), L88 l,
          nIf(Nat.beq j (nat_lit 89), L89 l, nat_lit 0)))))))

@[expose] noncomputable def net (j : Nat) : Bool :=
  orB (Nat.blt j (nat_lit 29)) (andB (Nat.ble (nat_lit 75) j) (Nat.blt j (nat_lit 90)))

@[expose] noncomputable def NV (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 13), CFSG.KD.Fi24Net.NW j l,
    nIf(Nat.blt j (nat_lit 29), NVa j l,
      nIf(andB (Nat.ble (nat_lit 75) j) (Nat.blt j (nat_lit 90)), NVc j l, nat_lit 0)))

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) i) l i

@[expose] def netL : List Nat :=
  [13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 27, 28, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
    87, 88, 89]

@[expose] def lineL : List Nat :=
  [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 75, 76, 77, 78, 79, 80, 81, 82,
    83, 84, 85, 86, 87, 88, 89]

@[expose] noncomputable def WL (j : Nat) : List Int := CFSG.KD.Fi24Net.nthW (pairWords ()).toList j

@[expose] noncomputable def fl (j : Nat) : List Int := flatF WL net (nat_lit 8) (Int.ofNat (Nat.add j 3))

@[expose] noncomputable def nck (g : Nat) : Bool := netOK (NV (nthN netL g))

@[expose] noncomputable def wck (g : Nat) : Bool :=
  (fun j => andB (dirOK net (WL j)) (wordOK NV (WL j) j (Nat.mod g (nat_lit 19))))
    (nthN lineL (Nat.div g (nat_lit 19)))

@[expose] def chOf (g : Nat) : ChainData :=
  if g < 4 then chainT else if g < 8 then chainA else if g < 12 then chainB else chainH

@[expose] def lvOf (g : Nat) : Nat := if g < 12 then g % 4 else g - 12

@[expose] def rd : List Nat := [4, 4, 10, 1, 3, 6, 8, 2, 4, 4, 8, 2, 17, 10, 10, 9, 6, 1]

@[expose] noncomputable def lvW (D : ChainData) (i : Nat) : List (List Int) :=
  (List.range' D.starts[i]! (D.starts[i + 1]! - D.starts[i]!)).map fun k => fl D.sel[k]!

@[expose] noncomputable def och (g : Nat) : Bool :=
  (fun D i => (fun ws => andB (ws.all (dirOK net))
      (orbW NV ws (nthN rd g) D.base[i]! (D.sizes.getD i 0))) (lvW D i))
    (chOf g) (lvOf g)

@[expose] noncomputable def fch (g : Nat) : Bool :=
  (fun D i => (lvW D i).all fun w => andB (dirOK net w) (fixW NV w (D.base.toList.take i)))
    (chOf g) (lvOf g)

end CFSG.KD.Fi24PairK

end
