module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.OmegaEight.AutChainOmP
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.PGrp
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Data
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Data
meta import Certificates.Kernel.Sporadic.RawGen

namespace CertificateChecks.KernelO8.E9KE

open CFSG.RankThree.PartTwo.Sec4.Item434O8pE9 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

meta def gQ : List (Array Nat) := (qGens o8pE9).toList

meta def gD : List (Array Nat) := (dGens o8pE9).toList

meta def keyOf (a : Array Nat) : Nat := [0, 1, 2].foldr (fun p acc => a[p]! + 360 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 360 9 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def kQ : List Nat := keyOrder gQ

meta def kD : List Nat := keyOrder gD

meta def hL : List Nat := (hArrs o8pE9).toList.map (CFSG.KS.RawGen.pack 9)

meta def cw : List Nat :=
  let qp := (CFSG.KC.BfsGen.search 360 9 (qGens o8pE9)).1
  let dp := (CFSG.KC.BfsGen.search 360 9 (dGens o8pE9)).1
  let hs := hArrs o8pE9
  (List.range hs.size).flatMap fun i => (List.range qp.size).map fun a =>
    let c := conjA 360 hs[i]! qp[a]!
    match dp.findIdx? (fun d => eqA 360 c d) with
    | some j => j + 1
    | none => 0

end CertificateChecks.KernelO8.E9KE

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelO8.E9Q CertificateChecks.KernelO8.E9KE.gQ 360 9
#lc_bfs CertificateChecks.KernelO8.E9D CertificateChecks.KernelO8.E9KE.gD 360 9
#kss_natlist CertificateChecks.KernelO8.E9Q.SKT CertificateChecks.KernelO8.E9KE.kQ
#kss_natlist CertificateChecks.KernelO8.E9D.SKT CertificateChecks.KernelO8.E9KE.kD
#kss_natlist CertificateChecks.KernelO8.E9H CertificateChecks.KernelO8.E9KE.hL
#kss_natlist CertificateChecks.KernelO8.E9CW CertificateChecks.KernelO8.E9KE.cw

namespace CertificateChecks.KernelO8.E9K

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.PGrp
open CertificateChecks.KernelO8

@[expose] noncomputable def E9Q.SK : List Nat := (List.range 243).map E9Q.SKT

@[expose] noncomputable def E9D.SK : List Nat := (List.range 81).map E9D.SKT

@[expose] def ps : List Nat := [0, 1, 2]

@[expose] noncomputable def pm (p q : Nat) : Nat := pcomp 360 9 (mask 9) p q

@[expose] noncomputable def keyC3 (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ acc => Nat.add (pg 9 (mask 9) p (pg 9 (mask 9) p (pg 9 (mask 9) p x)))
      (Nat.mul 360 acc)) ps

@[expose] def idKey : Nat := 259560

@[expose] noncomputable def oneK (a : Nat) : Bool := Nat.beq (keyK 360 9 ps (E9Q.T a)) idKey

@[expose] noncomputable def cubeK (a : Nat) : Bool := Nat.beq (keyC3 (E9Q.T a)) idKey

@[expose] noncomputable def cvK (i a : Nat) : Bool :=
  Nat.blt (nat_lit 0) (E9CW (Nat.add (Nat.mul 243 i) a))

@[expose] noncomputable def cwOK (t : Nat) : Bool :=
  strictB (E9CW t) fun j =>
    Nat.beq j 0 || (Nat.ble j 81 &&
      Nat.beq (pm (E9H (Nat.div t 243)) (E9Q.T (Nat.mod t 243)))
        (pm (E9D.T (Nat.sub j 1)) (E9H (Nat.div t 243))))

@[expose] noncomputable def pairK (a b : Nat) : Bool :=
  oneK a || oneK b || Nat.beq a b || !cubeK a || !cubeK b ||
    !Nat.beq (keyCK 360 9 ps (E9Q.T a) (E9Q.T b)) (keyCK 360 9 ps (E9Q.T b) (E9Q.T a)) ||
    Nat.beq (keyK 360 9 ps (E9Q.T b)) (keyCK 360 9 ps (E9Q.T a) (E9Q.T a)) ||
    (cvK 0 a && cvK 0 b) || (cvK 1 a && cvK 1 b) || (cvK 2 a && cvK 2 b) || (cvK 3 a && cvK 3 b)

end CertificateChecks.KernelO8.E9K

end
