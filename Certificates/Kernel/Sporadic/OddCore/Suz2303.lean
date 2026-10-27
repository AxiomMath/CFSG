module

public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Kernel.Sporadic.OddCore.SuzInvOdd
public import Certificates.Kernel.Sporadic.OddCore.PEnumFamGCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzOddCore.OddCoreCheckInputs
meta import CFSG.Sporadic.SuzOddCore.OddCoreCheckInputs
import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native

@[expose] def recEnt : List Nat := [0, 0, 0, 1, 1, 2, 2, 2, 3, 3, 3]

@[expose] def recR : List Nat := [0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 2]

@[expose] def recP : List Nat := [3, 5, 7, 3, 5, 3, 5, 11, 3, 5, 7]

@[expose] def recO : List Nat := [9, 5, 7, 81, 5, 27, 5, 11, 27, 25, 7]

@[expose] def recG : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1]

@[expose] def recL : List Nat := [4, 1, 1, 22, 1, 13, 1, 1, 13, 6, 1]

@[expose] def recS : List Nat := [82, 88, 90, 44, 69, 20, 36, 38, 36, 52, 60]

@[expose] def innS : List Nat := [32, 18, 12, 20]

meta def recTabM : Array (Nat × Nat × Nat × Nat) :=
  #[(0, 0, 3, 9), (0, 1, 5, 5), (0, 2, 7, 7), (1, 0, 3, 81), (1, 1, 5, 5), (2, 0, 3, 27),
    (2, 1, 5, 5), (2, 2, 11, 11), (3, 0, 3, 27), (3, 1, 5, 25), (3, 2, 7, 7)]

meta def recGensM : Array (Array (Array Nat)) :=
  recTabM.map fun e => invOddGenArrs e.1 e.2.1

meta def recCapsM : Array Nat := recTabM.map fun e => e.2.2.2

meta def oddWitM : Array (Array Nat) :=
  (recTabM.map fun e =>
    let i := e.1
    let r := e.2.1
    let p := e.2.2.1
    let lines := invOddLineArrs i r
    (oddEnum i r).tabs.map fun t =>
      #[((List.range p).findSome? fun j => ((List.range lines.size).find? fun l =>
        eqA 1782 (powA 1782 t j) lines[l]!).map fun l => 256 * j + l).getD 0]).flatten

meta def oddWitOffM : Array (Array Nat) :=
  (List.range 11).toArray.map fun ρ =>
    #[((List.range ρ).map fun ρ' => (recTabM[ρ']!).2.2.2).sum]

end CertificateChecks.KernelSpor.OddCore

#kpenumgens CertificateChecks.KernelSpor.OEF 1782 11 CertificateChecks.KernelSpor.OddCore.recGensM
  CertificateChecks.KernelSpor.OddCore.recCapsM

#kmisc_packarrs CertificateChecks.KernelSpor.OW CertificateChecks.KernelSpor.OddCore.oddWitM 32

#kmisc_packarrs CertificateChecks.KernelSpor.OWO CertificateChecks.KernelSpor.OddCore.oddWitOffM 32

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.Mathieu CFSG.KC.Misc.HexAt

@[expose] noncomputable def lgetA {α : Type} (d : α) (L : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) L

@[expose] noncomputable def genP (ρ k : Nat) : Nat := runP (nget recEnt ρ) (Nat.add (nget recS ρ) k)

@[expose] noncomputable def lineP (ρ l : Nat) : Nat :=
  runP (nget recEnt ρ) (Nat.add (Nat.add (nget recS ρ) (nget recG ρ)) l)

@[expose] noncomputable def innP (i h : Nat) : Nat := runP i (Nat.sub (Nat.add (nget innS i) h) 1)

@[expose] noncomputable def recGensK (ρ : Nat) : Bool :=
  bAnd(Nat.beq (OEF.K ρ) (nget recG ρ), bAnd(Nat.beq (OEF.C ρ) (nget recO ρ),
  allN (nget recG ρ) (fun k => strictB (genP ρ k) (fun G =>
    bAnd(Nat.beq (OEF.G (Nat.add (OEF.GO ρ) k)) G,
    bAnd(invEqK 1782 11 (mask 11) (1782 * 11) G (pinvS 1782 11 (mask 11) G),
    bAnd(msift G, commK 1782 11 (mask 11) (1782 * 11) G (SuzTP (nget recEnt ρ)))))))))

@[expose] noncomputable def recEnumK (ρ : Nat) : Bool :=
  bAnd(penumHdK (pidn 1782 11) (OEF.C ρ) (nget recO ρ) (offF OEF.T (OEF.TO ρ))
      (offF OEF.PL (OEF.PLO ρ)),
    penumSlK 1782 11 (mask 11) (1782 * 11) false (offF OEF.G (OEF.GO ρ)) (offF OEF.G (OEF.GO ρ))
      (OEF.K ρ) (OEF.C ρ) (offF OEF.T (OEF.TO ρ)) (offF OEF.PL (OEF.PLO ρ))
      (offF OEF.POS (OEF.POSO ρ)) (offF OEF.SRT (OEF.SRTO ρ)) (offF OEF.SRI (OEF.SRIO ρ)) 0
      (OEF.C ρ))

@[expose] noncomputable def elemPt (ρ k : Nat) : Bool :=
  strictB (offF OEF.T (OEF.TO ρ) k) (fun t =>
    bIf(Nat.beq (ppow 1782 11 (mask 11) (pidn 1782 11) t (nget recP ρ)) (pidn 1782 11),
      bIf(Nat.beq t (pidn 1782 11), true,
        strictB (OW (Nat.add (OWO ρ) k)) (fun wk =>
          strictB (Nat.shiftRight wk 8) (fun j => strictB (Nat.land wk 255) (fun l =>
            bAnd(Nat.blt j (nget recP ρ), bAnd(Nat.blt l (nget recL ρ),
              Nat.beq (ppow 1782 11 (mask 11) (pidn 1782 11) t j) (lineP ρ l))))))),
      true))

@[expose] noncomputable def oddWordK (ρ l : Nat) : List Nat :=
  lget2 (lgetA [] (lgetA [] invOddCoreWords (nget recEnt ρ)) (nget recR ρ)) l

@[expose] noncomputable def oddOrdK (ρ l : Nat) : Nat :=
  nget (lgetA [] (lgetA [] invOddCoreProductOrders (nget recEnt ρ)) (nget recR ρ)) l

@[expose] noncomputable def linePt (ρ l : Nat) : Bool :=
  strictB (lineP ρ l) (fun X =>
    strictB (wordTabK 1782 11 (mask 11) (pidn 1782 11) (innP (nget recEnt ρ)) (oddWordK ρ l))
      (fun G => strictB (pinvS 1782 11 (mask 11) G) (fun GI =>
      strictB (ppow 1782 11 (mask 11) (pidn 1782 11)
        (pcomp 1782 11 (mask 11) X (pcomp 1782 11 (mask 11) G (pcomp 1782 11 (mask 11) X GI)))
        (Nat.div (oddOrdK ρ l) 2)) (fun W =>
      bAnd(invEqK 1782 11 (mask 11) (1782 * 11) X (pinvS 1782 11 (mask 11) X),
      bAnd(invEqK 1782 11 (mask 11) (1782 * 11) G GI,
      bAnd(canonK 1782 11 (mask 11) (1782 * 11) GI,
      bAnd(canonK 1782 11 (mask 11) (1782 * 11) W,
      bAnd(Nat.beq (pcomp 1782 11 (mask 11) W W) (pidn 1782 11),
        bIf(Nat.beq W (pidn 1782 11), false, true))))))))))

theorem g0 : recGensK 0 = true := by quickRfl
theorem g1 : recGensK 1 = true := by quickRfl
theorem g2 : recGensK 2 = true := by quickRfl
theorem g3 : recGensK 3 = true := by quickRfl
theorem g4 : recGensK 4 = true := by quickRfl
theorem g5 : recGensK 5 = true := by quickRfl
theorem g6 : recGensK 6 = true := by quickRfl
theorem g7 : recGensK 7 = true := by quickRfl
theorem g8 : recGensK 8 = true := by quickRfl
theorem g9 : recGensK 9 = true := by quickRfl
theorem g10 : recGensK 10 = true := by quickRfl

theorem n0 : recEnumK 0 = true := by quickRfl
theorem n1 : recEnumK 1 = true := by quickRfl
theorem n2 : recEnumK 2 = true := by quickRfl
theorem n3 : recEnumK 3 = true := by quickRfl
theorem n4 : recEnumK 4 = true := by quickRfl
theorem n5 : recEnumK 5 = true := by quickRfl
theorem n6 : recEnumK 6 = true := by quickRfl
theorem n7 : recEnumK 7 = true := by quickRfl
theorem n8 : recEnumK 8 = true := by quickRfl
theorem n9 : recEnumK 9 = true := by quickRfl
theorem n10 : recEnumK 10 = true := by quickRfl

theorem e0 : allBlk 0 (elemPt 0) 9 = true := by quickRfl
theorem e1 : allBlk 0 (elemPt 1) 5 = true := by quickRfl
theorem e2 : allBlk 0 (elemPt 2) 7 = true := by quickRfl
theorem e3a : allBlk 0 (elemPt 3) 14 = true := by quickRfl
theorem e3b : allBlk 14 (elemPt 3) 14 = true := by quickRfl
theorem e3c : allBlk 28 (elemPt 3) 14 = true := by quickRfl
theorem e3d : allBlk 42 (elemPt 3) 14 = true := by quickRfl
theorem e3e : allBlk 56 (elemPt 3) 14 = true := by quickRfl
theorem e3f : allBlk 70 (elemPt 3) 11 = true := by quickRfl
theorem e4 : allBlk 0 (elemPt 4) 5 = true := by quickRfl
theorem e5a : allBlk 0 (elemPt 5) 14 = true := by quickRfl
theorem e5b : allBlk 14 (elemPt 5) 13 = true := by quickRfl
theorem e6 : allBlk 0 (elemPt 6) 5 = true := by quickRfl
theorem e7 : allBlk 0 (elemPt 7) 11 = true := by quickRfl
theorem e8a : allBlk 0 (elemPt 8) 14 = true := by quickRfl
theorem e8b : allBlk 14 (elemPt 8) 13 = true := by quickRfl
theorem e9a : allBlk 0 (elemPt 9) 13 = true := by quickRfl
theorem e9b : allBlk 13 (elemPt 9) 12 = true := by quickRfl
theorem e10 : allBlk 0 (elemPt 10) 7 = true := by quickRfl

theorem l0 : allBlk 0 (linePt 0) 4 = true := by quickRfl
theorem l1 : allBlk 0 (linePt 1) 1 = true := by quickRfl
theorem l2 : allBlk 0 (linePt 2) 1 = true := by quickRfl
theorem l3a : allBlk 0 (linePt 3) 6 = true := by quickRfl
theorem l3b : allBlk 6 (linePt 3) 6 = true := by quickRfl
theorem l3c : allBlk 12 (linePt 3) 6 = true := by quickRfl
theorem l3d : allBlk 18 (linePt 3) 4 = true := by quickRfl
theorem l4 : allBlk 0 (linePt 4) 1 = true := by quickRfl
theorem l5a : allBlk 0 (linePt 5) 5 = true := by quickRfl
theorem l5b : allBlk 5 (linePt 5) 5 = true := by quickRfl
theorem l5c : allBlk 10 (linePt 5) 3 = true := by quickRfl
theorem l6 : allBlk 0 (linePt 6) 1 = true := by quickRfl
theorem l7 : allBlk 0 (linePt 7) 1 = true := by quickRfl
theorem l8a : allBlk 0 (linePt 8) 5 = true := by quickRfl
theorem l8b : allBlk 5 (linePt 8) 5 = true := by quickRfl
theorem l8c : allBlk 10 (linePt 8) 3 = true := by quickRfl
theorem l9 : allBlk 0 (linePt 9) 6 = true := by quickRfl
theorem l10 : allBlk 0 (linePt 10) 1 = true := by quickRfl

end CertificateChecks.KernelSpor.OddCore

end
