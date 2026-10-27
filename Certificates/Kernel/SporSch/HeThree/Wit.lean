module

public import Certificates.Kernel.SporSch.HeThree.Data
public import Certificates.Data.Kernel.SporSch.NfGroup
public meta import Certificates.Kernel.SporSch.HeThree.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Certificates.Native CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open CertificateChecks.KernelSporSch.HeCn

meta def nfB (f : Nat → Nat) : Array Nat := decodeNF lv ((heBase.map f).toArray)

meta def nfA (g : Array Nat) : Array Nat := nfB fun b => g[b]!

meta def idN : Array Nat := nfB fun b => b

meta def mulN (a b : Array Nat) : Array Nat := nfB fun x => ev a (ev b x)

meta def powN (a : Array Nat) (k : Nat) : Array Nat := Id.run do
  let mut r := idN
  for _ in [0:k] do
    r := mulN a r
  return r

meta def ordN (a : Array Nat) : Nat := Id.run do
  let mut r := a
  for k in [1:200] do
    if r == idN then return k
    r := mulN a r
  return 0

meta def invN (a : Array Nat) : Array Nat := powN a (ordN a - 1)

meta def closNW (gens : Array (Array Nat)) (cap : Nat) : Array (Array Nat) × Array Nat := Id.run do
  let mut els : Array (Array Nat) := #[idN]
  let mut codes : Array Nat := #[0]
  let mut seen : Std.HashMap Nat Nat := {}
  seen := seen.insert (packNF idN) 0
  let mut i := 0
  while i < els.size && els.size ≤ cap do
    for t in [0:gens.size] do
      let h := mulN gens[t]! els[i]!
      if !(seen.contains (packNF h)) then
        seen := seen.insert (packNF h) els.size
        els := els.push h
        codes := codes.push (t + 1 + 4 * codes[i]!)
    i := i + 1
  return (els, codes)

meta def closN (gens : Array (Array Nat)) (cap : Nat) : Array (Array Nat) := (closNW gens cap).1

meta def wordsN (gens : Array (Array Nat)) (L : Array (Array Nat)) : List Nat :=
  let (els, codes) := closNW gens 100000
  let m : Std.HashMap Nat Nat := (List.range els.size).foldl
    (fun m i => m.insert (packNF els[i]!) codes[i]!) {}
  L.toList.map fun a => m.getD (packNF a) 0

meta def idxN (L : Array (Array Nat)) (a : Array Nat) : Nat := (L.findIdx? (· == a)).getD 0

meta def tabN (L : Array (Array Nat)) : List Nat :=
  (L.map packNF).toList ++
    (List.range (L.size * L.size)).map (fun q => idxN L (mulN L[q / L.size]! L[q % L.size]!)) ++
    (L.toList.map fun a => idxN L (invN a))

meta def yN (c : Nat) : Array Nat := nfA heS3CaseX[c]!

meta def cN (c : Nat) : Array (Array Nat) :=
  closN ((if c == 0 then heS3C0Gens else heS3C1Gens).map nfA) 100000

meta def eN (c : Nat) : Nat := if c == 0 then 280 else 56

meta def sylN (C : Array (Array Nat)) (p : Nat) : Array (Array Nat) := Id.run do
  if p != 2 then
    let w := (C.find? fun a => ordN a == p).getD idN
    return (List.range p).toArray.map (powN w)
  for a in C do
    if ordN a == 4 then
      for b in C do
        let S := closN #[a, b] 9
        if S.size == 8 then return S
  return #[]

meta def witN (C : Array (Array Nat)) (e : Nat) (s : Array Nat) : Array Nat :=
  (C.find? fun u => powN (mulN s (mulN u (mulN s (invN u)))) e != idN).getD idN

meta def sylDat (c p : Nat) : List Nat :=
  let C := cN c
  let S := sylN C p
  let fl := S.map fun s => if ordN s == p then 1 else 0
  let us := S.map fun s => if ordN s == p then witN C (eN c) s else idN
  tabN S ++ fl.toList ++ (us.map packNF).toList ++ (us.map fun u => packNF (invN u)).toList

meta def sw00M : List Nat := sylDat 0 2
meta def sw05M : List Nat := sylDat 0 5
meta def sw07M : List Nat := sylDat 0 7
meta def sw12M : List Nat := sylDat 1 2
meta def sw17M : List Nat := sylDat 1 7

meta def syl3N : Array (Array Nat) := Id.run do
  let C := cN 0
  let A := C.filter fun a => ordN a == 3
  for a in A do
    for b in A do
      let S := closN #[a, b] 28
      if S.size == 27 then return S
  return #[]

meta def sw03M : List Nat := tabN syl3N

meta def gwM : List Nat := (heS3QGens.map fun g => packNF (nfA g)).toList ++
  (heS3C0Gens.map fun g => packNF (nfA g)).toList

meta def qcwM : List Nat :=
  wordsN (heS3QGens.map nfA) (closN (heS3QGens.map nfA) 100)

meta def cwM : List Nat :=
  let C := cN 0
  let gs := heS3C0Gens.map nfA
  wordsN gs (sylN C 2) ++ wordsN gs (sylN C 5) ++ wordsN gs (sylN C 7) ++ wordsN gs syl3N

meta def qwM : List Nat :=
  let Q := closN (heS3QGens.map nfA) 100
  let ls := heS3Lines.map nfA
  let je := Q.map fun g => Id.run do
    for j in [0:ls.size] do
      for e in [1:3] do
        if powN ls[j]! e == g then return (j, e)
    return (0, 0)
  tabN Q ++ (je.map (·.1)).toList ++ (je.map (·.2)).toList

meta def lwM : List Nat :=
  let ls := heS3Lines.map nfA
  let hs := (List.range ls.size).toArray.map fun j => Id.run do
    let h := nfA heS3Trans[j]!
    let y := yN (heS3Rec.getD j 0)
    if mulN h y == mulN ls[j]! h then return h
    return invN h
  (ls.map packNF).toList ++ (hs.map packNF).toList ++ heS3Rec

end CertificateChecks.KernelSporSch.HeThree

set_option Elab.async false

#knatlist CertificateChecks.KernelSporSch.HeThree.QW CertificateChecks.KernelSporSch.HeThree.qwM
#knatlist CertificateChecks.KernelSporSch.HeThree.LW CertificateChecks.KernelSporSch.HeThree.lwM
#knatlist CertificateChecks.KernelSporSch.HeThree.GW CertificateChecks.KernelSporSch.HeThree.gwM
#knatlist CertificateChecks.KernelSporSch.HeThree.QCW CertificateChecks.KernelSporSch.HeThree.qcwM
#knatlist CertificateChecks.KernelSporSch.HeThree.CW CertificateChecks.KernelSporSch.HeThree.cwM
#knatlist CertificateChecks.KernelSporSch.HeThree.SW03 CertificateChecks.KernelSporSch.HeThree.sw03M

#ks_chars CertificateChecks.KernelSporSch.HeThree.QGX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.heS3QGensHex
#kb3_hexarrs CertificateChecks.KernelSporSch.HeThree.QGX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.heS3QGensHex 4 8330 14
#ks_chars CertificateChecks.KernelSporSch.HeThree.CGX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.heS3C0GensHex
#kb3_hexarrs CertificateChecks.KernelSporSch.HeThree.CGX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.heS3C0GensHex 4 8330 14
#knatlist CertificateChecks.KernelSporSch.HeThree.SW00 CertificateChecks.KernelSporSch.HeThree.sw00M
#knatlist CertificateChecks.KernelSporSch.HeThree.SW05 CertificateChecks.KernelSporSch.HeThree.sw05M
#knatlist CertificateChecks.KernelSporSch.HeThree.SW07 CertificateChecks.KernelSporSch.HeThree.sw07M
#knatlist CertificateChecks.KernelSporSch.HeThree.SW12 CertificateChecks.KernelSporSch.HeThree.sw12M
#knatlist CertificateChecks.KernelSporSch.HeThree.SW17 CertificateChecks.KernelSporSch.HeThree.sw17M

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeCn CFSG.Sporadic.HeldB

@[expose] noncomputable def evH (F x : Nat) : Nat := HeTc.nfp F x

@[expose] noncomputable def vldH (F : Nat) : Bool := nfValidK 5 HeC.LR F

@[expose] noncomputable def bsH : List Nat := [0, 1, 2, 3, 4]

@[expose] noncomputable def atL (l : List Nat) (k : Nat) : Nat := l.getD k 0

@[expose] noncomputable def QL (i : Nat) : Nat := atL QW i
@[expose] noncomputable def QT (q : Nat) : Nat := atL QW (Nat.add 27 q)
@[expose] noncomputable def QI (i : Nat) : Nat := atL QW (Nat.add 756 i)
@[expose] noncomputable def QJ (i : Nat) : Nat := atL QW (Nat.add 783 i)
@[expose] noncomputable def QE (i : Nat) : Nat := atL QW (Nat.add 810 i)
@[expose] noncomputable def LN (j : Nat) : Nat := atL LW j
@[expose] noncomputable def HN (j : Nat) : Nat := atL LW (Nat.add 13 j)
@[expose] noncomputable def RC (j : Nat) : Nat := atL LW (Nat.add 26 j)

@[expose] noncomputable def qOK : Bool := lgOK evH vldH bsH QL QT QI 27

@[expose] noncomputable def qLines : Bool :=
  allN 26 (fun i => strictB (Nat.add i 1) (fun k => bAnd(Nat.blt (QJ k) 13,
    bAnd(bAnd(Nat.blt 0 (QE k), Nat.blt (QE k) 3),
      eqOnL bsH (evH (QL k)) (powF (evH (LN (QJ k))) (QE k))))))

@[expose] noncomputable def qTrans : Bool :=
  allN 13 (fun j => bAnd(vldH (LN j), bAnd(vldH (HN j), bAnd(Nat.blt (RC j) 2,
    eqOnL bsH (fun x => evH (HN j) (pmR (RY (RC j)) x)) (fun x => evH (LN j) (evH (HN j) x))))))

@[expose] noncomputable def SW (c p : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat) SW17 SW12 (Nat.beq p 2))
    (Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) SW07 SW05 (Nat.beq p 5)) SW00 (Nat.beq p 2))
    (Nat.beq c 0)

@[expose] noncomputable def SL (c p m i : Nat) : Nat := atL (SW c p) i
@[expose] noncomputable def ST (c p m q : Nat) : Nat := atL (SW c p) (Nat.add m q)
@[expose] noncomputable def SI (c p m i : Nat) : Nat :=
  atL (SW c p) (Nat.add (Nat.add m (Nat.mul m m)) i)
@[expose] noncomputable def SF (c p m i : Nat) : Nat :=
  atL (SW c p) (Nat.add (Nat.add (Nat.mul 2 m) (Nat.mul m m)) i)
@[expose] noncomputable def SU (c p m i : Nat) : Nat :=
  atL (SW c p) (Nat.add (Nat.add (Nat.mul 3 m) (Nat.mul m m)) i)
@[expose] noncomputable def SV (c p m i : Nat) : Nat :=
  atL (SW c p) (Nat.add (Nat.add (Nat.mul 4 m) (Nat.mul m m)) i)

@[expose] noncomputable def sEl (c p m e i : Nat) : Bool :=
  bAnd(comL evH bsH (pmR (RY c)) (SL c p m i),
    Bool.rec (motive := fun _ => Bool)
      (bIf(ordPL bsH (evH (SL c p m i)) p, false, true))
      (bAnd(vldH (SU c p m i), bAnd(vldH (SV c p m i),
        bAnd(comL evH bsH (pmR (RY c)) (SU c p m i),
          wtL evH bsH (SL c p m i) (SU c p m i) (SV c p m i) e))))
      (Nat.beq (SF c p m i) 1))

@[expose] noncomputable def sOK (c p m e : Nat) : Bool :=
  bAnd(lgOK evH vldH bsH (SL c p m) (ST c p m) (SI c p m) m, allN m (sEl c p m e))

@[expose] noncomputable def QG (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (atL GW j) (Nat.blt j 2)

@[expose] noncomputable def CG (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (atL GW (Nat.add 2 j)) (Nat.blt j 3)

@[expose] noncomputable def gb (s : Nat) : Bool :=
  allN 170 (fun j => strictB (Nat.add (Nat.mul s 170) j) (fun x =>
    bAnd(allN 2 (fun i => Nat.beq (pm (QGX.F i) x) (evH (QG i) x)),
      allN 3 (fun i => Nat.beq (pm (CGX.F i) x) (evH (CG i) x)))))

@[expose] noncomputable def gOK : Bool :=
  bAnd(vldH 0, bAnd(eqOnL bsH (evH 0) (fun x => x),
  bAnd(allN 2 (fun i => bAnd(vldH (QG i), eqOnL bsH (evH (QG i)) (evH (QL (Nat.add i 1))))),
    allN 3 (fun i => bAnd(vldH (CG i), comL evH bsH (pmR (RY 0)) (CG i))))))

@[expose] noncomputable def qwOK : Bool := wordsOK evH bsH QG QL (fun i => atL QCW i) 27

@[expose] noncomputable def S3L (i : Nat) : Nat := atL SW03 i
@[expose] noncomputable def S3T (q : Nat) : Nat := atL SW03 (Nat.add 27 q)
@[expose] noncomputable def S3I (i : Nat) : Nat := atL SW03 (Nat.add 756 i)

@[expose] noncomputable def s3OK : Bool := lgOK evH vldH bsH S3L S3T S3I 27

@[expose] noncomputable def cwOK : Bool :=
  bAnd(wordsOK evH bsH CG (SL 0 2 8) (fun i => atL CW i) 8,
  bAnd(wordsOK evH bsH CG (SL 0 5 5) (fun i => atL CW (Nat.add 8 i)) 5,
  bAnd(wordsOK evH bsH CG (SL 0 7 7) (fun i => atL CW (Nat.add 13 i)) 7,
    wordsOK evH bsH CG S3L (fun i => atL CW (Nat.add 20 i)) 27)))

end CertificateChecks.KernelSporSch.HeThree

end
