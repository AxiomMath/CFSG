module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Data.Kernel.Spor.Join
public import Certificates.Data.J3Cls
meta import Certificates.Data.J3Cls
meta import CFSG.Sporadic.Schreier.PairJ3CheckInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelJ3Ref.ClsT CFSG.SectionRank.QTK.Insp443.J3Cls.j3ClsHex

#kmisc_hexflat CertificateChecks.KernelJ3Ref.ClsT CFSG.SectionRank.QTK.Insp443.J3Cls.j3ClsHex
  4 513 13 120

namespace CertificateChecks.KernelJ3Ref

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def clsM : Array (Array Nat) := (List.range 10).toArray.map fun k => natArr (clsTbl k)

meta def clsIM : Array (Array Nat) := clsM.map (CFSG.Monster.B.Co2.Native.invCand 6156)

meta def allM : Array (Array Nat) :=
  #[natArr (j3CentTbl 9)] ++ clsM ++ (List.range 5).toArray.map fun k => natArr (j3CentTbl (10 + k))

meta def compM (p q : Array Nat) : Array Nat := q.map fun i => p[i]!

meta def invM (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate p.size 0
  for i in [0:p.size] do
    r := r.set! p[i]! i
  return r

meta def strongS : Array (Array Nat) := CFSG.Sporadic.Schreier.j3StrongArrs

meta def strongSI : Array (Array Nat) := strongS.map invM

meta def letterM (z : Int) : Array Nat :=
  if z > 0 then strongS[z.toNat - 1]! else strongSI[(-z).toNat - 1]!

meta def valM (w : List Int) : Array Nat :=
  w.foldr (fun z r => compM (letterM z) r) (Array.range 6156)

meta def levelM (i : Nat) : Array (Option (List Int)) := Id.run do
  let base := CFSG.Sporadic.Schreier.PairJ3.baseArr
  let gs := (List.range strongS.size).filter fun j =>
    (List.range i).all fun t =>
      let s := strongS[j]!
      s[base[t]!]! == base[t]!
  let letters : List Int := gs.map (fun j => ((j + 1 : Nat) : Int)) ++
    gs.map (fun j => -((j + 1 : Nat) : Int))
  let b := base[i]!
  let mut words : Array (Option (List Int)) := Array.replicate 6156 none
  words := words.set! b (some [])
  let mut queue : Array Nat := #[b]
  let mut h := 0
  while h < queue.size do
    let y := queue[h]!
    h := h + 1
    let wy := (words[y]!).getD []
    for z in letters do
      let yy := (letterM z)[y]!
      if (words[yy]!).isNone then
        words := words.set! yy (some (z :: wy))
        queue := queue.push yy
  return words

meta def levelsM : Array (Array (Option (List Int))) := (List.range 4).toArray.map levelM

meta def siftWordM (x : Array Nat) : List Int := Id.run do
  let base := CFSG.Sporadic.Schreier.PairJ3.baseArr
  let mut x := x
  let mut word : List Int := []
  for i in [0:4] do
    let lv := levelsM[i]!
    let y := x[base[i]!]!
    match lv[y]! with
    | none => return []
    | some w =>
      word := word ++ w
      x := compM (invM (valM w)) x
  return word

meta def wordsM : Array (List Int) := allM.map siftWordM

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 6156

meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM

meta def recOfM (gens : Array (Array Nat)) : Array (Array Nat) :=
  (CFSG.PSL3Four.Native.bfs (fun j t => CFSG.PSL3Four.Native.conjTab 6156 idM gens[j]! t)
    gens.size idM 3000).tabs

meta def hvOfM (rec : Array (Array Nat)) : Array (Array Nat) :=
  rec.map fun t => #[(hkey 6156 (t.map UInt32.ofNat)).toNat]

meta def indexM (rec : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:rec.size] do
    m := m.insert rec[i]! i
  return m

meta def clOfM (rec gens : Array (Array Nat)) : Array Nat := Id.run do
  let idx := indexM rec
  let letters := gens ++ gens.map invM
  let mut out : Array Nat := #[]
  for x in rec do
    for g in letters do
      out := out.push (idx.getD (compM x g) rec.size)
  return out

meta def conjOfM (rec : Array (Array Nat)) (c : Array Nat) : Array Nat :=
  let idx := indexM rec
  let ci := invM c
  rec.map fun x => idx.getD (compM (compM c x) ci) rec.size

meta def posOfM (rec qs : Array (Array Nat)) : Array Nat :=
  let idx := indexM rec
  qs.map fun q => idx.getD q rec.size

end CertificateChecks.KernelJ3Ref

#kmisc_packarrs CertificateChecks.KernelJ3Ref.J3ClsP CertificateChecks.KernelJ3Ref.clsM 13

#kmisc_packarrs CertificateChecks.KernelJ3Ref.J3ClsI CertificateChecks.KernelJ3Ref.clsIM 13

#kc_intwords CertificateChecks.KernelJ3Ref.W CertificateChecks.KernelJ3Ref.wordsM

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Join CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] def bsJ : List Nat := [0, 1, 3, 2]

theorem cls_join : joinK 12 (13 * 513) ClsT.F J3ClsP 10 = true := by
  quickRfl

@[expose] noncomputable def clsPerm (k : Nat) : Bool :=
  invEqK 6156 13 (mask 13) (6156 * 13) (J3ClsP k) (J3ClsI k)

theorem cls_perms0 : allBlk 0 clsPerm 5 = true := by
  quickRfl

theorem cls_perms1 : allBlk 5 clsPerm 5 = true := by
  quickRfl

@[expose] noncomputable def tbP (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), J3CentP (nat_lit 9),
    nIf(Nat.blt i (nat_lit 11), J3ClsP (Nat.sub i (nat_lit 1)), J3CentP (Nat.sub i (nat_lit 1))))

@[expose] noncomputable def ebL : List Nat := [J3CentP 9, J3ClsP 0, J3ClsP 1, J3ClsP 2]

@[expose] noncomputable def wordOK (i : Nat) : Bool :=
  wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (W.getD i []) (tbP i)

theorem words0 : allBlk 0 wordOK 4 = true := by
  quickRfl

theorem words1 : allBlk 4 wordOK 4 = true := by
  quickRfl

theorem words2 : allBlk 8 wordOK 4 = true := by
  quickRfl

theorem words3 : allBlk 12 wordOK 4 = true := by
  quickRfl

theorem word_neg : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (W.getD 1 []) (tbP 2) =
    false := by
  decide +kernel

end CertificateChecks.KernelJ3Ref

end
