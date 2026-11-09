module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Data.Kernel.Spor.MulHPc
public import Certificates.Data.Kernel.Spor.PEnumC
meta import CFSG.Sporadic.SmallOddCore.J3DataInputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import Std.Data.HashSet
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3OutSyl

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 8 idM

meta def sM : Array (Array Nat) := (List.range 8).toArray.map fun k => natArr (j3CentTbl (k + 1))

meta def recM : Array (Array Nat) :=
  (CFSG.PSL3Four.Native.bfs (fun j t => CFSG.PSL3Four.Native.conjTab 6156 idM sM[j]! t) 8 idM 256).tabs

meta def wit (x : Array Nat) : Nat := Id.run do
  for j in [0:8] do
    let g := sM[j]!
    for p in [0:6156] do
      if x[g[p]!]! != g[x[p]!]! then
        return 6156 * j + p
  return 0

meta def witM : Array (Array Nat) := #[recM.map wit]

open CFSG.PSL3Four.Native in
meta def pcSeqX (els : Array (Array Nat)) (m : Nat) : Array (Array Nat) × Array (Array Nat) :=
  Id.run do
  let idm := idTab 6156
  let mut S : Array (Array Nat) := #[idm]
  let mut set : Std.HashSet (Array Nat) := Std.HashSet.emptyWithCapacity.insert idm
  let mut ys : Array (Array Nat) := #[]
  for _ in [0:m] do
    let mut found : Option (Array Nat) := none
    for y in els do
      if found.isNone && !set.contains y && set.contains (comp 6156 y y) then
        let yi := CFSG.Monster.B.Co2.Native.invCand 6156 y
        if ys.all (fun s => set.contains (comp 6156 (comp 6156 y s) yi)) then
          found := some y
    match found with
    | some y =>
      ys := ys.push y
      let S2 := S.map fun x => comp 6156 x y
      S := S ++ S2
      set := S2.foldl (fun h x => h.insert x) set
    | none => pure ()
  return (S, ys)

meta def pcPX : Array (Array Nat) × Array (Array Nat) := pcSeqX recM 8

meta def pcNX : Array (Array Nat) := pcPX.1

open CFSG.PSL3Four.Native in
meta def pcSqX : Array (Array Nat) := pcPX.2.map fun y => comp 6156 y y

open CFSG.PSL3Four.Native in
meta def pcCjX : Array (Array Nat) :=
  let ys := pcPX.2
  ((List.range ys.size).toArray.map fun r => (List.range ys.size).toArray.map fun s =>
    if s < r then
      comp 6156 (comp 6156 ys[r]! ys[s]!) (CFSG.Monster.B.Co2.Native.invCand 6156 ys[r]!)
    else idTab 6156).flatten

meta def pcPtX : Array (Array Nat) :=
  #[recM.foldl (init := (Array.replicate 6156 0, 0)) (fun (a, j) t => (a.set! t[1]! j, j + 1)) |>.1]

end CertificateChecks.KernelSpor.J3OutSyl

#kmulh CertificateChecks.KernelSpor.J3XS 6156 13 CertificateChecks.KernelSpor.J3OutSyl.idsM
  CertificateChecks.KernelSpor.J3OutSyl.sM CertificateChecks.KernelSpor.J3OutSyl.idM 256

#kmisc_packarrs CertificateChecks.KernelSpor.J3XW CertificateChecks.KernelSpor.J3OutSyl.witM 16

#kfind CertificateChecks.KernelSpor.J3XcP CertificateChecks.KernelSpor.J3OutSyl.recM
  CertificateChecks.KernelSpor.J3OutSyl.pcNX
#kfind CertificateChecks.KernelSpor.J3XcS CertificateChecks.KernelSpor.J3OutSyl.pcNX
  CertificateChecks.KernelSpor.J3OutSyl.recM
#kfind CertificateChecks.KernelSpor.J3XcA CertificateChecks.KernelSpor.J3OutSyl.pcNX
  CertificateChecks.KernelSpor.J3OutSyl.pcSqX
#kfind CertificateChecks.KernelSpor.J3XcB CertificateChecks.KernelSpor.J3OutSyl.pcNX
  CertificateChecks.KernelSpor.J3OutSyl.pcCjX
#kfind CertificateChecks.KernelSpor.J3XcU CertificateChecks.KernelSpor.J3OutSyl.pcNX
  CertificateChecks.KernelSpor.J3OutSyl.sM
#kmisc_packarrs CertificateChecks.KernelSpor.J3XcPP CertificateChecks.KernelSpor.J3OutSyl.pcPtX 13

namespace CertificateChecks.KernelSpor.J3OutSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSporSch

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

theorem base_ok : bAnd(szOK 6156 13, bAnd(cK (pidn 6156 13), bAnd(CFSG.KS.Prim.idK 6156 13 (mask 13),
    bAnd(cK (J3CentP 9),
    bAnd(allN 8 (fun j => bAnd(cK (J3XS.GI j), bAnd(Nat.beq (J3XS.GI j) (J3CentP (Nat.add j 1)),
      Nat.beq (J3XS.G j) (pidn 6156 13)))),
    bAnd(Nat.beq J3XS.cnt 256, penumHdK (pidn 6156 13) J3XS.cnt 256 J3XS.T J3XS.PL)))))) =
      true := by
  quickRfl

@[expose] noncomputable def ntX (r k : Nat) : Bool :=
  slK (Nat.shiftLeft 1 r) (pcTK 6156 13 (mask 13) J3XS.T J3XcP r) (Nat.mul 32 k) 32

@[expose] noncomputable def rlX (r c : Nat) : Bool :=
  pcRK 6156 13 (mask 13) 8 J3XS.T J3XcP J3XcA J3XcB r (Nat.mul 4 c) 4

@[expose] noncomputable def mbX : Bool :=
  pcMK 6156 13 (mask 13) 8 J3XS.cnt 1 J3XS.T J3XS.GI J3XcP J3XcS J3XcU J3XcPP

@[expose] noncomputable def pcFK8 (w m k cnt p : Nat) (T G CL : Nat → Nat) (c : Nat) : Bool :=
  strictB (r32 CL c) (fun q => bAnd(Nat.blt q cnt, Nat.beq (pg w m (T q) p)
    (pg w m (T (Nat.div c k)) (pg w m (G (Nat.mod c k)) p))))

theorem ntX_lo : allN 5 (fun r => ntX r 0) = true := by quickRfl

theorem ntX_5 : ntX 5 0 = true := by quickRfl

theorem ntX_60 : ntX 6 0 = true := by quickRfl

theorem ntX_61 : ntX 6 1 = true := by quickRfl

theorem ntX_70 : ntX 7 0 = true := by quickRfl

theorem ntX_71 : ntX 7 1 = true := by quickRfl

theorem ntX_72 : ntX 7 2 = true := by quickRfl

theorem ntX_73 : ntX 7 3 = true := by quickRfl

theorem rlX_lo : allN 5 (fun r => rlX r 0) = true := by quickRfl

theorem rlX_50 : rlX 5 0 = true := by quickRfl

theorem rlX_51 : rlX 5 1 = true := by quickRfl

theorem rlX_60 : rlX 6 0 = true := by quickRfl

theorem rlX_61 : rlX 6 1 = true := by quickRfl

theorem rlX_70 : rlX 7 0 = true := by quickRfl

theorem rlX_71 : rlX 7 1 = true := by quickRfl

theorem mbX_ok : mbX = true := by quickRfl

theorem clJ3X : slK (Nat.mul J3XS.cnt 8) (pcFK8 13 (mask 13) 8 J3XS.cnt 1 J3XS.T J3XS.GI J3XS.POS)
    0 2048 = true := by quickRfl

theorem peX : slK J3XS.cnt (CFSG.KS.PEnumC.penumPtC 8 8 J3XS.cnt J3XS.T J3XS.PL J3XS.POS J3XS.POS
    J3XS.SRT J3XS.SRI) 0 256 = true := by quickRfl

theorem sHF : slK J3XS.cnt (hsortPtKF 6156 13 (mask 13) J3XS.cnt J3XS.T J3XS.HS J3XS.HSI)
    0 J3XS.cnt = true := by quickRfl

theorem sHF_neg : hsortPtKF 6156 13 (mask 13) J3XS.cnt (fun _ => 0) J3XS.HS J3XS.HSI 0 = false := by
  decide +kernel

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] def xWord : List Int := [3, -5, 2, -3, 2, 1, 2, 1, -3, 5, 3, 1, 5]

@[expose] noncomputable def xW : Nat := wordK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI xWord

@[expose] noncomputable def commAll (p : Nat) : Bool :=
  (List.range 8).all fun j => Nat.beq (pc p (J3XS.GI j)) (pc (J3XS.GI j) p)

@[expose] noncomputable def cenRow (i : Nat) : Bool :=
  !commAll (J3XS.T i) || Nat.beq (J3XS.T i) (pidn 6156 13) || Nat.beq (J3XS.T i) (J3CentP 9)

@[expose] noncomputable def cWJ (i : Nat) : Nat := Nat.div (pg 16 (mask 16) (J3XW 0) i) 6156

@[expose] noncomputable def cWP (i : Nat) : Nat := Nat.mod (pg 16 (mask 16) (J3XW 0) i) 6156

@[expose] noncomputable def centerWK (t i : Nat) : Bool :=
  Nat.beq (J3XS.T i) (pidn 6156 13) || Nat.beq (J3XS.T i) t ||
    (Nat.blt (cWJ i) 8 &&
      !Nat.beq (pg 13 (mask 13) (J3XS.T i) (pg 13 (mask 13) (J3XS.GI (cWJ i)) (cWP i)))
        (pg 13 (mask 13) (J3XS.GI (cWJ i)) (pg 13 (mask 13) (J3XS.T i) (cWP i))) &&
      Nat.blt (cWP i) 6156)

theorem t0_mem : (List.range 256).any (fun i => Nat.beq (J3XS.T i) (J3CentP 9)) = true := by
  quickRfl

theorem center_wK : (List.range 256).all (centerWK (J3CentP 9)) = true := by
  quickRfl

theorem x_mem : (List.range 256).any (fun i => Nat.beq (J3XS.T i) xW) = true := by
  quickRfl

theorem x_four : Nat.beq (pc (pc xW xW) (pc xW xW)) (J3CentP 9) = true := by
  quickRfl

theorem x_word : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 xWord xW = true := by
  quickRfl

theorem neg_center : (!commAll xW) = true := by
  quickRfl

theorem neg_sq : (!Nat.beq (pc xW xW) (J3CentP 9)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J3OutSyl

end
