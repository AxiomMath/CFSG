module

public import Certificates.Kernel.SporSch.Tits.T614Q
public import Certificates.Kernel.Sporadic.Tits.LocS
public meta import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.T614

meta def keyM : List (Array Nat) :=
  let g1 : Array Nat := CFSG.Sporadic.Schreier.Tits.titsGenArrs[1]!
  CFSG.Quasithin.H13.Tits614.eArrs.map fun e => (Array.range 8).map fun x => g1[e[x]!]!

end CertificateChecks.KernelSporSch.T614

#kst_plist CertificateChecks.KernelSporSch.T614KE 11 CertificateChecks.KernelSporSch.T614.keyM

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAbel

@[expose] noncomputable def memK (k : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => bIf(Nat.beq h k, true, ih)) L

@[expose] noncomputable def pk8 (z0 z1 z2 z3 z4 z5 z6 z7 : Nat) : Nat :=
  Nat.lor z0 (Nat.lor (Nat.shiftLeft z1 11) (Nat.lor (Nat.shiftLeft z2 22)
    (Nat.lor (Nat.shiftLeft z3 33) (Nat.lor (Nat.shiftLeft z4 44) (Nat.lor (Nat.shiftLeft z5 55)
    (Nat.lor (Nat.shiftLeft z6 66) (Nat.shiftLeft z7 77)))))))

@[expose] noncomputable def keyOf (E : Nat) : Nat :=
  pk8 (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 0)) (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 1))
    (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 2)) (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 3))
    (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 4)) (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 5))
    (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 6)) (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E 7))

@[expose] noncomputable def aInvPt (i0 i1 i2 i3 i4 x : Nat) : Nat :=
  pg 11 (mask 11) i4 (pg 11 (mask 11) i3 (pg 11 (mask 11) i2 (pg 11 (mask 11) i1
    (pg 11 (mask 11) i0 x))))

@[expose] noncomputable def keyStep (t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI x : Nat) (fb : Bool)
    (k : Nat → Bool) : Bool :=
  strictB (uPt t0 t1 t2 t3 t4 (pg 11 (mask 11) H x)) (fun v =>
  strictB (aInvPt i0 i1 i2 i3 i4 (pg 11 (mask 11) HI v)) (fun z =>
    bIf(bAnd(Nat.blt z 1755,
      Nat.beq (pg 11 (mask 11) H (gpt 11 (mask 11) t0 t1 t2 t3 t4 z)) v), k z, fb)))

@[expose] noncomputable def keyTest (t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI : Nat) (fb : Bool) :
    Bool :=
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 0 fb (fun z0 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 1 fb (fun z1 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 2 fb (fun z2 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 3 fb (fun z3 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 4 fb (fun z4 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 5 fb (fun z5 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 6 fb (fun z6 =>
  keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI 7 fb (fun z7 =>
    memK (pk8 z0 z1 z2 z3 z4 z5 z6 z7) T614KE))))))))

@[expose] noncomputable def POUK (k t0 t1 t2 t3 t4 : Nat) : Bool :=
  strictB (trAt 1755 (1755 * 11) TitsS.LR TitsS.TRI 0 (Nat.shiftRight k 8)) (fun i0 =>
  strictB (trAt 1755 (1755 * 11) TitsS.LR TitsS.TRI 1 (Nat.land (Nat.shiftRight k 7) 1)) (fun i1 =>
  strictB (trAt 1755 (1755 * 11) TitsS.LR TitsS.TRI 2 (Nat.land (Nat.shiftRight k 3) 15)) (fun i2 =>
  strictB (trAt 1755 (1755 * 11) TitsS.LR TitsS.TRI 3 (Nat.land (Nat.shiftRight k 1) 3)) (fun i3 =>
  strictB (trAt 1755 (1755 * 11) TitsS.LR TitsS.TRI 4 (Nat.land k 1)) (fun i4 =>
  bIf(allN 3 (fun i => strictB (TitsH.S i) (fun H => strictB (TitsH.SI i) (fun HI =>
      keyTest t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI (T614EL.any (cmEq t0 t1 t2 t3 t4 H))))),
    strictB (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1) (fun U =>
      strictB (pinv U) (fun UI => kTests U UI)), true))))))

end CertificateChecks.KernelSporSch.T614

end
