module

public import Certificates.Data.Kernel.GL33K
public import Certificates.Data.GL33.Check
public import Certificates.Kernel.GL33K.Data

public section

namespace CFSG.KD.GL33K

open CFSG.KC.GL33K

@[expose] noncomputable def mR : Nat → List (Nat × Nat × Nat)
  | 0 => m0R | 1 => m1R | 2 => m2R | 3 => m3R | 4 => m4R | 5 => m5R | 6 => m6R | 7 => m7R
  | 8 => m8R | 9 => m9R | 10 => m10R | 11 => m11R | 12 => m12R | _ => []

@[expose] noncomputable def mM : Nat → Nat
  | 0 => m0M | 1 => m1M | 2 => m2M | 3 => m3M | 4 => m4M | 5 => m5M | 6 => m6M | 7 => m7M
  | 8 => m8M | 9 => m9M | 10 => m10M | 11 => m11M | 12 => m12M | _ => 0

@[expose] noncomputable def oR : Nat → List (Nat × Nat × Nat)
  | 0 => o0R | 1 => o1R | 2 => o2R | 3 => o3R | 4 => o4R | 5 => o5R | 6 => o6R | 7 => o7R
  | 8 => o8R | 9 => o9R | 10 => o10R | 11 => o11R | 12 => o12R | _ => []

@[expose] noncomputable def cs : Nat → List (Nat × Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat))
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6 | 7 => c7
  | 8 => c8 | 9 => c9 | 10 => c10 | 11 => c11 | 12 => c12 | _ => []

@[expose] def ords : List Nat := [1, 3, 3, 9, 9, 9, 12, 24, 27, 39, 216, 216, 5616]

@[expose] noncomputable def gA (i : Nat) : Nat := (g.getD i (0, 0)).1

@[expose] noncomputable def gB (i : Nat) : Nat := (g.getD i (0, 0)).2

@[expose] noncomputable def nP (i : Nat) : (Nat × Nat) × (Nat × Nat) := ns.getD i ((0, 0), (0, 0))

@[expose] noncomputable def memC (i : Nat) : Bool := memK (gA i) (gB i) (ords.getD i 0) (mM i) (mR i)

@[expose] noncomputable def normC (i : Nat) : Bool :=
  let n := nP i
  mulK n.1.1 n.1.2 == oneK && mulK n.2.1 n.2.2 == oneK &&
    bitK (mM i) (conjK n.1.1 n.1.2 (gA i)) && bitK (mM i) (conjK n.1.1 n.1.2 (gB i)) &&
    bitK (mM i) (conjK n.2.1 n.2.2 (gA i)) && bitK (mM i) (conjK n.2.1 n.2.2 (gB i))

@[expose] noncomputable def orbC (i : Nat) : Bool :=
  let n := nP i
  orbK n.1.1 n.1.2 n.2.1 n.2.2 (mM i) ((cs i).map (·.1)) T (oR i) 0

@[expose] noncomputable def caseOne (i : Nat)
    (c : Nat × Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)) : Bool :=
  let x := c.1
  let j := c.2.1
  let h := c.2.2.1
  let h' := c.2.2.2.1
  decide (j < 13) && mulK h h' == oneK && bitK (mM j) (conjK h h' (gA i)) &&
    bitK (mM j) (conjK h h' (gB i)) && bitK (mM j) (conjK h h' x) &&
    evalK (gA i) (gB i) x c.2.2.2.2.1 == conjK h' h (gA j) &&
    evalK (gA i) (gB i) x c.2.2.2.2.2 == conjK h' h (gB j)

@[expose] noncomputable def caseC (i : Nat) : Bool := allK (caseOne i) (cs i)

@[expose] noncomputable def goodL : List Nat :=
  g.map (·.1) ++ g.map (·.2) ++ ns.map (·.1.1) ++ ns.map (·.1.2) ++ ns.map (·.2.1) ++
    ns.map (·.2.2) ++ (List.range 13).flatMap (fun i => (cs i).flatMap fun c =>
      [c.1, c.2.2.1, c.2.2.2.1]) ++
    [monG.1, monG.2, sylG.1, sylG.2, u13, m1, sl1i, sl2i] ++ monI ++ v4 ++
    v4O.map (·.1) ++ v4O.map (·.2)

@[expose] noncomputable def goodC : Bool := allK (fun c => CFSG.GL33.Native.detC c != 0) goodL

@[expose] noncomputable def tC : Bool :=
  setK TM T 0 && mulK (gA 12) sl1i == oneK && mulK (gB 12) sl2i == oneK &&
    allK (fun t => bitK TM (conjK (gA 12) sl1i t) && bitK TM (conjK sl1i (gA 12) t) &&
      bitK TM (conjK (gB 12) sl2i t) && bitK TM (conjK sl2i (gB 12) t)) T &&
    allK (fun r => bitK TM r.1) (mR 8)

@[expose] noncomputable def vecOK (j v : Nat) : Bool :=
  v != 0 && decide (v < 27) && CFSG.GL33.Native.vecC (gA j) v == v &&
    CFSG.GL33.Native.vecC (gB j) v == v

@[expose] noncomputable def covOK (v : Nat) : Bool :=
  v != 0 && decide (v < 27) && CFSG.GL33.Native.covC v (gA 10) == v &&
    CFSG.GL33.Native.covC v (gB 10) == v

@[expose] noncomputable def kindC : Bool :=
  kind == [0, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5] && gA 0 == oneK && gB 0 == oneK &&
    allK (fun j => vecOK j (vec.getD j 0)) [1, 2, 3, 4, 5, 7, 8, 11] &&
    covOK (vec.getD 10 0) &&
    CFSG.GL33.Native.detC (gA 12) == 1 && CFSG.GL33.Native.detC (gB 12) == 1

@[expose] noncomputable def sylC : Bool :=
  memK sylG.1 sylG.2 16 sylM sylR && !bitK sylM m1 &&
    (CFSG.GL33.Native.vecC sylG.1 9 == 9 || CFSG.GL33.Native.vecC sylG.1 9 == 18) &&
    (CFSG.GL33.Native.vecC sylG.2 9 == 9 || CFSG.GL33.Native.vecC sylG.2 9 == 18) &&
    m1 == 13286

@[expose] noncomputable def c13C : Bool :=
  memK u13 u13 13 uM uR && bitK (mM 9) u13 &&
    allK (fun c => powK c 13 != oneK || bitK uM c) (oneK :: (mR 9).map (·.1))

@[expose] noncomputable def a4C : Bool :=
  let v₁ := v4.getD 0 0
  let v₂ := v4.getD 1 0
  let v₃ := v4.getD 2 0
  v4.length == 3 && memK v₁ v₂ 4 vM vR && vM == maskK [oneK, v₁, v₂, v₃] &&
    bitK (mM 6) v₁ && bitK (mM 6) v₂ &&
    allK (fun c => mulK c c != oneK || bitK vM c) (oneK :: (mR 6).map (·.1)) &&
    memK monG.1 monG.2 48 monM monR &&
    allK CFSG.GL33.Native.monoC (oneK :: monR.map (·.1)) &&
    mulK monG.1 (monI.getD 0 0) == oneK && mulK monG.2 (monI.getD 1 0) == oneK &&
    bitK vM (conjK monG.1 (monI.getD 0 0) v₁) && bitK vM (conjK monG.1 (monI.getD 0 0) v₂) &&
    bitK vM (conjK monG.2 (monI.getD 1 0) v₁) && bitK vM (conjK monG.2 (monI.getD 1 0) v₂) &&
    v4O.length == 234 && keysK v₁ v₂ v₃ v4O 0

end CFSG.KD.GL33K

end
