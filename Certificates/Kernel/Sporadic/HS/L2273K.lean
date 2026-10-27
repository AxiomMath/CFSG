module

public import Certificates.Kernel.Sporadic.HS.L2273D
public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Data.Kernel.Spor.HSL2273
public import Certificates.Data.Kernel.Spor.Mathieu
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.HSCosetInputs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KS.HSL
open CFSG.KD.LQT.C4126 CFSG.KS.Mathieu CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def c1L (j : Nat) : Nat := HC.F (Nat.add j (nat_lit 6))

@[expose] noncomputable def c2L (j : Nat) : Nat := HC.F (Nat.add j (nat_lit 13))

@[expose] noncomputable def wk (S : Nat → Nat) (wd : List Nat) : Nat :=
  wordTabK 3850 12 (mask 12) idn S wd

@[expose] noncomputable def oT (l : Nat) : Nat → Nat := sel7 l O0.T O1.T O2.T O3.T O4.T O5.T O6.T
@[expose] noncomputable def oPL (l : Nat) : Nat → Nat :=
  sel7 l O0.PL O1.PL O2.PL O3.PL O4.PL O5.PL O6.PL
@[expose] noncomputable def oPOS (l : Nat) : Nat → Nat :=
  sel7 l O0.POS O1.POS O2.POS O3.POS O4.POS O5.POS O6.POS
@[expose] noncomputable def oSRT (l : Nat) : Nat → Nat :=
  sel7 l O0.SRT O1.SRT O2.SRT O3.SRT O4.SRT O5.SRT O6.SRT
@[expose] noncomputable def oSRI (l : Nat) : Nat → Nat :=
  sel7 l O0.SRI O1.SRI O2.SRI O3.SRI O4.SRI O5.SRI O6.SRI
@[expose] noncomputable def oG (l : Nat) : Nat → Nat := sel7 l O0.G O1.G O2.G O3.G O4.G O5.G O6.G
@[expose] noncomputable def oGI (l : Nat) : Nat → Nat :=
  sel7 l O0.GI O1.GI O2.GI O3.GI O4.GI O5.GI O6.GI
@[expose] noncomputable def oC (l : Nat) : Nat :=
  sel7 l (fun _ => O0.cnt) (fun _ => O1.cnt) (fun _ => O2.cnt) (fun _ => O3.cnt)
    (fun _ => O4.cnt) (fun _ => O5.cnt) (fun _ => O6.cnt) 0
@[expose] noncomputable def oR (l : Nat) : Nat :=
  sel7 l (fun _ => O0.R) (fun _ => O1.R) (fun _ => O2.R) (fun _ => O3.R)
    (fun _ => O4.R) (fun _ => O5.R) (fun _ => O6.R) 0

theorem base_ok : bAnd(allN 4 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (c2L k)),
    bAnd(allN 2 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (HCI (Nat.add k 6))),
    bAnd(allN 4 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (HCI (Nat.add k 13))),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) idn,
    allN 8 (fun i => bAnd(canonK 3850 12 (mask 12) (3850 * 12) (CS i),
      bAnd(canonK 3850 12 (mask 12) (3850 * 12) (CSI i),
        invEqK 3850 12 (mask 12) (3850 * 12) (CS i) (CSI i)))))))) = true := by
  quickRfl

theorem q_gens : allN 6 (fun j => bAnd(Nat.beq (Q.G j) (wk c1L (lget2 hsQWords j)),
    canonK 3850 12 (mask 12) (3850 * 12) (Q.G j))) = true := by
  quickRfl

theorem d_gens : allN 2 (fun j => bAnd(Nat.beq (D.G j) (wk c2L (lget2 hsDWords j)),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (D.G j),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (O0.GI j),
      invEqK 3850 12 (mask 12) (3850 * 12) (D.G j) (O0.GI j))))) = true := by
  quickRfl

theorem o_gens : allN 7 (fun l => allN 2 (fun j =>
    bAnd(Nat.beq (oG l j) (D.G j), Nat.beq (oGI l j) (O0.GI j)))) = true := by
  quickRfl

theorem cs_words : allN 8 (fun i => Nat.beq (CS i) (wk c2L (lget2 hsCosWords i))) = true := by
  quickRfl

theorem q_hd : bAnd(penumHdK idn Q.cnt 64 Q.T Q.PL, Nat.beq Q.cnt 64) = true := by quickRfl

theorem d_hd : bAnd(penumHdK idn D.cnt 360 D.T D.PL, Nat.beq D.cnt 360) = true := by quickRfl

theorem o_hd : allN 7 (fun l => bAnd(penumHdK (oR l) (oC l) 1000 (oT l) (oPL l),
    bAnd(Nat.beq (oR l) (wk D.G (lget2 hsDClassWords l)),
      Nat.beq (oC l) (nget hsDClassSizes l)))) = true := by
  quickRfl

theorem q_norm : allN 2 (fun j => allN 6 (fun i =>
    bAnd(strictB (NQ1 (Nat.add (Nat.mul j 6) i)) (fun q => bAnd(Nat.blt q Q.cnt,
      Nat.beq (Q.T q) (pc (pc (c1L j) (Q.G i)) (HCI (Nat.add j 6))))),
    strictB (NQ2 (Nat.add (Nat.mul j 6) i)) (fun q => bAnd(Nat.blt q Q.cnt,
      Nat.beq (Q.T q) (pc (pc (HCI (Nat.add j 6)) (Q.G i)) (c1L j))))))) = true := by
  quickRfl

theorem d_norm : allN 4 (fun j => allN 2 (fun i =>
    bAnd(strictB (ND1 (Nat.add (Nat.mul j 2) i)) (fun q => bAnd(Nat.blt q D.cnt,
      Nat.beq (D.T q) (pc (pc (c2L j) (D.G i)) (HCI (Nat.add j 13))))),
    strictB (ND2 (Nat.add (Nat.mul j 2) i)) (fun q => bAnd(Nat.blt q D.cnt,
      Nat.beq (D.T q) (pc (pc (HCI (Nat.add j 13)) (D.G i)) (c2L j))))))) = true := by
  quickRfl

theorem notin : allN 7 (fun l => allN 7 (fun l' => bIf(Nat.beq l l', true,
    notinK (oT l) (oC l) (oR l')))) = true := by
  quickRfl

@[expose] noncomputable def coverK (k : Nat) : Bool :=
  strictB (COV k) (fun wk =>
    strictB (Nat.shiftRight wk 16) (fun l => strictB (Nat.land wk 65535) (fun q =>
      bAnd(Nat.blt l 7, bAnd(Nat.blt q (oC l), Nat.beq (oT l q) (D.T k))))))

theorem cover : allN 360 coverK = true := by quickRfl

theorem cs_dist : allN 8 (fun i => allN 8 (fun j => bIf(Nat.beq i j, true,
    notinK D.T D.cnt (pc (CSI i) (CS j))))) = true := by
  quickRfl

theorem cs_comm : allN 2 (fun j => Nat.beq (pc (CS 1) (D.G j)) (pc (D.G j) (CS 1))) = true := by
  quickRfl

theorem cs_bad : allN 6 (fun i => strictB (nget hsCosCls i) (fun l => bAnd(Nat.blt l 7,
    notinK (oT l) (oC l) (pc (pc (CSI (Nat.add i 2)) (oR l)) (CS (Nat.add i 2)))))) = true := by
  quickRfl

end CFSG.KD.HSL

end
