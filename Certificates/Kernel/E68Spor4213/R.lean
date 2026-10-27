module

public import Certificates.Data.Kernel.SporLatCodeR
public import Certificates.Data.Kernel.SporLatOrb
public import Certificates.Data.E68Spor.Words
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.E68S4213

open CFSG.KC.SLOrb CFSG.KC.SLOm CFSG.KC.E64F CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.E6.Spor

@[expose] def AB23 (l p : Nat) : Nat := (if l = 0 then m23ta else m23tb).getD p 0

@[expose] def AB24 (l p : Nat) : Nat := (if l = 0 then m24ta else m24tb).getD p 0

@[expose] def Z23 (p : Nat) : Nat := (m23SLP[159]!).toList.getD p 0

@[expose] def Z24 (p : Nat) : Nat := (m24SLP[162]!).toList.getD p 0

@[expose] def L23 (l p : Nat) : Nat :=
  if l < CFSG.Quasithin.H.MathieuLat.m23STabs.length then
    (CFSG.Quasithin.H.MathieuLat.m23STabs.getD l #[]).toList.getD p 0
  else wordF AB23 (m23UWords.getD (l - CFSG.Quasithin.H.MathieuLat.m23STabs.length) []) p

@[expose] def L24 (l p : Nat) : Nat :=
  if l < CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs.length then
    (CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs.getD l #[]).toList.getD p 0
  else wordF AB24 (m24UWords.getD (l - CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs.length) []) p

@[expose] def D23 : List Nat :=
  insN (CFSG.Quasithin.H.MathieuLat.m23Sets.map (CFSG.QuasithinUnique.Ch1.SporLat.encodeSet 23))

@[expose] def D24 : List Nat :=
  insN (CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Sets.map
    (CFSG.QuasithinUnique.Ch1.SporLat.encodeSet 24))

theorem good23 : (goodB 23 m23ta.toArray (AB23 0) && goodB 23 m23tb.toArray (AB23 1) &&
    goodB 23 m23SLP[159]! Z23 &&
    (List.range CFSG.Quasithin.H.MathieuLat.m23STabs.length).all fun l =>
      goodB 23 (CFSG.Quasithin.H.MathieuLat.m23STabs.toArray.getD l #[]) (L23 l)) = true := by
  quickRfl

theorem good24 : (goodB 24 m24ta.toArray (AB24 0) && goodB 24 m24tb.toArray (AB24 1) &&
    goodB 24 m24SLP[162]! Z24 &&
    (List.range CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs.length).all fun l =>
      goodB 24 (CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs.toArray.getD l #[]) (L24 l)) =
    true := by
  quickRfl

theorem r23 : rChkC 23 D23 L23
    CFSG.Quasithin.H.MathieuLat.m23STabs.length AB23 Z23 m23UWords m23YWord m23NWord 7 21 100 =
    true := by
  quickRfl

theorem r24 : rChkC 24 D24 L24
    CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs.length AB24 Z24 m24UWords m24YWord m24NWord 7
    21 100 = true := by
  quickRfl

end CFSG.KD.E68S4213

end
