module

public import CFSG.Certificates.Kernel.LocalQTPairsHSound
public import Certificates.Kernel.LocalQT.Pairs.D4094
public import Certificates.Kernel.LocalQT.Pairs.D4094k
public import Certificates.Kernel.LocalQT.Pairs.D4094i
public import Certificates.Kernel.LocalQT.Pairs.D4094c
public import Certificates.Kernel.LocalQT.Pairs.D4094t
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KC.LQT.P CFSG.KC.LQT.L CFSG.KC.Ord CFSG.KD.LQT.M24Chain CFSG.KD.LQT.M24K
  CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs CFSG.Sporadic.Mathieu

theorem hA : cX m24a = 817395973838868159142633316802379971 := by decide +kernel
theorem hB : cX m24b = 938078705133617800621527216201835139 := by decide +kernel
theorem hS0 : List.map (CFSG.KC.LQT.W.evalZK 24 GAB) s0Words = S0G := by decide +kernel
theorem ht1 : CFSG.KC.LQT.W.evalZK 24 GAB (tWords.getD 0 []) = t1C := by decide +kernel
theorem ht3 : CFSG.KC.LQT.W.evalZK 24 GAB (tWords.getD 1 []) = t3C := by decide +kernel
theorem ht2 : CFSG.KC.LQT.W.codeP (t2Perm.headD 1) = t2C := by decide +kernel
theorem hQ1P : q1Perms.map CFSG.KC.LQT.W.codeP = Q1P := by decide +kernel
theorem hA2P : a2Perms.map CFSG.KC.LQT.W.codeP = A2P := by decide +kernel
theorem hJL : jLetters.map CFSG.KC.LQT.W.codeP = JL := by decide +kernel
theorem hwA : evalW jLetters wordA = m24gA := by decide +kernel
theorem hwB : evalW jLetters wordB = m24gB := by decide +kernel

@[expose] noncomputable def K1G : List Nat := S0G ++ [t1C]
@[expose] noncomputable def T0G : List Nat := S0G ++ [t3C]
@[expose] noncomputable def K2G : List Nat := S0G ++ [t2C]

theorem kCS : chainOK 24 CS = true := by quickRfl
theorem kCK1 : chainOK 24 CK1 = true := by quickRfl
theorem kCT0 : chainOK 24 CT0 = true := by quickRfl
theorem kCK2 : chainOK 24 CK2 = true := by quickRfl
theorem kCQ1 : chainOK 24 CQ1 = true := by quickRfl
theorem kCA2 : chainOK 24 CA2 = true := by quickRfl
theorem iCS : chainInj 24 CS = true := by quickRfl
theorem iCK1 : chainInj 24 CK1 = true := by quickRfl
theorem iCT0 : chainInj 24 CT0 = true := by quickRfl
theorem iCK2 : chainInj 24 CK2 = true := by quickRfl
theorem iCQ1 : chainInj 24 CQ1 = true := by quickRfl
theorem iCA2 : chainInj 24 CA2 = true := by quickRfl
theorem pK1 : CFSG.KC.LQT.P.allL K1G (CFSG.KC.LQT.P.permK 24) = true := by quickRfl
theorem pT0 : CFSG.KC.LQT.P.allL T0G (CFSG.KC.LQT.P.permK 24) = true := by quickRfl
theorem pK2 : CFSG.KC.LQT.P.allL K2G (CFSG.KC.LQT.P.permK 24) = true := by quickRfl
theorem lS : chainF CS = 1024 := by decide +kernel
theorem lK1 : chainF CK1 = 21504 := by decide +kernel
theorem lT0 : chainF CT0 = 64512 := by decide +kernel
theorem lK2 : chainF CK2 = 9216 := by decide +kernel
theorem lQ1 : chainF CQ1 = 128 := by decide +kernel
theorem lA2 : chainF CA2 = 256 := by decide +kernel

theorem gS : grpC 24 CS (chainF CS) S0G WS 40 = true := by quickRfl
theorem gQ1 : grpC 24 CQ1 (chainF CQ1) Q1P WQ1 40 = true := by quickRfl
theorem gA2 : grpC 24 CA2 (chainF CA2) A2P WA2 40 = true := by quickRfl
theorem gK1 : grpS 24 CK1 (chainF CK1) K1G WK1 60 = true := by quickRfl
theorem gT0 : grpS 24 CT0 (chainF CT0) T0G WT0 60 = true := by quickRfl
theorem gK2 : grpS 24 CK2 (chainF CK2) K2G WK2 60 = true := by quickRfl
theorem hkS : hkR 24 CS 1 0 = true := by quickRfl
theorem hkQ1 : hkR 24 CQ1 1 0 = true := by quickRfl
theorem hkA2 : hkR 24 CA2 1 0 = true := by quickRfl

noncomputable abbrev pA1 : Nat → Bool := fun c =>
  allL S0G fun s => Nat.beq (mul 24 s c) (mul 24 c s)
noncomputable abbrev pZ2 : Nat → Bool := fun y =>
  allL S0G fun s => CFSG.KC.LQT.S.memL (mul 24 (mul 24 (mul 24 y s) (inv 24 y)) (inv 24 s)) A1L
noncomputable abbrev pA2 : Nat → Bool := fun x =>
  allL Z2L fun y => Nat.beq (mul 24 y x) (mul 24 x y)

theorem kA1 : CFSG.KC.LQT.L.eqL (CFSG.KC.LQT.Syl.sortN (colAll 24 CS (fun c => c) pA1)) A1L =
    true := by quickRfl
theorem kZ2 : CFSG.KC.LQT.L.eqL (CFSG.KC.LQT.Syl.sortN (colAll 24 CS (fun c => c) pZ2)) Z2L =
    true := by quickRfl
theorem kA2 : CFSG.KC.LQT.L.eqL (CFSG.KC.LQT.Syl.sortN (colAll 24 CS (fun c => c) pA2)) A2L =
    true := by quickRfl
theorem kQ1L : CFSG.KC.LQT.L.eqL (CFSG.KC.LQT.Syl.sortN (colAll 24 CQ1 (fun c => c) fun _ => true))
    Q1L = true := by quickRfl
theorem kz : CFSG.KC.LQT.L.eqL (CFSG.KC.LQT.S.filtL A1L fun c => notB (Nat.beq c (one 24))) [zC] =
    true := by quickRfl
theorem kz1 : notB (Nat.beq zC (one 24)) = true := by quickRfl
theorem kA1z : allL A1L (fun a => orB (Nat.beq a (one 24)) (Nat.beq a zC)) = true := by quickRfl
theorem kzA1 : CFSG.KC.LQT.S.memL zC A1L = true := by quickRfl
theorem kA2P :
    allL A2P (fun a => andB (inC 24 CS (chainF CS) a) (CFSG.KC.LQT.S.memL a A2L)) = true := by
  quickRfl
theorem kA2Pd : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN A2P) = true := by quickRfl
theorem kQ1P : allL Q1P (inC 24 CS (chainF CS)) = true := by quickRfl
theorem kQ1Pd : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN Q1P) = true := by quickRfl
theorem kA2cl : allL A2L (inC 24 CA2 (chainF CA2)) = true := by quickRfl
theorem kA2d : CFSG.KC.LQT.T2.sincK A2L = true := by quickRfl
theorem kt2 : inC 24 CT0 (chainF CT0) t2C = true := by quickRfl
theorem kt : trioK 24 A2L = tC := by decide +kernel
theorem kts : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN
    ((List.range 24).map (orbMask A2L)))) = true := by quickRfl
theorem kJ :
    allL JL (fun g => orB (inC 24 CK1 (chainF CK1) g) (inC 24 CK2 (chainF CK2) g)) = true := by
  quickRfl

theorem kQ1K : allL Q1L (inC 24 CK1 (chainF CK1)) = true := by quickRfl
theorem kQ1n : allL Q1L (fun q => allL K1G fun k => andB (inC 24 CQ1 (chainF CQ1) (conj 24 k q))
    (inC 24 CQ1 (chainF CQ1) (CFSG.KC.LQT.Pairs.conjI 24 k q))) = true := by quickRfl
theorem kQ1e : allL Q1L (fun q => Nat.beq (CFSG.KC.LQT.Syl.sqK 24 q 4) (one 24)) = true := by
  quickRfl
theorem kA2K : allL A2L (inC 24 CK2 (chainF CK2)) = true := by quickRfl
theorem kA2n : allL A2L (fun q => allL K2G fun k => andB (inC 24 CA2 (chainF CA2) (conj 24 k q))
    (inC 24 CA2 (chainF CA2) (CFSG.KC.LQT.Pairs.conjI 24 k q))) = true := by quickRfl
theorem kA2e : allL A2L (fun q => Nat.beq (CFSG.KC.LQT.Syl.sqK 24 q 4) (one 24)) = true := by
  quickRfl
theorem kSe : allChain 24 CS (fun q => Nat.beq (CFSG.KC.LQT.Syl.sqK 24 q 10) (one 24)) = true := by
  quickRfl

noncomputable abbrev pN : Nat → Bool := fun x =>
  allL A2P fun a => CFSG.KC.LQT.S.memL (conj 24 x a) A2L

noncomputable abbrev ord3 : Nat → Bool := fun x =>
  andB (notB (Nat.beq x (one 24))) (Nat.beq (pow 24 x 3) (one 24))

noncomputable abbrev fK1 : Nat → Bool := fun x =>
  andB (Nat.beq (conj 24 x zC) zC) (andB (allL A1L fun a => andB
    (CFSG.KC.LQT.S.memL (conj 24 x a) A1L)
    (CFSG.KC.LQT.S.memL (CFSG.KC.LQT.Pairs.conjI 24 x a) A1L))
    (andB (impB (allL Q1L fun q => comm 24 x q) (CFSG.KC.LQT.S.memL x Q1L))
      (impB (ord3 x) (fiveK (fun q => encK 24 (mul 24 (conj 24 q x) (inv 24 x))) Q1L))))

noncomputable abbrev fK2 : Nat → Bool := fun x =>
  andB (pN x) (andB (impB (allL A2L fun q => comm 24 x q) (CFSG.KC.LQT.S.memL x A2L))
    (impB (ord3 x) (fiveK (fun q => encK 24 (mul 24 (conj 24 q x) (inv 24 x))) A2L)))

noncomputable abbrev fT : Nat → Bool := fun x => Nat.beq (actTK 24 x tC) tC

@[expose] def nT0 : List Nat := List.replicate 24 384

@[expose] noncomputable def tn (j : Nat) : Bool := Nat.beq (cntChunk 24 CT0 pN j) 384

end CFSG.KD.LQT.C4094

end
