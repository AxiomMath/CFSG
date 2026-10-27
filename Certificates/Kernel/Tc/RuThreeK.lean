module

public import Certificates.Kernel.Tc.RuK
public import Certificates.Kernel.Tc.RuThreeSrc
public meta import Certificates.Kernel.Tc.RuThreeSrc
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelTc.Ru.ET CertificateChecks.KernelTc.Ru.tenGs
  CertificateChecks.KernelTc.Ru.keys10 10 4

public section

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.TcF
  CFSG.KC.Misc.ArrEnum CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.Monster.B.Co2.Native

@[expose] noncomputable def anyF (N : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN N fun j => bIf(f j, false, true), false, true)

@[expose] noncomputable def gy (k x : Nat) : Nat := t3 (Nat.add 3 k) x

@[expose] noncomputable def EY (i k : Nat) : Nat := fld(TY.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def ty (i x : Nat) : Nat := trV gy TY.P TY.L 27 i x
@[expose] noncomputable def ky (i : Nat) : Nat := keyV 4060 ruKeys (ty i)

theorem kNY : Nat.beq TY.N 27 = true := by quickRfl

theorem kTreeY : allN 27 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 TY.P TY.L i)) = true := by
  quickRfl

theorem kReplayY : CFSG.KC.Bfs.replayOK EY 2 27 = true := by quickRfl

theorem kEdgeY : allN 27 (edgeAtK gy q0 TY.P TY.L EY 27 27 2 bs) = true := by quickRfl

theorem kSortY : allN 27 (sortAtK ky TY.SK TY.SKI 27) = true := by quickRfl

theorem kCube : eqOnL bs (powF (t3 0) 3) (fun y => y) = true := by quickRfl

theorem kNe : (!eqOnL bs (t3 0) (fun y => y)) = true := by quickRfl

theorem kRels : ruRels.all (fun r => decide (r.2.2 < 5) && decide (r.1 < ruBase.size) &&
    decide (r.2.1 < ruBase.size) && powF (t3 0) r.2.2 ruBase[r.1]! == ruBase[r.2.1]!) = true := by
  decide +kernel

theorem kComm : allN 2 (fun k => eqOnL bs (fun y => gc k (t3 0 y)) (fun y => t3 0 (gc k y))) =
    true := by quickRfl

theorem kSyl : allN 27 (fun k => bIf(eqOnL bs (ty k) (fun y => y), true,
    anyF 26 fun j => eqOnL bs (fun y => t3 (Nat.add 5 j) (ty k (i3 (Nat.add 5 j) y))) (t3 0))) =
    true := by quickRfl

theorem kFix : allN 4060 (fun i => bIf(Nat.beq (t3 0 i) i, ruF.contains i, !ruF.contains i)) =
    true := by quickRfl

theorem kKer : allN 2160 (fun k => bIf(ruF.all (fun p => Nat.beq (tc k p) p),
    eqOnL bs (powF (tc k) 3) (fun y => y), true)) = true := by quickRfl

theorem kR0 : ∀ i < 10, (ruF.idxOf (t3 1 ruF[i]!) == ruR0[i]!) = true := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem kR1 : ∀ i < 10, (ruF.idxOf (t3 2 ruF[i]!) == ruR1[i]!) = true := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem bT : ∀ j < 2, arrBind tenGs[j]! 10 4 (ET.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem nT : Nat.beq ET.ng 2 = true ∧ Nat.beq ET.N 720 = true := ⟨by quickRfl, by quickRfl⟩

theorem pT : allN 2 (fun k => permB 10 4 (ET.G k)) = true := by quickRfl

theorem kTwo : allN 10 (fun a => allN 10 fun b => bIf(Nat.beq a b, true,
    anyF 720 fun k => bAnd(Nat.beq (pg 4 (mask 4) (ET.T k) 0) a,
      Nat.beq (pg 4 (mask 4) (ET.T k) 1) b))) = true := by quickRfl

theorem kFixNeg : (!allN 4060 (fun i => bIf(Nat.beq (t3 0 i) i, (ruF.erase 622).contains i,
    !(ruF.erase 622).contains i))) = true := by quickRfl

theorem kSylNeg : (!allN 27 (fun k => bIf(eqOnL bs (ty k) (fun y => y), true,
    anyF 1 fun j => eqOnL bs (fun y => t3 (Nat.add 5 j) (ty k (i3 (Nat.add 5 j) y))) (t3 0)))) =
    true := by quickRfl

end CertificateChecks.KernelTc.Ru

end
