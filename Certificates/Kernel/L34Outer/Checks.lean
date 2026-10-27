module

public import Certificates.Kernel.L34Outer.Data
public import Certificates.Kernel.L34Outer.Words
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.L34OuterData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL34Outer

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open Certificates.L34Outer

@[expose] noncomputable def ET (e j : Nat) : Nat :=
  nIf(Nat.beq e 0, E0.T j, nIf(Nat.beq e 1, E1.T j, nIf(Nat.beq e 2, E2.T j, E3.T j)))

@[expose] noncomputable def EG (e j : Nat) : Nat :=
  nIf(Nat.beq e 0, E0.G j, nIf(Nat.beq e 1, E1.G j, nIf(Nat.beq e 2, E2.G j, E3.G j)))

@[expose] noncomputable def ctrK (Z A B : Nat) : Bool :=
  allN 27 (fun i => strictB (PE.T i) (fun t =>
    bIf(Nat.beq t (pidn 42 6), true, bIf(Nat.beq t Z, true,
      bIf(Nat.beq t (pcomp 42 6 (mask 6) Z Z), true,
        bIf(Nat.beq (pcomp 42 6 (mask 6) t A) (pcomp 42 6 (mask 6) A t),
          bIf(Nat.beq (pcomp 42 6 (mask 6) t B) (pcomp 42 6 (mask 6) B t), false, true), true))))))

@[expose] noncomputable def cvK (CV : Nat → Nat) : Bool :=
  allN 27 (fun i => strictB (CV i) (fun c => bAnd(Nat.blt (Nat.div c 16) 4,
    bAnd(Nat.blt (Nat.mod c 16) 9, Nat.beq (ET (Nat.div c 16) (Nat.mod c 16)) (PE.T i)))))

@[expose] noncomputable def yK (e j : Nat) : Bool :=
  strictB (r32 YH (Nat.add (Nat.mul 2 e) j)) (fun c => bAnd(Nat.blt c 9,
    bAnd(wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4 ((l34OuterData.es[Nat.succ e]!).ys[j]!)
      (ET (Nat.succ e) c),
    bAnd(bIf(Nat.beq (ET (Nat.succ e) c) (pidn 42 6), false, true),
      Nat.beq (pcomp 42 6 (mask 6) (HP (Nat.add (Nat.mul 2 e) j)) (ET (Nat.succ e) c))
        (pcomp 42 6 (mask 6) (ET (Nat.succ e) c) (HP (Nat.add (Nat.mul 2 e) j)))))))

@[expose] noncomputable def genK (e k : Nat) : Bool :=
  wordEqK 42 6 (mask 6) (pidn 42 6) (fun l => HP (Nat.add (Nat.mul 2 e) l))
    (fun l => HPI (Nat.add (Nat.mul 2 e) l)) 2 ((gW[e]!)[k]!) (GP k)

@[expose] noncomputable def xK (Z j : Nat) : Bool :=
  bAnd(wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 6 (xW[j]!) (XP j),
    bAnd(canonK 42 6 (mask 6) (42 * 6) (XP j),
      Nat.beq (pcomp 42 6 (mask 6) (XP j) Z) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) Z Z) (XP j))))

theorem ch19768_sz : szOK 42 6 = true := by quickRfl
theorem ch19768_gp : allN 6 (fun k => permOK 42 6 (mask 6) (42 * 6) (GP k) (GPI k)) = true := by
  quickRfl
theorem ch19768_r4 : Nat.beq (pcomp 42 6 (mask 6) (GP 3) (pcomp 42 6 (mask 6) (GP 3) (GP 3)))
    (pidn 42 6) = true := by quickRfl
theorem ch19768_r5 : Nat.beq (pcomp 42 6 (mask 6) (GP 4) (GP 4)) (pidn 42 6) = true := by quickRfl
theorem ch19768_r6 : Nat.beq (pcomp 42 6 (mask 6) (GP 5) (GP 5)) (pidn 42 6) = true := by quickRfl
theorem ch19768_r56 : Nat.beq (pcomp 42 6 (mask 6) (GP 4) (GP 5)) (pcomp 42 6 (mask 6) (GP 5) (GP 4))
    = true := by quickRfl
theorem ch19768_r54 : Nat.beq (pcomp 42 6 (mask 6) (GP 4) (pcomp 42 6 (mask 6) (GP 3) (GP 4)))
    (pcomp 42 6 (mask 6) (GP 3) (GP 3)) = true := by quickRfl
theorem ch19768_r64 : Nat.beq (pcomp 42 6 (mask 6) (GP 5) (pcomp 42 6 (mask 6) (GP 3) (GP 5)))
    (pcomp 42 6 (mask 6) (GP 3) (GP 3)) = true := by quickRfl

theorem ch19768_pa : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4 l34OuterData.a (PE.G 0) = true := by
  quickRfl
theorem ch19768_pb : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4 l34OuterData.b (PE.G 1) = true := by
  quickRfl
theorem ch19768_pgc : allN 2 (fun j => canonK 42 6 (mask 6) (42 * 6) (PE.G j)) = true := by quickRfl
theorem ch19768_eu : allN 4 (fun e => wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4
    (l34OuterData.es[e]!).u (EG e 0)) = true := by quickRfl
theorem ch19768_ev : allN 4 (fun e => wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4
    (l34OuterData.es[e]!).v (EG e 1)) = true := by quickRfl
theorem ch19768_egc : allN 4 (fun e => allN 2 (fun j => canonK 42 6 (mask 6) (42 * 6) (EG e j))) =
    true := by quickRfl

theorem ch19768_ph : penumHdK (pidn 42 6) PE.cnt 27 PE.T PE.PL = true := by quickRfl
theorem ch19768_ps : penumSlK 42 6 (mask 6) (42 * 6) false PE.G PE.GI PE.k PE.cnt PE.T PE.PL
    PE.POS PE.SRT PE.SRI 0 27 = true := by quickRfl
theorem ch19768_e0h : penumHdK (pidn 42 6) E0.cnt 9 E0.T E0.PL = true := by quickRfl
theorem ch19768_e0s : penumSlK 42 6 (mask 6) (42 * 6) false E0.G E0.GI E0.k E0.cnt E0.T E0.PL
    E0.POS E0.SRT E0.SRI 0 9 = true := by quickRfl
theorem ch19768_e1h : penumHdK (pidn 42 6) E1.cnt 9 E1.T E1.PL = true := by quickRfl
theorem ch19768_e1s : penumSlK 42 6 (mask 6) (42 * 6) false E1.G E1.GI E1.k E1.cnt E1.T E1.PL
    E1.POS E1.SRT E1.SRI 0 9 = true := by quickRfl
theorem ch19768_e2h : penumHdK (pidn 42 6) E2.cnt 9 E2.T E2.PL = true := by quickRfl
theorem ch19768_e2s : penumSlK 42 6 (mask 6) (42 * 6) false E2.G E2.GI E2.k E2.cnt E2.T E2.PL
    E2.POS E2.SRT E2.SRI 0 9 = true := by quickRfl
theorem ch19768_e3h : penumHdK (pidn 42 6) E3.cnt 9 E3.T E3.PL = true := by quickRfl
theorem ch19768_e3s : penumSlK 42 6 (mask 6) (42 * 6) false E3.G E3.GI E3.k E3.cnt E3.T E3.PL
    E3.POS E3.SRT E3.SRI 0 9 = true := by quickRfl

theorem ch19768_sub : allN 4 (fun e => allN 2 (fun j => bAnd(Nat.blt (r32 PH (Nat.add (Nat.mul 2 e) j)) 27,
    Nat.beq (PE.T (r32 PH (Nat.add (Nat.mul 2 e) j))) (EG e j)))) = true := by quickRfl
theorem ch19768_cv : cvK (r32 CV) = true := by quickRfl
theorem ch19768_ctr : ctrK (E0.G 0) (PE.G 0) (PE.G 1) = true := by quickRfl
theorem ch19768_zne : bIf(Nat.beq (E0.G 0) (pidn 42 6), false, true) = true := by quickRfl

theorem ch19768_sw : allN 2 (fun j => wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3 (sW[j]!) (E0.G j)) =
    true := by quickRfl
theorem ch19768_hw : allN 3 (fun e => allN 2 (fun j => bAnd(wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4
    ((l34OuterData.es[Nat.succ e]!).hs[j]!) (HP (Nat.add (Nat.mul 2 e) j)),
    permOK 42 6 (mask 6) (42 * 6) (HP (Nat.add (Nat.mul 2 e) j)) (HPI (Nat.add (Nat.mul 2 e) j)))))
    = true := by quickRfl
theorem ch19768_y : allN 3 (fun e => allN 2 (fun j => yK e j)) = true := by quickRfl
theorem ch19768_gen : allN 3 (fun e => allN 4 (fun k => genK e k)) = true := by quickRfl
theorem ch19768_x : allN 3 (fun j => xK (E0.G 0) j) = true := by quickRfl

theorem ch19768_nc : bIf(Nat.beq (pcomp 42 6 (mask 6) (PE.G 0) (PE.G 1))
    (pcomp 42 6 (mask 6) (PE.G 1) (PE.G 0)), false, true) = true := by quickRfl
end CertificateChecks.KernelL34Outer

end
