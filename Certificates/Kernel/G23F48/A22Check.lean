module

public import Certificates.Kernel.G23F48.Chains
public import Certificates.Kernel.G23F48.A22Data
public import Certificates.Data.Kernel.G23F48.ConjOrb
public meta import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option compiler.extract_closed false

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.ONSchreier.Native

meta def gInvM : Array (Array Nat) := (burnsideF48t_g23Gens ()).map (pinvCand 728)

meta def tauM : Array (Array Nat) := #[burnsideF48t_g23Tau, pinvCand 728 burnsideF48t_g23Tau]

meta def orbM (gs : List (Array Nat)) (roots : List Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate 728 false
  for r in roots do
    seen := seen.set! r true
  for _ in [0:728] do
    for x in [0:728] do
      if seen[x]! then
        for g in gs do
          seen := seen.set! g[x]! true
  let mut out : Array Nat := #[]
  for x in [0:728] do
    if seen[x]! then
      out := out.push x
  return out

meta def restrM (om : Array Nat) (g : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for x in om do
    out := out.push (om.idxOf g[x]!)
  return out

meta def om1M : Array Nat :=
  let L := burnsideF48t_g23LArr
  orbM [L[0]!, L[1]!, L[2]!] [0, 1, 7]

meta def om2M : Array Nat :=
  let L := burnsideF48t_g23LArr
  orbM [L[0]!, L[1]!, L[3]!] [364, 365, 372]

meta def omM : Array (Array Nat) := #[om1M, om2M]

meta def r1M : Array (Array Nat) :=
  let L := burnsideF48t_g23LArr
  let K := burnsideF48t_g23KArr ()
  #[restrM om1M L[0]!, restrM om1M L[1]!, restrM om1M L[2]!, restrM om1M K[0]!,
    restrM om1M K[1]!]

meta def r2M : Array (Array Nat) :=
  let L := burnsideF48t_g23LArr
  let K := burnsideF48t_g23KArr ()
  #[restrM om2M L[0]!, restrM om2M L[1]!, restrM om2M L[3]!, restrM om2M K[0]!,
    restrM om2M K[1]!]

meta def r1IM : Array (Array Nat) :=
  #[pinvCand 121 r1M[0]!, pinvCand 121 r1M[1]!, pinvCand 121 r1M[2]!, pinvCand 121 r1M[3]!,
    pinvCand 121 r1M[4]!]

meta def r2IM : Array (Array Nat) :=
  #[pinvCand 121 r2M[0]!, pinvCand 121 r2M[1]!, pinvCand 121 r2M[2]!, pinvCand 121 r2M[3]!,
    pinvCand 121 r2M[4]!]

end CFSG.KC.G23F48

end

#kmisc_packarrs CFSG.KC.G23F48.GP CFSG.ASVolI.burnsideF48t_g23GensArr 10
#kmisc_packarrs CFSG.KC.G23F48.GPI CFSG.KC.G23F48.gInvM 10
#kmisc_packarrs CFSG.KC.G23F48.TP CFSG.KC.G23F48.tauM 10
#kmisc_packarrs CFSG.KC.G23F48.OM CFSG.KC.G23F48.omM 10
#kmisc_packarrs CFSG.KC.G23F48.R1 CFSG.KC.G23F48.r1M 7
#kmisc_packarrs CFSG.KC.G23F48.R1I CFSG.KC.G23F48.r1IM 7
#kmisc_packarrs CFSG.KC.G23F48.R2 CFSG.KC.G23F48.r2M 7
#kmisc_packarrs CFSG.KC.G23F48.R2I CFSG.KC.G23F48.r2IM 7

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22

theorem g_bind : allN 4 (fun i => arrBind (burnsideF48t_g23Gens ())[i]! 728 10 (GP i)) = true := by
  decide +kernel

theorem g_perm : allN 4 (fun i => permOK 728 10 (mask 10) (728 * 10) (GP i) (GPI i)) = true := by
  quickRfl

theorem t_bind : arrBind burnsideF48t_g23Tau 728 10 (TP 0) = true := by
  decide +kernel

theorem t_perm : permOK 728 10 (mask 10) (728 * 10) (TP 0) (TP 1) = true := by
  quickRfl

theorem x_words : allN 4 (fun i => Nat.beq (evPN 728 10 GP GPI (wX.getD i [])) (LP i)) = true ∧
    allN 4 (fun i => Nat.beq (evPN 728 10 GP GPI (wX.getD (i + 4) []))
      (pconj 728 10 (TP 0) (TP 1) (GP i))) = true := by
  decide +kernel

theorem tau_0 : 364 ≤ pg 10 (mask 10) (TP 0) 0 ∧ pg 10 (mask 10) (TP 0) 0 < 728 := by
  decide +kernel

theorem rel_ok : (burnsideF48t_g23R1 ++ burnsideF48t_g23R2 ++
    [(List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten]).all
      (fun r => Nat.beq (evP 728 10 LP LPI r) (pidn 728 10)) = true := by
  decide +kernel

theorem comm_ok : [KCh.S 0, KCh.S 1, pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1)].all (fun k =>
    !Nat.beq (pcomp 728 10 (mask 10) (pcomp 728 10 (mask 10) (LP 2) (LP 3)) k)
      (pcomp 728 10 (mask 10) k (pcomp 728 10 (mask 10) (LP 2) (LP 3)))) = true := by
  decide +kernel

theorem fix_ok :
    pg 10 (mask 10) (LP 0) 0 = 0 ∧ pg 10 (mask 10) (LP 0) 364 = 364 ∧
    pg 10 (mask 10) (LP 1) 0 = 0 ∧ pg 10 (mask 10) (LP 1) 364 = 364 ∧
    pg 10 (mask 10) (LP 2) 0 = 0 ∧ pg 10 (mask 10) (LP 3) 364 = 364 ∧
    pg 10 (mask 10) (LP 3) 0 ≠ 0 ∧ pg 10 (mask 10) (LP 2) 364 ≠ 364 ∧
    allN 3 (fun j => Nat.beq (pg 10 (mask 10) (S0C.S j) 0) 0 &&
      Nat.beq (pg 10 (mask 10) (S0C.S j) 364) 364) = true ∧
    allN 728 (fun p => Nat.beq p 0 || Nat.beq p 364 ||
      [0, 1, 2].any fun j => !Nat.beq (pg 10 (mask 10) (S0C.S j) p) p) = true ∧
    allN 364 (fun p => [0, 1, 2].any fun j =>
      !Nat.beq (pg 10 (mask 10) (LP j) (p + 364)) (p + 364)) = true ∧
    allN 364 (fun p => [0, 1, 3].any fun j => !Nat.beq (pg 10 (mask 10) (LP j) p) p) = true := by
  decide +kernel

theorem x_pres : allN 4 (fun i => allN 364 (fun p => Nat.blt (pg 10 (mask 10) (GP i) p) 364)) =
    true := by
  decide +kernel

theorem p1_trees : reachP 728 10 1 [LP 0, LP 1, LP 2] trP1_1 = true ∧
    reachP 728 10 7 [LP 0, LP 1, LP 2] trP1_7 = true ∧
    reachP 728 10 34 [LP 0, LP 1, LP 2] trP1_34 = true ∧
    coverP (trP1_1 ++ trP1_7 ++ trP1_34) 1 363 = true := by
  decide +kernel

theorem p2_trees : reachP 728 10 365 [LP 0, LP 1, LP 3] trP2_365 = true ∧
    reachP 728 10 372 [LP 0, LP 1, LP 3] trP2_372 = true ∧
    reachP 728 10 400 [LP 0, LP 1, LP 3] trP2_400 = true ∧
    coverP (trP2_365 ++ trP2_372 ++ trP2_400) 365 363 = true := by
  decide +kernel

theorem ha_trees :
    [1, 7, 34] = (List.range 3).map (fun j =>
      pg 10 (mask 10) (evP 728 10 GP GPI (burnsideF48t_g23HA.getD j [])) 0) ∧
    reachP 728 10 0 [LP 0, LP 1, LP 2, evP 728 10 GP GPI (burnsideF48t_g23HA.getD 0 [])] trHA0 =
      true ∧
    reachP 728 10 0 [LP 0, LP 1, LP 2, evP 728 10 GP GPI (burnsideF48t_g23HA.getD 1 [])] trHA1 =
      true ∧
    reachP 728 10 0 [LP 0, LP 1, LP 2, evP 728 10 GP GPI (burnsideF48t_g23HA.getD 2 [])] trHA2 =
      true ∧
    coverP trHA0 0 364 = true ∧ coverP trHA1 0 364 = true ∧ coverP trHA2 0 364 = true := by
  decide +kernel

theorem hb_trees :
    [365, 372, 400] = (List.range 3).map (fun j =>
      pg 10 (mask 10) (evP 728 10 GP GPI (burnsideF48t_g23HB.getD j [])) 364) ∧
    reachP 728 10 364 [LP 0, LP 1, LP 3, evP 728 10 GP GPI (burnsideF48t_g23HB.getD 0 [])] trHB0 =
      true ∧
    reachP 728 10 364 [LP 0, LP 1, LP 3, evP 728 10 GP GPI (burnsideF48t_g23HB.getD 1 [])] trHB1 =
      true ∧
    reachP 728 10 364 [LP 0, LP 1, LP 3, evP 728 10 GP GPI (burnsideF48t_g23HB.getD 2 [])] trHB2 =
      true ∧
    coverP trHB0 364 364 = true ∧ coverP trHB1 364 364 = true ∧ coverP trHB2 364 364 = true := by
  decide +kernel

theorem s0_norm : allN 2 (fun i => allN 3 (fun j =>
    Nat.beq (evPN 728 10 S0C.S S0C.SI (wS.getD (3 * i + j) []))
      (pconj 728 10 (LP i) (LPI i) (S0C.S j)))) = true := by
  decide +kernel

@[expose] noncomputable def kEls : List Nat :=
  [pidn 728 10, KCh.S 0, KCh.S 1, pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1)]

theorem k_ok : Nat.beq (pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 0)) (pidn 728 10) = true ∧
    Nat.beq (pcomp 728 10 (mask 10) (KCh.S 1) (KCh.S 1)) (pidn 728 10) = true ∧
    Nat.beq (pcomp 728 10 (mask 10) (KCh.S 0) (KCh.S 1))
      (pcomp 728 10 (mask 10) (KCh.S 1) (KCh.S 0)) = true ∧
    [2, 3].all (fun r => [0, 1].all (fun t =>
      kEls.contains (pconj 728 10 (LP r) (LPI r) (KCh.S t))) && !kEls.contains (LP r)) = true := by
  decide +kernel

theorem om_ok : allN 2 (fun t => allN 120 (fun i =>
    Nat.blt (pg 10 (mask 10) (OM t) i) (pg 10 (mask 10) (OM t) (i + 1))) &&
      Nat.blt (pg 10 (mask 10) (OM t) 120) 728) = true := by
  decide +kernel

theorem r_bind :
    allN 5 (fun s => allN 121 (fun i =>
      Nat.beq (pg 10 (mask 10) ([LP 0, LP 1, LP 2, KCh.S 0, KCh.S 1].getD s 0)
        (pg 10 (mask 10) (OM 0) i)) (pg 10 (mask 10) (OM 0) (pg 7 (mask 7) (R1 s) i)))) = true ∧
    allN 5 (fun s => allN 121 (fun i =>
      Nat.beq (pg 10 (mask 10) ([LP 0, LP 1, LP 3, KCh.S 0, KCh.S 1].getD s 0)
        (pg 10 (mask 10) (OM 1) i)) (pg 10 (mask 10) (OM 1) (pg 7 (mask 7) (R2 s) i)))) = true := by
  decide +kernel

theorem r_perm : allN 5 (fun s => permOK 121 7 (mask 7) (121 * 7) (R1 s) (R1I s) &&
    permOK 121 7 (mask 7) (121 * 7) (R2 s) (R2I s)) = true := by
  quickRfl

theorem conj1_ok : conjQ 121 7 115809 [R1 0, R1 1, R1 2] [R1I 0, R1I 1, R1I 2] (R1 3) (R1 4) cC1
    1458 = true := by
  decide +kernel

theorem conj2_ok : conjQ 121 7 128945 [R2 0, R2 1, R2 2] [R2I 0, R2I 1, R2I 2] (R2 3) (R2 4) cC2
    1458 = true := by
  decide +kernel

theorem a22_neg :
    Nat.beq (evPN 728 10 GP GPI (wX.getD 0 [])) (LP 1) = false ∧
    Nat.beq (evP 728 10 LP LPI [((2 : Fin 4), true)]) (pidn 728 10) = false ∧
    reachP 728 10 7 [LP 0, LP 1, LP 2] trP1_1 = false ∧
    coverP (trP1_1 ++ trP1_34) 1 363 = false ∧
    conjQ 121 7 115809 [R1 0, R1 1, R1 2] [R1I 0, R1I 1, R1I 2] (R1 3) (R1 4) cC1 1457 = false ∧
    conjQ 121 7 1000 [R1 0, R1 1, R1 2] [R1I 0, R1I 1, R1I 2] (R1 3) (R1 4) cC1 1458 = false ∧
    conjQ 121 7 115809 [R1 0, R1 1, R1 2] [R1I 0, R1I 1, R1I 2] (R1 3) (R1 4) cC1.tail 1458 =
      false ∧
    kEls.contains (LP 0) = false := by
  decide +kernel

end CFSG.KC.G23F48

end
