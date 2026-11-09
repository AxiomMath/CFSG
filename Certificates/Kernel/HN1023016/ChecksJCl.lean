module

public import Certificates.Kernel.HN1023016.Snaps
public import Certificates.Data.Kernel.SlpPcRun
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HN1023016

open CFSG.KC.SlpPc CFSG.KC.Ord

@[expose] noncomputable def SM (i : Nat) : Store := stOf S.VR S.BL (3 + Nat.min (32 * i) 2084)

@[expose, reducible] noncomputable def RF : Nat → Nat :=
  lk CFSG.KD.FamHNSeed.ONE (SM 66).1 (SM 66).2.1 (SM 66).2.2

@[expose] noncomputable def gC (i : Nat) : Bool :=
  chkS mul CFSG.KD.FamHNSeed.ONE (((prg ++ px).drop (32 * i)).take 32) (SM i) (SM (i + 1))

@[expose] noncomputable def rE (t : Nat) : Bool :=
  relE mul CFSG.KD.FamHNSeed.ONE S.HS S.PW rel t

@[expose] noncomputable def fE (t : Nat) : Bool :=
  fusE mul CFSG.KD.FamHNSeed.ONE RF S.PW wr (nthD List.nil fus t)

@[expose] noncomputable def MS : List Nat := [2, 2, 2, 0, 12]

@[expose] noncomputable def LS (k i : Nat) : Store :=
  stOf (nthD List.nil S.CVL k) (nthD List.nil S.CBL k)
    (nthD 0 S.CN k + Nat.min (32 * i) (nthD List.nil lp k).length)

@[expose] noncomputable def lpC (k i : Nat) : Bool :=
  chkS mul CFSG.KD.FamHNSeed.ONE (((nthD List.nil lp k).drop (32 * i)).take 32) (LS k i)
    (LS k (i + 1))

@[expose] noncomputable def k0C : Nat → Bool := lpC 0
@[expose] noncomputable def k1C : Nat → Bool := lpC 1
@[expose] noncomputable def k2C : Nat → Bool := lpC 2
@[expose] noncomputable def k4C : Nat → Bool := lpC 4

@[expose] noncomputable def lpI (k : Nat) : Bool :=
  stEq (clInit CFSG.KD.FamHNSeed.ONE RF S.HS (nthD List.nil ce k)) (LS k 0)

@[expose] noncomputable def clE (k : Nat) : Bool :=
  entsAll mul CFSG.KD.FamHNSeed.ONE RF S.PW (RF (nthD 0 wr k)) (nthD List.nil ce k)

@[expose] noncomputable def clZ (k : Nat) : Bool :=
  (fun s : Store => andB
    (Nat.beq (lk CFSG.KD.FamHNSeed.ONE s.1 s.2.1 s.2.2 (nthD 0 (nthD List.nil lab k) 0))
      (CFSG.KD.FamHNSeed.RW 1))
    (Nat.beq (lk CFSG.KD.FamHNSeed.ONE s.1 s.2.1 s.2.2 (nthD 0 (nthD List.nil lab k) 1))
      (CFSG.KD.FamHNSeed.RW 2))) (LS k (nthD 0 MS k))

theorem gI : stEq (List.nil, [CFSG.KD.FamHNSeed.RW 2, CFSG.KD.FamHNSeed.RW 1,
    CFSG.KD.FamHNSeed.ONE], 3) (SM 0) = true := by quickRfl

theorem gHS : mapS (fun w => wordP mul CFSG.KD.FamHNSeed.ONE (fun l => RF (nthD 0 wg l)) w) hw
    (fun xs => xs == S.HS) = true := by quickRfl

theorem gPW : pows mul CFSG.KD.FamHNSeed.ONE S.HS (fun pw => pw == S.PW) = true := by quickRfl

theorem g6 : Nat.beq S.HS.length 6 = true := by quickRfl

theorem gRI : relsIdx rel 0 0 = true := by quickRfl

theorem gHwm : hwmOK L9 H9 hwm = true := by quickRfl

theorem gBw : bwOK CFSG.KD.FamHNSeed.L bw = true := by quickRfl

theorem gInv : invOK vec CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV CFSG.KD.FamHNSeed.RM bw S.HS
    hwm = true := by quickRfl

#kc_each gC 0 66
#kc_each rE 0 21
#kc_each fE 0 50
#kc_each k0C 0 2
#kc_each k1C 0 2
#kc_each k2C 0 2
#kc_each k4C 0 12
#kc_each lpI 0 3
#kc_each lpI 4 5
#kc_each clE 0 3
#kc_each clE 4 5
#kc_each clZ 0 3
#kc_each clZ 4 5

#kc_forall_tree gC_all (fun i => gC i = true) 66 CFSG.KD.HN1023016.gC
#kc_forall_tree rE_all (fun i => rE i = true) 21 CFSG.KD.HN1023016.rE
#kc_forall_tree fE_all (fun i => fE i = true) 50 CFSG.KD.HN1023016.fE
#kc_forall_tree k0C_all (fun i => k0C i = true) 2 CFSG.KD.HN1023016.k0C
#kc_forall_tree k1C_all (fun i => k1C i = true) 2 CFSG.KD.HN1023016.k1C
#kc_forall_tree k2C_all (fun i => k2C i = true) 2 CFSG.KD.HN1023016.k2C
#kc_forall_tree k4C_all (fun i => k4C i = true) 12 CFSG.KD.HN1023016.k4C

theorem clOK (k : Nat) (hm : (nthD List.nil lp k).length ≤ 32 * nthD 0 MS k)
    (hI : lpI k = true) (hch : ∀ i < nthD 0 MS k, lpC k i = true) (hE : clE k = true)
    (hZ : clZ k = true) :
    clK mul CFSG.KD.FamHNSeed.ONE (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) RF S.PW S.HS
      (RF (nthD 0 wr k)) (nthD List.nil ce k) (nthD List.nil lp k) (nthD List.nil lab k) = true := by
  refine clK_of (LS k (nthD 0 MS k)) hE ?_ hZ
  rw [eq_of_stEq hI]
  exact stP_of_chunks (S := LS k) (K := 32) (m := nthD 0 MS k) hm hch

theorem ce_length : ce.length = 5 := by decide +kernel

theorem chkJCl : chkJClW prg px wg wr hw rel fus bw hwm ce lp lab = true := by
  have hrun : stP mul CFSG.KD.FamHNSeed.ONE (prg ++ px)
      (List.nil, [CFSG.KD.FamHNSeed.RW 2, CFSG.KD.FamHNSeed.RW 1, CFSG.KD.FamHNSeed.ONE], 3) =
      SM 66 := by
    rw [eq_of_stEq gI]
    exact stP_of_chunks (S := SM) (K := 32) (m := 66) (by decide +kernel) gC_all
  refine chkJCl_of (SM 66) S.HS S.PW hrun (map_of_mapS gHS) (powsL_of_pows gPW) g6 gRI rE_all
    gHwm gBw gInv fE_all ce_length ?_
  intro k hk
  rw [ce_length] at hk
  match k, hk with
  | 0, _ => exact Or.inr (clOK 0 (by decide +kernel) lpI0 k0C_all clE0 clZ0)
  | 1, _ => exact Or.inr (clOK 1 (by decide +kernel) lpI1 k1C_all clE1 clZ1)
  | 2, _ => exact Or.inr (clOK 2 (by decide +kernel) lpI2 k2C_all clE2 clZ2)
  | 3, _ => exact Or.inl (by decide +kernel)
  | 4, _ => exact Or.inr (clOK 4 (by decide +kernel) lpI4 k4C_all clE4 clZ4)
  | _ + 5, h => exact absurd h (by omega)

theorem gC_neg : (!chkS mul CFSG.KD.FamHNSeed.ONE ((prg ++ px).take 32) (SM 0) (SM 2)) = true := by
  quickRfl

end CFSG.KD.HN1023016

end
