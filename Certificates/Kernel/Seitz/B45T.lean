module

public import Certificates.Kernel.Seitz.B45
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSeitz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.SeitzB45
open CFSG.PSL3Four.Native Certificates.Seitz77CaseB45

@[expose] noncomputable def repT : Nat → Nat := vB (B45A 1)
@[expose] noncomputable def rsT : Nat → Nat := rsB (B45A 3)

@[expose] noncomputable def mulK (c : Nat) : Bool :=
  allN 64 fun d => allN 256 fun j => bAnd(Nat.blt (mtT (64 * c + d) j) 256,
    Nat.beq (pcomp 42 6 (mask 6) (TLE.T (64 * c + d)) (TLE.T j)) (TLE.T (mtT (64 * c + d) j)))

@[expose] noncomputable def bindK : Bool :=
  (List.range 256).all (fun i => ((List.range 256).find? fun j => mtT i j == 0).getD 0 == invT i) &&
  (List.range 256).all (fun i =>
    isUT i == (List.range 64).any fun k => Nat.beq (UE.T k) (TLE.T i)) &&
  (List.range 64).all (fun k => (List.range 256).any fun i => Nat.beq (TLE.T i) (UE.T k)) &&
  (List.range 256).all (fun i =>
    ((List.range 256).find? fun j => isUT (mtT (invT j) i)).getD i == repT i) &&
  ((List.range 256).filter fun i => repT i == i) == [rsT 0, rsT 1, rsT 2, rsT 3] &&
  (List.range 256).all (fun i =>
    ([rsT 0, rsT 1, rsT 2, rsT 3].findIdx? (· == repT i)).getD 0 == labT i)

@[expose] noncomputable def tabK : Bool :=
  (allBelow 256 fun i => invT i < 256 && mtT i (invT i) == 0) &&
  (allBelow 256 fun i => labT i < 4) &&
  (allBelow 4 fun p => rsT p < 256 && labT (rsT p) == p) &&
  labT 0 == 0 &&
  (allBelow 256 fun i => allBelow 256 fun j => (labT i == labT j) == isUT (mtT (invT i) j)) &&
  (allBelow 256 fun i => allBelow 256 fun j => labT (mtT i j) == laddT (labT i) (labT j))

theorem t_hd : bAnd(gensK tlGens 42 6 TLE.k TLE.G, bAnd(Nat.beq TLE.cnt 256,
    penumHdK (pidn 42 6) TLE.cnt 256 TLE.T TLE.PL)) = true := by quickRfl

theorem t_sl : penumSlK 42 6 (mask 6) (42 * 6) false TLE.G TLE.GI TLE.k TLE.cnt TLE.T TLE.PL
    TLE.POS TLE.SRT TLE.SRI 0 256 = true := by quickRfl

theorem u_hd : bAnd(gensK uGens 42 6 UE.k UE.G, bAnd(Nat.beq UE.cnt 64,
    penumHdK (pidn 42 6) UE.cnt 64 UE.T UE.PL)) = true := by quickRfl

theorem u_sl : penumSlK 42 6 (mask 6) (42 * 6) false UE.G UE.GI UE.k UE.cnt UE.T UE.PL
    UE.POS UE.SRT UE.SRI 0 64 = true := by quickRfl

end CertificateChecks.KernelSeitz

#kc_each CertificateChecks.KernelSeitz.mulK 0 4

namespace CertificateChecks.KernelSeitz

open CFSG.KC.SeitzB45 Certificates.Seitz77CaseB45

theorem k_bind : bindK = true := by decide +kernel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.PSL3Four.Native

@[expose] noncomputable def vBF (V i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (pg 8 (mask 8) V i) (Nat.blt i 256)

@[expose] noncomputable def mtBF (P : Nat → Nat) (i j : Nat) : Nat :=
  (fun k => Bool.rec (motive := fun _ => Nat) 0
    (pg 8 (mask 8) (P (Nat.div k 256)) (Nat.mod k 256)) (Nat.blt k 65536)) (Nat.add (Nat.mul 256 i) j)

@[expose] noncomputable def rsBF (R p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (pg 8 (mask 8) R p) (Nat.blt p 4)

@[expose] noncomputable def bEqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

theorem vB_eqF (V i : Nat) : vB V i = vBF V i := by
  unfold vB vBF
  by_cases hi : i < 256
  · rw [if_pos hi, show Nat.blt i 256 = true from by simpa using hi]
  · rw [if_neg hi, show Nat.blt i 256 = false from Bool.eq_false_iff.2 (fun h => hi (by simpa using h))]

theorem rsB_eqF (R p : Nat) : rsB R p = rsBF R p := by
  unfold rsB rsBF
  by_cases hi : p < 4
  · rw [if_pos hi, show Nat.blt p 4 = true from by simpa using hi]
  · rw [if_neg hi, show Nat.blt p 4 = false from Bool.eq_false_iff.2 (fun h => hi (by simpa using h))]

theorem mtB_eqF (P : Nat → Nat) (i j : Nat) : mtB P i j = mtBF P i j := by
  unfold mtB mtBF
  show _ = Bool.rec (motive := fun _ => Nat) 0
    (pg 8 (mask 8) (P ((256 * i + j) / 256)) ((256 * i + j) % 256)) (Nat.blt (256 * i + j) 65536)
  by_cases hi : 256 * i + j < 65536
  · rw [if_pos hi, show Nat.blt (256 * i + j) 65536 = true from by simpa using hi]
  · rw [if_neg hi, show Nat.blt (256 * i + j) 65536 = false from
      Bool.eq_false_iff.2 (fun h => hi (by simpa using h))]

theorem natBeq_eqF (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem boolBeq_eqF (a b : Bool) : (a == b) = bEqB a b := by
  cases a <;> cases b <;> rfl

@[expose] noncomputable def tabKF : Bool :=
  (allBelow 256 fun i => invT i < 256 && mtT i (invT i) == 0) &&
  (allBelow 256 fun i => labT i < 4) &&
  (allBelow 4 fun p => rsT p < 256 && labT (rsT p) == p) &&
  labT 0 == 0 &&
  (allBelow 256 fun i => allBelow 256 fun j =>
    bEqB (Nat.beq (vBF (B45A 2) i) (vBF (B45A 2) j))
      (Nat.beq (vBF (B45A 4) (mtBF MTR (vBF (B45A 0) i) j)) 1)) &&
  (allBelow 256 fun i => allBelow 256 fun j =>
    Nat.beq (vBF (B45A 2) (mtBF MTR i j))
      (vBF (B45A 2) (mtBF MTR (rsBF (B45A 3) (vBF (B45A 2) i)) (rsBF (B45A 3) (vBF (B45A 2) j)))))

theorem tabK_eqF : tabK = tabKF := by
  unfold tabKF tabK labT isUT mtT invT laddT rsT uB laddB
  simp only [natBeq_eqF, boolBeq_eqF, vB_eqF, mtB_eqF, rsB_eqF]

theorem k_tabF : tabKF = true := by decide +kernel

theorem k_tab : tabK = true := by
  rw [tabK_eqF]
  exact k_tabF

theorem k_fb7 : fb7Check mtT isUT = true := by decide +kernel

theorem k_grp : grpOK mtT invT laddT = true := by decide +kernel

theorem k_orb : orbOK mtT invT labT crT cgT = true := by decide +kernel

theorem k_neg : ((List.range 256).all fun i => labT i == 0) = false := by decide +kernel

end CertificateChecks.KernelSeitz

end
