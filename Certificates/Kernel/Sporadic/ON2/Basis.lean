module

public import Certificates.Kernel.Sporadic.ON2.Checks
public import Certificates.Kernel.Sporadic.ON2.MVData
public import Certificates.Data.Kernel.ON.BasisLit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.ONLaneSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONF CFSG.Sporadic.ON.Native CFSG.Sporadic.ON.Kernel

@[expose] noncomputable def XL : List Nat := basisXPairs.map fun r => vmk r.1 r.2

@[expose] noncomputable def RbL : List Nat := (List.range 154).map fun t => key ONW.K (cq t)

@[expose] noncomputable def CO (c : Nat) : Nat := mv XL (key ONW.K c)

open CFSG.KS.ONLane in
@[expose] noncomputable def on2Lmv (L : List Nat) (xp xm : Nat) : Nat := mvLW 154 (oneL 154) L 0 xp xm 0 0

@[expose] noncomputable def on2LidL : List Nat := (List.range 154).map (2 ^ ·)

@[expose] noncomputable def on2LaP : List Nat := (List.range 154).map fun j => vP (ONW.CA j)
@[expose] noncomputable def on2LaM : List Nat := (List.range 154).map fun j => vM (ONW.CA j)
@[expose] noncomputable def on2LbP : List Nat := (List.range 154).map fun j => vP (ONW.CB j)
@[expose] noncomputable def on2LbM : List Nat := (List.range 154).map fun j => vM (ONW.CB j)

open CFSG.KS.ONLane in
@[expose] noncomputable def on2Lit (L : List Nat) (xp xm : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.lor xp (Nat.shiftLeft xm (256 * 154))) fun _ ih =>
    on2Lmv L (ih % 2 ^ (256 * 154)) (ih >>> (256 * 154))

open CFSG.KS.ONLane in
theorem on2Lid : ltAll (2 ^ 256) on2LidL = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LaPb : ltAll (2 ^ 256) on2LaP = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LaMb : ltAll (2 ^ 256) on2LaM = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LbPb : ltAll (2 ^ 256) on2LbP = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LbMb : ltAll (2 ^ 256) on2LbM = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LcA : ltAll (2 ^ 256) (ONW.LA.map vM) = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LcB : ltAll (2 ^ 256) (ONW.LB.map vM) = true := by quickRfl
theorem on2LlA : Nat.beq ONW.LA.length 154 = true := by quickRfl
theorem on2LlB : Nat.beq ONW.LB.length 154 = true := by quickRfl

open CFSG.KS.ONLane in
theorem on2LdA : Nat.beq (Nat.land (packL on2LaP) (packL on2LaM)) 0 = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LdB : Nat.beq (Nat.land (packL on2LbP) (packL on2LbM)) 0 = true := by quickRfl
open CFSG.KS.ONLane in
theorem on2LA : Nat.beq (on2Lmv ONW.LA (packL on2LaP) (packL on2LaM)) (packL on2LidL) = true := by
  quickRfl
open CFSG.KS.ONLane in
@[expose] noncomputable def on2LX (k : Nat) : Nat := on2Lit ONW.LB (packL on2LbP) (packL on2LbM) k

theorem on2LB1 : Nat.beq (Nat.land (on2LX 1 % 2 ^ (256 * 154)) (on2LX 1 >>> (256 * 154))) 0 = true := by quickRfl
theorem on2LB2 : Nat.beq (Nat.land (on2LX 2 % 2 ^ (256 * 154)) (on2LX 2 >>> (256 * 154))) 0 = true := by quickRfl
theorem on2LB3 : Nat.beq (on2LX 3) (CFSG.KS.ONLane.packL on2LidL) = true := by quickRfl

theorem mv_eq_mvL (L : List Nat) (x : Nat) : mv L x = mvL L (vP x) (vM x) 0 0 := by
  unfold mv
  rw [CFSG.KS.PackFld.strictN_eqP, CFSG.KS.PackFld.strictN_eqP]

open CFSG.KS.ONLane in
theorem on2L_step {L : List Nat} (hL : L.length ≤ 256) (hc : ltAll (2 ^ 256) (L.map vM) = true)
    {R : Nat} (hd : Nat.land (R % 2 ^ (256 * 154)) (R >>> (256 * 154)) = 0) {j : Nat} (hj : j < 154) :
    mv L (vmk (laneOf j (R % 2 ^ (256 * 154))) (laneOf j (R >>> (256 * 154)))) =
      vmk (laneOf j (on2Lmv L (R % 2 ^ (256 * 154)) (R >>> (256 * 154)) % 2 ^ (256 * 154)))
        (laneOf j (on2Lmv L (R % 2 ^ (256 * 154)) (R >>> (256 * 154)) >>> (256 * 154))) := by
  rw [mv_eq_mvL, vP_vmk (laneOf_lt _ _), vM_vmk (laneOf_lt _ _)]
  exact mvLW_halves (n := 154) hL hd hc j hj

theorem on2L_id {j : Nat} (hj : j < 154)
    (h : CFSG.KS.ONLane.ltAll (2 ^ 256) on2LidL = true) {R : Nat}
    (hR : R = CFSG.KS.ONLane.packL on2LidL) :
    vmk (CFSG.KS.ONLane.laneOf j (R % 2 ^ (256 * 154))) (CFSG.KS.ONLane.laneOf j (R >>> (256 * 154))) =
      vmk (Nat.pow 2 j) 0 := by
  obtain ⟨h1, _⟩ := CFSG.KS.ONLane.packL_spec on2LidL
    fun x hx => CFSG.KS.ONLane.ltAll_spec h x hx
  have hl : on2LidL.length = 154 := by simp [on2LidL]
  rw [hl] at h1
  subst hR
  rw [Nat.mod_eq_of_lt h1, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h1,
    CFSG.KS.ONLane.laneOf_zero]
  unfold on2LidL
  rw [CFSG.KS.ONLane.laneOf_packL_range (by exact h) hj]
  rfl

theorem matA : allN 154 (fun j => Nat.beq (mv ONW.LA (ONW.CA j)) (vmk (Nat.pow 2 j) 0)) = true := by
  refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
  have e : mv ONW.LA (ONW.CA j) = vmk (Nat.pow 2 j) 0 := by
    rw [mv_eq_mvL, ← CFSG.KS.ONLane.laneOf_packL_range (f := fun j => vP (ONW.CA j)) on2LaPb hj,
      ← CFSG.KS.ONLane.laneOf_packL_range (f := fun j => vM (ONW.CA j)) on2LaMb hj]
    exact (CFSG.KS.ONLane.mvLW_halves (n := 154) (by rw [Nat.eq_of_beq_eq_true on2LlA]; omega)
        (Nat.eq_of_beq_eq_true on2LdA) on2LcA j hj).trans
      (on2L_id hj on2Lid (Nat.eq_of_beq_eq_true on2LA))
  rw [e]
  exact Nat.beq_refl _

set_option exponentiation.threshold 40000 in
theorem matB : allN 154 (fun j => Nat.beq (mv ONW.LB (mv ONW.LB (mv ONW.LB (ONW.CB j))))
    (vmk (Nat.pow 2 j) 0)) = true := by
  have hL : ONW.LB.length ≤ 256 := by
    rw [Nat.eq_of_beq_eq_true on2LlB]
    omega
  refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
  have h1 := (CFSG.KS.ONLane.packL_spec on2LbP fun x hx =>
    CFSG.KS.ONLane.ltAll_spec on2LbPb x hx).1
  have hl : on2LbP.length = 154 := by simp [on2LbP]
  rw [hl] at h1
  have hp : on2LX 0 % 2 ^ (256 * 154) = CFSG.KS.ONLane.packL on2LbP ∧
      on2LX 0 >>> (256 * 154) = CFSG.KS.ONLane.packL on2LbM := by
    have e0 : on2LX 0 = Nat.lor (CFSG.KS.ONLane.packL on2LbP)
        (Nat.shiftLeft (CFSG.KS.ONLane.packL on2LbM) (256 * 154)) := rfl
    rw [e0]
    exact CFSG.KS.ONLane.halves_lor (s := 256 * 154) (P := CFSG.KS.ONLane.packL on2LbP)
      (M := CFSG.KS.ONLane.packL on2LbM) h1
  have e1 : mv ONW.LB (ONW.CB j) = vmk (CFSG.KS.ONLane.laneOf j (on2LX 1 % 2 ^ (256 * 154)))
      (CFSG.KS.ONLane.laneOf j (on2LX 1 >>> (256 * 154))) := by
    have ex : on2LX 1 = on2Lmv ONW.LB (on2LX 0 % 2 ^ (256 * 154)) (on2LX 0 >>> (256 * 154)) := rfl
    rw [ex, hp.1, hp.2, mv_eq_mvL,
      ← CFSG.KS.ONLane.laneOf_packL_range (f := fun j => vP (ONW.CB j)) on2LbPb hj,
      ← CFSG.KS.ONLane.laneOf_packL_range (f := fun j => vM (ONW.CB j)) on2LbMb hj]
    exact CFSG.KS.ONLane.mvLW_halves (n := 154) hL (Nat.eq_of_beq_eq_true on2LdB) on2LcB j hj
  have e2 : on2Lmv ONW.LB (on2LX 1 % 2 ^ (256 * 154)) (on2LX 1 >>> (256 * 154)) = on2LX 2 := rfl
  have e3 : on2Lmv ONW.LB (on2LX 2 % 2 ^ (256 * 154)) (on2LX 2 >>> (256 * 154)) = on2LX 3 := rfl
  rw [e1, on2L_step hL on2LcB (Nat.eq_of_beq_eq_true on2LB1) hj, e2,
    on2L_step hL on2LcB (Nat.eq_of_beq_eq_true on2LB2) hj, e3,
    on2L_id hj on2Lid (Nat.eq_of_beq_eq_true on2LB3)]
  exact Nat.beq_refl _

@[expose] noncomputable def basisPS : List Nat := basisXPairs.map Prod.fst

@[expose] noncomputable def basisMS : List Nat := basisXPairs.map Prod.snd

@[expose] noncomputable def fBR (k : Nat) : Bool := bAnd(canon (List.getD XL k 0),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).1 (Nat.pow 2 154),
    Nat.blt (List.getD basisXPairs k (0, 0)).2 (Nat.pow 2 154)))

theorem on2LRows : allN 154 fBR = true := by quickRfl
theorem lenRb : Nat.beq RbL.length 154 = true := by quickRfl
theorem boLaneP : CFSG.KS.ONLane.ltAll (2 ^ 256) basisPS = true := by quickRfl
theorem boLaneM : CFSG.KS.ONLane.ltAll (2 ^ 256) basisMS = true := by quickRfl
theorem boLaneR : CFSG.KS.ONLane.ltAll (2 ^ 256) (RbL.map vM) = true := by quickRfl
theorem boLaneD : Nat.beq (Nat.land (CFSG.KS.ONLane.packL basisPS) (CFSG.KS.ONLane.packL basisMS)) 0 =
    true := by quickRfl
theorem boLaneX : Nat.beq (CFSG.KS.ONLane.mvLW 154 (CFSG.KS.ONLane.oneL 154) RbL 0
    (CFSG.KS.ONLane.packL basisPS) (CFSG.KS.ONLane.packL basisMS) 0 0)
    (CFSG.KS.ONLane.packL ((List.range 154).map (2 ^ ·))) = true := by quickRfl

private theorem getD_map' {α β : Type} (f : α → β) (l : List α) (d : α) (k : Nat) :
    (l.map f).getD k (f d) = f (l.getD k d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

theorem basisOK : allN 154 (fun k => bAnd(canon (List.getD XL k 0),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).1 (Nat.pow 2 154),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).2 (Nat.pow 2 154),
    Nat.beq (mv RbL (List.getD XL k 0)) (vmk (Nat.pow 2 k) 0))))) = true := by
  have hlr : RbL.length = 154 := Nat.eq_of_beq_eq_true lenRb
  have hmv := CFSG.KS.ONLane.mvL_of_lanes (by omega) (by omega) boLaneP boLaneM
    (Nat.eq_of_beq_eq_true boLaneD) boLaneR (Nat.eq_of_beq_eq_true boLaneX)
  have hr := allN_spec on2LRows
  refine CFSG.KS.PackFld.allN_of_forall fun k hk => ?_
  obtain ⟨h0, h1⟩ := (bAnd_iff _ _).1 (hr k hk)
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h1
  refine (bAnd_iff _ _).2 ⟨h0, (bAnd_iff _ _).2 ⟨h1, (bAnd_iff _ _).2 ⟨h2, ?_⟩⟩⟩
  have hp : (List.getD basisXPairs k (0, 0)).1 < 2 ^ 256 :=
    Nat.lt_trans (Nat.le_of_ble_eq_true h1) (Nat.pow_lt_pow_right (by omega) (by omega))
  have e0 : vmk 0 0 = 0 := by
    unfold vmk
    change (0 : Nat) ||| 0 <<< 256 = 0
    simp
  have eX : List.getD XL k 0 = vmk (List.getD basisXPairs k (0, 0)).1
      (List.getD basisXPairs k (0, 0)).2 := by
    have := getD_map' (fun r : Nat × Nat => vmk r.1 r.2) basisXPairs (0, 0) k
    dsimp only at this
    rw [e0] at this
    exact this
  have eP : basisPS.getD k 0 = (List.getD basisXPairs k (0, 0)).1 :=
    getD_map' Prod.fst basisXPairs (0, 0) k
  have eM : basisMS.getD k 0 = (List.getD basisXPairs k (0, 0)).2 :=
    getD_map' Prod.snd basisXPairs (0, 0) k
  have hm := hmv k hk
  rw [eP, eM] at hm
  have e2 : mv RbL (List.getD XL k 0) = vmk (Nat.pow 2 k) 0 := by
    rw [eX]
    unfold mv
    rw [CFSG.KS.PackFld.strictN_eqP, CFSG.KS.PackFld.strictN_eqP, vP_vmk hp, vM_vmk hp]
    exact hm
  rw [e2]
  exact Nat.beq_refl _

theorem lensOK : bAnd(Nat.beq (List.length XL) 154, Nat.beq (List.length RbL) 154) = true := by quickRfl

theorem supOK : allN 7 (fun s => strictB (checkVecs[s]!) fun c => bAnd(Nat.blt c 245520,
    bAnd(canon (CO c), bAnd(Nat.beq (mv RbL (CO c)) (key ONW.K c),
    bIf(bit (vP (CO c)) 0, true, bit (vM (CO c)) 0))))) = true := by
  quickRfl

theorem supCover : allN 154 (fun t => Bool.not (allN 7 fun s =>
    Bool.not (bIf(bit (vP (CO (checkVecs[s]!))) t, true, bit (vM (CO (checkVecs[s]!))) t)))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ON2

end
