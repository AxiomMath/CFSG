module

public import Certificates.Kernel.SporSch.Ly.SevCData
public import Certificates.Kernel.SporSch.Ly.GenSevF
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Lean
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.SporSch.LySevBfs
import CFSG.Certificates.Kernel.SporSch.LySevMat
import CFSG.Certificates.Kernel.SporSch.LySevCbfs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySc

open Lean CFSG.KC.Eval in
meta def cmpStep : Step := fun _ => do
  let mut outs : Array (Name × Val) :=
    #[(`M7, .nat ((List.range 256).foldl (fun acc t => acc ||| (7 <<< (20 * t))) 0))]
  for r in [0:8] do
    let W := 20 * 2 ^ r
    let c := 3 * 2 ^ r
    let ev := (List.range (256 / 2 ^ r)).foldl (fun acc k =>
      if k % 2 == 0 then acc ||| ((2 ^ c - 1) <<< (W * k)) else acc) 0
    outs := outs.push (Name.mkSimple s!"E{r}", .nat ev)
    outs := outs.push (Name.mkSimple s!"O{r}", .nat (ev <<< W))
  return outs

end CertificateChecks.KernelSporSch.LySc

#kc_eval CertificateChecks.KernelSporSch.LySc cm CertificateChecks.KernelSporSch.LySc.cmpStep

namespace CertificateChecks.KernelSporSch.LySc

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev

@[expose] noncomputable def cmRnd (E O s X : Nat) : Nat :=
  Nat.lor (Nat.land X E) (Nat.shiftRight (Nat.land X O) s)

@[expose] noncomputable def cmpL (Y : Nat) : Nat :=
  strictN (Nat.land Y cm.M7) fun X0 =>
  strictN (cmRnd cm.E0 cm.O0 (nat_lit 17) X0) fun X1 =>
  strictN (cmRnd cm.E1 cm.O1 (nat_lit 34) X1) fun X2 =>
  strictN (cmRnd cm.E2 cm.O2 (nat_lit 68) X2) fun X3 =>
  strictN (cmRnd cm.E3 cm.O3 (nat_lit 136) X3) fun X4 =>
  strictN (cmRnd cm.E4 cm.O4 (nat_lit 272) X4) fun X5 =>
  strictN (cmRnd cm.E5 cm.O5 (nat_lit 544) X5) fun X6 =>
  strictN (cmRnd cm.E6 cm.O6 (nat_lit 1088) X6) fun X7 =>
  cmRnd cm.E7 cm.O7 (nat_lit 2176) X7

@[expose] noncomputable def cStepF (ET WT PT : Nat → Nat) (c h P j cnt : Nat) : Nat :=
  strictN fld(P, Nat.mul (nat_lit 147) j, mask (nat_lit 147)) (fun y =>
    strictN fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) (fun w =>
      nIf(Nat.blt w cnt, nIf(Nat.beq (rowR ET (nat_lit 147) w) y, cnt, cFail),
        nIf(bAnd(Nat.beq w cnt, bAnd(Nat.blt cnt c, bAnd(Nat.beq (rowR ET (nat_lit 147) cnt) y,
            Nat.beq (rowR PT (nat_lit 24) cnt) (Nat.add h (Nat.shiftLeft j (nat_lit 19)))))),
          Nat.succ cnt, cFail))))

@[expose] noncomputable def cRunF (KC : Nat → Nat) (QM : Nat) (ET WT PT : Nat → Nat)
    (kg c h₀ len cnt : Nat) : Nat :=
  foldUp len (fun i cnt => strictN (Nat.add h₀ i) (fun h => nIf(Nat.blt h cnt,
    strictN (cmpL (imgs KC QM (rowR ET (nat_lit 147) h))) (fun P =>
      foldUp kg (fun j cnt => cStepF ET WT PT c h P j cnt) cnt),
    cnt))) cnt

@[expose] noncomputable def crF (q : Nat) : Bool :=
  bIf(Nat.blt q nS, Nat.beq (cRunF KC QM ET WT PT 5 c (Nat.mul q 32) 32 (C q)) (C (Nat.succ q)), true)

@[expose] noncomputable def cmBad : Nat := 1048576

@[expose] noncomputable def cmTr (E O s i : Nat) : Nat :=
  bif Nat.beq i cmBad then cmBad else
  bif Nat.testBit E i then (bif Nat.testBit O (s + i) then cmBad else i)
  else (bif Nat.testBit O (s + i) then s + i else cmBad)

@[expose] noncomputable def cmFin (p : Nat) : Nat := bif Nat.testBit cm.M7 p then p else cmBad

@[expose] noncomputable def cmTrAll (i : Nat) : Nat :=
  cmFin (cmTr cm.E0 cm.O0 (nat_lit 17) (cmTr cm.E1 cm.O1 (nat_lit 34)
    (cmTr cm.E2 cm.O2 (nat_lit 68) (cmTr cm.E3 cm.O3 (nat_lit 136)
    (cmTr cm.E4 cm.O4 (nat_lit 272) (cmTr cm.E5 cm.O5 (nat_lit 544)
    (cmTr cm.E6 cm.O6 (nat_lit 1088) (cmTr cm.E7 cm.O7 (nat_lit 2176) i))))))))

theorem cmTrOK :
    (List.range 768).all (fun i => Nat.beq (cmTrAll i) (20 * (i / 3) + i % 3)) = true := by
  decide +kernel

theorem cmRnd_bit (E O s X i : Nat) : Nat.testBit (cmRnd E O s X) i =
    (Nat.testBit X i && Nat.testBit E i || Nat.testBit X (s + i) && Nat.testBit O (s + i)) := by
  change ((X &&& E) ||| ((X &&& O) >>> s)).testBit i = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight]

theorem cmTr_bad (E O s : Nat) : cmTr E O s cmBad = cmBad := by
  unfold cmTr
  simp

theorem cmTr_ne {E O s i : Nat} (h : cmTr E O s i ≠ cmBad) : i ≠ cmBad :=
  fun e => h (by rw [e]; exact cmTr_bad E O s)

theorem cmTr_spec {E O s i X : Nat} (h : cmTr E O s i ≠ cmBad) :
    Nat.testBit (cmRnd E O s X) i = Nat.testBit X (cmTr E O s i) := by
  rw [cmRnd_bit]
  unfold cmTr at h ⊢
  cases hb : Nat.beq i cmBad <;> cases hE : Nat.testBit E i <;>
    cases hO : Nat.testBit O (s + i) <;> simp_all

theorem cmFin_ne {p : Nat} (h : cmFin p ≠ cmBad) : p ≠ cmBad := by
  intro e
  apply h
  unfold cmFin
  rw [e]
  cases Nat.testBit cm.M7 cmBad <;> rfl

theorem cmFin_spec {p Y : Nat} (h : cmFin p ≠ cmBad) :
    Nat.testBit (Nat.land Y cm.M7) p = Nat.testBit Y (cmFin p) := by
  change (Y &&& cm.M7).testBit p = _
  rw [Nat.testBit_and]
  unfold cmFin at h ⊢
  cases hM : Nat.testBit cm.M7 p <;> simp_all

theorem cmpL_bit (Y i : Nat) (h : cmTrAll i ≠ cmBad) :
    Nat.testBit (cmpL Y) i = Nat.testBit Y (cmTrAll i) := by
  unfold cmpL
  simp only [CFSG.KS.SporSch.LyLoop.strictN_eqP]
  unfold cmTrAll at h ⊢
  have h0 := cmFin_ne h
  have h1 := cmTr_ne h0
  have h2 := cmTr_ne h1
  have h3 := cmTr_ne h2
  have h4 := cmTr_ne h3
  have h5 := cmTr_ne h4
  have h6 := cmTr_ne h5
  have h7 := cmTr_ne h6
  rw [cmTr_spec h7, cmTr_spec h6, cmTr_spec h5, cmTr_spec h4, cmTr_spec h3, cmTr_spec h2,
    cmTr_spec h1, cmTr_spec h0, cmFin_spec h]

theorem cmp_bit (Y s q : Nat) (hs : s < 256) (hq : q < 3) :
    Nat.testBit (cmpL Y) (3 * s + q) = Nat.testBit Y (20 * s + q) := by
  have ht : cmTrAll (3 * s + q) = 20 * s + q := by
    have h : Nat.beq (cmTrAll (3 * s + q)) (20 * ((3 * s + q) / 3) + (3 * s + q) % 3) = true :=
      List.all_eq_true.1 cmTrOK (3 * s + q) (List.mem_range.2 (by omega))
    rw [Nat.beq_eq] at h
    rw [h]
    have e1 : (3 * s + q) / 3 = s := by omega
    have e2 : (3 * s + q) % 3 = q := by omega
    rw [e1, e2]
  rw [cmpL_bit Y _ (by rw [ht]; unfold cmBad; omega), ht]

theorem pack_key (Y j : Nat) (hj : j < 5) :
    fld(cmpL Y, Nat.mul (nat_lit 147) j, mask (nat_lit 147)) =
      pack49 Y (Nat.mul (nat_lit 980) j) := by
  have hlt : pack49 Y (Nat.mul 980 j) < 2 ^ 147 := by
    rw [CFSG.KS.SporSch.LySvC.pack49_place]
    exact CFSG.KS.SporSch.LySvM.placeF_lt (w := 3) 49
      (fun p _ => Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num))
      (fun p hp => by beta_reduce; omega)
  have hm : mask 147 = 2 ^ 147 - 1 := by
    unfold mask
    change 1 <<< 147 - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  apply Nat.eq_of_testBit_eq
  intro b
  change ((cmpL Y >>> (147 * j)) &&& mask 147).testBit b = _
  rw [hm, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hb : b < 147
  · simp only [hb, decide_true, Bool.and_true]
    have ht : b / 3 < 49 := by omega
    have hq : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have e1 : 147 * j + b = 3 * (49 * j + b / 3) + b % 3 := by omega
    rw [e1, cmp_bit Y _ _ (by omega) hq]
    have hd := CFSG.KS.SporSch.LySvC.d3_pack49 Y (Nat.mul 980 j) ht
    rw [CFSG.KS.SporSch.LySvB.d3_eq, CFSG.KS.SporSch.LySvC.fld7_eq] at hd
    have e8 : (8 : Nat) = 2 ^ 3 := by norm_num
    rw [e8] at hd
    have hb2 := congrArg (fun z => Nat.testBit z (b % 3)) hd
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hq, decide_true,
      Bool.true_and] at hb2
    have e2 : b % 3 + 3 * (b / 3) = b := by omega
    rw [e2] at hb2
    rw [hb2]
    congr 1
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  · simp only [hb, decide_false, Bool.and_false]
    exact (Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem cStepF_eq (ET WT PT : Nat → Nat) (c h Y j cnt : Nat) (hj : j < 5) :
    cStepF ET WT PT c h (cmpL Y) j cnt = cStep ET WT PT c h Y j cnt := by
  unfold cStepF cStep
  rw [pack_key Y j hj]

theorem cRunF_eq (KC : Nat → Nat) (QM : Nat) (ET WT PT : Nat → Nat) {kg : Nat} (hkg : kg ≤ 5)
    (c h₀ len cnt : Nat) :
    cRunF KC QM ET WT PT kg c h₀ len cnt = cRun KC QM ET WT PT kg c h₀ len cnt := by
  unfold cRunF cRun
  simp only [CFSG.KS.SporSch.LyLoop.foldUp_eqP, CFSG.KS.SporSch.LyLoop.strictN_eqP,
    CFSG.KS.SporSch.LyLoop.nIf_eqP]
  refine List.foldl_ext _ _ _ (fun cnt i _ => ?_)
  split
  · exact List.foldl_ext _ _ _ (fun cnt j hj =>
      cStepF_eq ET WT PT c _ _ j cnt (by rw [List.mem_range] at hj; omega))
  · rfl

theorem crF_imp (q : Nat) (h : crF q = true) : crQ q = true := by
  unfold crF at h
  unfold crQ
  rw [cRunF_eq KC QM ET WT PT (le_refl 5)] at h
  exact h

end CertificateChecks.KernelSporSch.LySc

end
