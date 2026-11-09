module

public import Certificates.Kernel.MatCert.HN11.Steps
public import Certificates.Kernel.MatCert.HN11.Tabs
public import Certificates.Data.Kernel.LocalComp.FactsV
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData7
import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMC.HN11

open CFSG.KC.LocalComp.FactsV CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.KD.MC.HN11 (lay V P N)

open CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native in
theorem replay_app (c : CFSG.KC.LQT.Lay) (V P T : Nat → Nat) (N : Nat) :
    ∀ (l₁ l₂ : List Op) (s : Nat) (R : List Nat), replayK c V P T N (l₁ ++ l₂) s R =
      ((replayK c V P T N l₁ s R).1 &&
        (replayK c V P T N l₂ (s + l₁.length) (replayK c V P T N l₁ s R).2).1,
        (replayK c V P T N l₂ (s + l₁.length) (replayK c V P T N l₁ s R).2).2)
  | [], l₂, s, R => by simp [replayK]
  | o :: l₁, l₂, s, R => by
    have e : s + (l₁.length + 1) = s + 1 + l₁.length := by omega
    cases o <;> simp only [List.cons_append, replayK, replay_app c V P T N l₁ l₂, List.length_cons,
      e, Bool.and_assoc]

open CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native in
theorem replay_len (c : CFSG.KC.LQT.Lay) (V P T : Nat → Nat) (N : Nat) :
    ∀ (l : List Op) (s : Nat) (R : List Nat), (replayK c V P T N l s R).2.length = R.length
  | [], _, _ => rfl
  | .mul _ _ k :: l, s, R => by
    simp only [replayK]
    rw [replay_len c V P T N l (s + 1), List.length_set]
  | .pow _ _ k :: l, s, R => by
    simp only [replayK]
    rw [replay_len c V P T N l (s + 1), List.length_set]

theorem listIs_eq (Rf : Nat → Nat) :
    ∀ (l : List Nat) (i : Nat), listIs Rf l i = true → l = (List.range' i l.length).map Rf
  | [], _, _ => rfl
  | a :: l, i, h => by
    simp only [listIs, Bool.and_eq_true, Nat.beq_eq] at h
    rw [List.length_cons, List.range'_succ, List.map_cons, ← listIs_eq Rf l (i + 1) h.2, h.1]

theorem listIs_map (Rf : Nat → Nat) :
    ∀ (m i : Nat), listIs Rf ((List.range' i m).map Rf) i = true
  | 0, _ => rfl
  | m + 1, i => by
    simp only [List.range'_succ, List.map_cons, listIs, Nat.beq_refl, Bool.true_and]
    exact listIs_map Rf m (i + 1)

@[expose] noncomputable def RQ (j r : Nat) : Nat :=
  if j = 0 then (if r = 0 then 0 else if r = 1 then 1 else 2) else if j = 24 then RF r
  else CFSG.KC.LocalComp.FactsV.fld (SN j) r

@[expose] noncomputable def RS (j : Nat) : List Nat := (List.range hn_11_claims.nregs).map (RQ j)

@[expose] noncomputable def chkR (i : Nat) : Bool :=
  let r := CFSG.KC.LocalComp.Replay.replayK lay V P TT N ((hn_11_claims.prog.drop (i * 100)).take 100)
    (i * 100) (RS i)
  r.1 && listIs (RQ (i + 1)) r.2 0

theorem regs_pre : (decide (N ≤ 1048576) && decide (2 ≤ hn_11_claims.nregs) &&
    hn_11_claims.prog.all (CFSG.SectionRank.Native.Op.lt hn_11_claims.nregs)) = true := by
  quickRfl

theorem plen : 2300 ≤ hn_11_claims.prog.length ∧ hn_11_claims.prog.length ≤ 24 * 100 := by
  decide +kernel

end CertificateChecks.KernelMC.HN11

#kc_each CertificateChecks.KernelMC.HN11.chkR 0 24

namespace CertificateChecks.KernelMC.HN11

open CFSG.KC.LocalComp.FactsV CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.KD.MC.HN11 (lay V P N)

theorem chkR_all : ∀ i < 24, chkR i = true := by
  intro i hi
  match i, hi with
  | 0, _ => exact chkR0 | 1, _ => exact chkR1 | 2, _ => exact chkR2 | 3, _ => exact chkR3
  | 4, _ => exact chkR4 | 5, _ => exact chkR5 | 6, _ => exact chkR6 | 7, _ => exact chkR7
  | 8, _ => exact chkR8 | 9, _ => exact chkR9 | 10, _ => exact chkR10 | 11, _ => exact chkR11
  | 12, _ => exact chkR12 | 13, _ => exact chkR13 | 14, _ => exact chkR14
  | 15, _ => exact chkR15 | 16, _ => exact chkR16 | 17, _ => exact chkR17
  | 18, _ => exact chkR18 | 19, _ => exact chkR19 | 20, _ => exact chkR20
  | 21, _ => exact chkR21 | 22, _ => exact chkR22 | 23, _ => exact chkR23
  | _ + 24, h => exact absurd h (by omega)

theorem replay_chain : ∀ j ≤ 24, CFSG.KC.LocalComp.Replay.replayK lay V P TT N
    (hn_11_claims.prog.take (j * 100)) 0 (RS 0) = (true, RS j)
  | 0, _ => rfl
  | j + 1, hj => by
    have h := chkR_all j (by omega)
    unfold chkR at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have e2 := listIs_eq _ _ _ h2
    have hlen : (RS j).length = hn_11_claims.nregs := by simp [RS]
    rw [replay_len, hlen, ← List.range_eq_range'] at e2
    have hl : (hn_11_claims.prog.take (j * 100)).length = j * 100 := by
      rw [List.length_take]
      have := plen.1
      omega
    rw [Nat.add_mul, Nat.one_mul, List.take_add, replay_app, replay_chain j (by omega), hl,
      Nat.zero_add]
    simp only [h1, Bool.true_and, e2]
    rfl

theorem regs_K : regsV lay V P TT N hn_11_claims.nregs hn_11_claims.prog RF = true := by
  have e0 : initK hn_11_claims.nregs = RS 0 := rfl
  have e24 : RQ 24 = RF := by
    funext r
    simp [RQ]
  simp only [regsV]
  rw [e0, ← List.take_of_length_le plen.2, replay_chain 24 le_rfl, List.take_of_length_le plen.2,
    regs_pre, RS, e24, List.range_eq_range']
  simp only [Bool.true_and]
  exact listIs_map RF _ 0

@[expose] noncomputable def chk (i : Nat) : Bool :=
  chunkV lay V P N RF hn_11_claims.nregs hn_11_claims.facts HH (fun _ => true) 128 i

theorem nfacts : hn_11_claims.facts.length ≤ 28 * 128 := by decide +kernel

end CertificateChecks.KernelMC.HN11

#kc_each CertificateChecks.KernelMC.HN11.chk 0 28

namespace CertificateChecks.KernelMC.HN11

open CFSG.KC.LocalComp.FactsV CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.KD.MC.HN11 (lay V P N)

theorem neg_regs : Bool.not (regsV lay V P (fun s => TT (s + 1)) N hn_11_claims.nregs
    hn_11_claims.prog RF) = true := by quickRfl

theorem neg_facts : Bool.not (chunkV lay V P N RF hn_11_claims.nregs hn_11_claims.facts
    (fun i => HH (i + 1)) (fun _ => true) 256 0) = true := by quickRfl

end CertificateChecks.KernelMC.HN11

end
