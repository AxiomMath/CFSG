module

public import Certificates.Kernel.RuFive.Defs
public import Certificates.Kernel.Misc.RuInv.Data
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HeLoc.PTail
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Kernel.RuFive.Tab
public import Certificates.Kernel.RuFive.SLPData
public import Certificates.Data.Kernel.PermSLP
import CFSG.Certificates.Kernel.PermSLPSound
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KS.Prim

theorem kBind0 : allN 8 (fun j => Nat.beq (H50.F j) (S50.S j)) = true := by quickRfl

theorem kBind1 : allN 10 (fun j => Nat.beq (H51.F j) (S51.S j)) = true := by quickRfl

theorem kPerm0 : allN 8 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (S50.S j) (S50.SI j)) =
    true := by quickRfl

theorem kPerm1 : allN 10 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (S51.S j) (S51.SI j)) =
    true := by quickRfl

theorem kGen00 : Nat.beq (S50.S 0) CertificateChecks.KernelMisc.RuInv.AD.n0 = true := by quickRfl

theorem kGen01 : Nat.beq (S50.S 1) CertificateChecks.KernelMisc.RuInv.AD.n1 = true := by quickRfl

theorem kGen10 : Nat.beq (S51.S 0) CertificateChecks.KernelMisc.RuInv.AD.n0 = true := by quickRfl

theorem kGen11 : Nat.beq (S51.S 1) CertificateChecks.KernelMisc.RuInv.AD.n1 = true := by quickRfl

theorem kBase0 : allN 9 (fun t => Nat.beq CFSG.RankThree.PartOne.ruCase0BaseArr[t]!
    (pg 12 (mask 12) S50.BP t)) = true := by quickRfl

theorem kBase1 : allN 5 (fun t => Nat.beq CFSG.RankThree.PartOne.ruCase1BaseArr[t]!
    (pg 12 (mask 12) S51.BP t)) = true := by quickRfl

theorem kOrb0 : allN 9 (fun i => Nat.beq (rcnt (S50.LR i))
    ([4060, 1755, 1024, 4, 5, 1, 1, 1, 1].getD i 0)) = true := by quickRfl

theorem kOrb1 : allN 5 (fun i => Nat.beq (rcnt (S51.LR i)) ([4060, 1755, 1024, 20, 1].getD i 0)) =
    true := by quickRfl

theorem kPermF : allN 75 (fun k => permOK 4060 12 (mask 12) (4060 * 12) (F k) (AI k)) = true := by
  quickRfl

@[expose] noncomputable def SL (j : Nat) : Nat := S50.S (Nat.land j 7)

@[expose] noncomputable def SLI (j : Nat) : Nat := S50.SI (Nat.land j 7)

@[expose] noncomputable def ruleB (c : Nat) : Bool :=
  allN 8 fun i => bIf(Nat.blt (Nat.add (Nat.mul 8 c) i) 381,
    CFSG.KC.PermSLP.ruleK 4060 12 16 SL SLI PRV PRG (Nat.add (Nat.mul 8 c) i), true)

@[expose] noncomputable def topV (k : Nat) : Bool :=
  bAnd(CFSG.KC.PermSLP.topK 16 381 397 PRG (PRT k) (wd k),
    Nat.beq (CFSG.KC.PermSLP.symV 16 SL SLI PRV (PRT k)) (F k))

end CertificateChecks.KernelRuFive

#kss_each CertificateChecks.KernelRuFive.RB CertificateChecks.KernelRuFive.ruleB 48

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KS.Prim

theorem kSz : szOK 4060 12 = true := by quickRfl

theorem kCnS : allN 8 (fun j => bAnd(canonK 4060 12 (mask 12) (4060 * 12) (S50.S j),
    canonK 4060 12 (mask 12) (4060 * 12) (S50.SI j))) = true := by quickRfl

theorem kCnId : canonK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) = true := by quickRfl

theorem kLet : allN 16 (fun s => CFSG.KC.PermSLP.letK 4060 12 16 SL SLI PRV s) = true := by
  quickRfl

theorem kLW : allN 75 (fun k => lettersK 8 (wd k)) = true := by quickRfl

theorem kTopA : allN 33 topV = true := by quickRfl

theorem kTopB : allN 40 (fun k => topV (Nat.add 35 k)) = true := by quickRfl

theorem kW33 : wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd 33) (F 33) = true := by
  quickRfl

theorem kW34 : wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd 34) (F 34) = true := by
  quickRfl

theorem sl_canon (j : Nat) : canonK 4060 12 (mask 12) (4060 * 12) (SL j) = true ∧
    canonK 4060 12 (mask 12) (4060 * 12) (SLI j) = true := by
  have hj : Nat.land j 7 < 8 := Nat.lt_succ_of_le Nat.and_le_right
  have h := CFSG.KS.PK.allN_iff.1 kCnS _ hj
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem rule_k (k : Nat) (hk : k < 381) :
    CFSG.KC.PermSLP.ruleK 4060 12 16 SL SLI PRV PRG k = true := by
  have hc : k / 8 < 48 := by omega
  have h : ruleB (k / 8) = true := RB.all _ hc
  unfold ruleB at h
  have h2 := CFSG.KS.PK.allN_iff.1 h (k % 8) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 8 (k / 8)) (k % 8) = k := Nat.div_add_mod k 8
  simp only [e] at h2
  rw [Nat.blt_eq.mpr hk] at h2
  exact h2

theorem wordK_SL : ∀ u : List Int, lettersK 8 u = true →
    wordK 4060 12 (mask 12) (pidn 4060 12) SL SLI u =
      wordK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI u
  | [], _ => rfl
  | z :: u, h => by
    have h' : strictB (CFSG.KS.Mathieu.icode z) (fun c => bAnd(Nat.blt (nat_lit 0) c,
        bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) 8, lettersK 8 u))) = true := h
    rw [CFSG.KS.PK.strictB_eq, CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true,
      Bool.and_eq_true] at h'
    obtain ⟨-, h2, h3⟩ := h'
    rw [CFSG.KC.PermTool.wordK_cons, CFSG.KC.PermTool.wordK_cons]
    simp only [CFSG.KS.PK.strictN_eq]
    rw [wordK_SL u h3]
    have hs := Nat.ble_eq.mp h2
    unfold SL SLI
    generalize Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1) = s at hs ⊢
    have hq : s - 1 < 8 := by omega
    have hi : Nat.land (Nat.sub s (nat_lit 1)) 7 = Nat.sub s (nat_lit 1) := by
      change (s - 1) &&& (2 ^ 3 - 1) = s - 1
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt hq
    rw [hi]

theorem kWord (k : Nat) (hk : k < 75) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd k) (F k) = true := by
  by_cases h33 : k = 33
  · subst h33
    exact kW33
  by_cases h34 : k = 34
  · subst h34
    exact kW34
  have ht : topV k = true := by
    rcases Nat.lt_or_ge k 33 with h | h
    · exact CFSG.KS.PK.allN_iff.1 kTopA k h
    · have h' := CFSG.KS.PK.allN_iff.1 kTopB (k - 35) (by omega)
      have e : Nat.add 35 (k - 35) = k := by
        change 35 + (k - 35) = k
        omega
      rw [e] at h'
      exact h'
  unfold topV at ht
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at ht
  obtain ⟨htop, hval⟩ := ht
  have hl := CFSG.KS.PK.allN_iff.1 kLW k hk
  have hw := CFSG.KC.PermSLP.slp_word (n := 4060) (w := 12) (S := SL) (SI := SLI)
    (nL := 16) (R := 381) (f := 397) (t := PRT k) (V := PRV) (G := PRG) (wd := wd k)
    (fun j => (sl_canon j).1) (fun j => (sl_canon j).2) kCnId
    (CFSG.KS.PK.allN_iff.1 kLet) rule_k (by decide) htop
  rw [wordK_SL _ hl] at hw
  unfold wordEqK
  rw [CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, hw]
  exact ⟨kSz, hl, hval⟩

theorem kQN : Nat.beq Q.N 125 = true := by quickRfl

theorem kQTree : allN 125 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 Q.P Q.L i)) = true := by
  quickRfl

theorem kQReplay : CFSG.KC.Bfs.replayOK QE 2 125 = true := by quickRfl

theorem kQEdge : allN 125 (edgeAtK gQ q0 Q.P Q.L QE 125 125 2 bs) = true := by quickRfl

theorem kQSort : allN 125 (sortAtK qkey Q.SK Q.SKI 125) = true := by quickRfl

theorem kQPow : allN 125 (fun i => eqOnL bs (powF (qv i) 5) (fun x => x)) = true := by quickRfl

theorem kCover : allN 125 coverAt = true := by quickRfl

theorem kDist : allN 31 (fun j => allN 31 (distAt j)) = true := by quickRfl

theorem kLine : allN 31 lineAt = true := by quickRfl

theorem kTrans : allN 31 transAt = true := by quickRfl

theorem kOrbNeg : (!allN 9 (fun i => Nat.beq (rcnt (S50.LR i))
    ([4060, 1755, 1024, 4, 5, 1, 1, 1, 2].getD i 0))) = true := by quickRfl

theorem kWordNeg : (!wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd 0) (F 1)) = true := by
  quickRfl

theorem kDistNeg : (!distAt 1 1 || distAt 0 1) = true := by quickRfl

end CertificateChecks.KernelRuFive

end
