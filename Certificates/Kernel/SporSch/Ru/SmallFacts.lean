
module

public import Certificates.Kernel.SporSch.Ru.SmallChains
public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuLines

theorem binds1920 {f off l nb BP : Nat} {PS : Nat → Nat} {b : List Nat}
    (hs : ruLines1920.getD f (0, 0) = (off, l)) (hl : off + l ≤ 41)
    (hS : allN l (fun j => Nat.beq (PS j) (RuT1920.L (Nat.add off j))) = true)
    (hb : b.length = nb)
    (hB : allN nb (fun t => Nat.beq (ruBaseArr 1920 b)[t]! (pg 11 (mask 11) BP t)) = true) :
    Binds 1920 11 PS l nb BP (ruField1920 f) (ruBaseArr 1920 b) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, ?_,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hB t ht)⟩
  · rw [ruField1920, Array.size_ofFn, hs]
  · have e : PS j = RuT1920.L (Nat.add off j) := Nat.eq_of_beq_eq_true (allN_spec hS j hj)
    rw [RuCe.f1920 off l (off + j) hs hj rfl (by omega)]
    exact congrArg (unpack 1920 11) e.symm
  · simp [ruBaseArr, hb]

theorem binds80 {nb BP : Nat} {PS : Nat → Nat} {b : List Nat}
    (hS : allN 8 (fun j => Nat.beq (PS j) (RuT80.L j)) = true) (hb : b.length = nb)
    (hB : allN nb (fun t => Nat.beq (ruBaseArr 80 b)[t]! (pg 7 (mask 7) BP t)) = true) :
    Binds 80 7 PS 8 nb BP ruField80 (ruBaseArr 80 b) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by rw [ruField80, Array.size_ofFn],
    fun j hj => ?_, by simp [ruBaseArr, hb], fun t ht => Nat.eq_of_beq_eq_true (allN_spec hB t ht)⟩
  rw [RuCe.field80_get hj]
  exact congrArg (unpack 80 7) (Nat.eq_of_beq_eq_true (allN_spec hS j hj)).symm

theorem bindsLit {n w kS nb BP : Nat} {PS : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
    (hn : 0 < n ∧ n + 1 < 2 ^ w ∧ n < 65536)
    (hS : (Nat.beq S.size kS && allN kS fun k => bindArrK S[k]! n w (PS k)) = true)
    (hbs : base.size = nb)
    (hB : allN nb (fun t => Nat.beq base[t]! (pg w (mask w) BP t)) = true) :
    Binds n w PS kS nb BP S base :=
  ⟨hn.1, hn.2.1, hn.2.2, (binds_of_check hS).1, (binds_of_check hS).2, hbs,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hB t ht)⟩

theorem sF : allN 7 (fun j => Nat.beq (RuFS.S j) (RuT1920.L (Nat.add 0 j))) = true := by quickRfl
theorem sS : allN 7 (fun j => Nat.beq (RuSS2.S j) (RuT1920.L (Nat.add 7 j))) = true := by quickRfl
theorem sK : allN 10 (fun j => Nat.beq (RuKS.S j) (RuT1920.L (Nat.add 14 j))) = true := by
  quickRfl
theorem sJ : allN 10 (fun j => Nat.beq (RuJS2.S j) (RuT1920.L (Nat.add 24 j))) = true := by
  quickRfl
theorem sR : allN 7 (fun j => Nat.beq (RuRS2.S j) (RuT1920.L (Nat.add 34 j))) = true := by
  quickRfl
theorem sQ : allN 8 (fun j => Nat.beq (RuQS.S j) (RuT80.L j)) = true := by quickRfl
theorem sBC : (Nat.beq ruCBlockStrong.size 6 &&
    allN 6 fun k => bindArrK ruCBlockStrong[k]! 6 3 (RuBC.S k)) = true := by quickRfl
theorem sBN : (Nat.beq ruNBlockStrong.size 5 &&
    allN 5 fun k => bindArrK ruNBlockStrong[k]! 7 4 (RuBN.S k)) = true := by quickRfl

theorem bF : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruCFaithfulBase)[t]!
    (pg 11 (mask 11) RuFS.BP t)) = true := by quickRfl
theorem bS : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruSBase)[t]!
    (pg 11 (mask 11) RuSS2.BP t)) = true := by quickRfl
theorem bK : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruKBase)[t]!
    (pg 11 (mask 11) RuKS.BP t)) = true := by quickRfl
theorem bJ : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruJBase)[t]!
    (pg 11 (mask 11) RuJS2.BP t)) = true := by quickRfl
theorem bR : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruRBase)[t]!
    (pg 11 (mask 11) RuRS2.BP t)) = true := by quickRfl
theorem bQ : allN 4 (fun t => Nat.beq (ruBaseArr 80 ruCQuotient80Base)[t]!
    (pg 7 (mask 7) RuQS.BP t)) = true := by quickRfl
theorem bBC : allN 3 (fun t => Nat.beq (ruBaseArr 6 [0, 2, 1])[t]!
    (pg 3 (mask 3) RuBC.BP t)) = true := by quickRfl
theorem bBN : allN 3 (fun t => Nat.beq (ruBaseArr 7 [1, 0, 2])[t]!
    (pg 4 (mask 4) RuBN.BP t)) = true := by quickRfl

theorem pF : allN 7 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuFS.S j) (RuFS.SI j)) =
    true := by quickRfl
theorem pS : allN 7 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuSS2.S j) (RuSS2.SI j)) =
    true := by quickRfl
theorem pK : allN 10 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuKS.S j) (RuKS.SI j)) =
    true := by quickRfl
theorem pJ : allN 10 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuJS2.S j) (RuJS2.SI j)) =
    true := by quickRfl
theorem pR : allN 7 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuRS2.S j) (RuRS2.SI j)) =
    true := by quickRfl
theorem pQ : allN 8 (fun j => permOK 80 7 (mask 7) (80 * 7) (RuQS.S j) (RuQS.SI j)) = true := by
  quickRfl
theorem pBC : allN 6 (fun j => permOK 6 3 (mask 3) (6 * 3) (RuBC.S j) (RuBC.SI j)) = true := by
  quickRfl
theorem pBN : allN 5 (fun j => permOK 7 4 (mask 4) (7 * 4) (RuBN.S j) (RuBN.SI j)) = true := by
  quickRfl

theorem bindsF : Binds 1920 11 RuFS.S 7 2 RuFS.BP (ruField1920 0)
    (ruBaseArr 1920 ruCFaithfulBase) := binds1920 rfl (by norm_num) sF rfl bF
theorem bindsS : Binds 1920 11 RuSS2.S 7 2 RuSS2.BP (ruField1920 1) (ruBaseArr 1920 ruSBase) :=
  binds1920 rfl (by norm_num) sS rfl bS
theorem bindsK : Binds 1920 11 RuKS.S 10 2 RuKS.BP (ruField1920 2) (ruBaseArr 1920 ruKBase) :=
  binds1920 rfl (by norm_num) sK rfl bK
theorem bindsJ : Binds 1920 11 RuJS2.S 10 2 RuJS2.BP (ruField1920 3) (ruBaseArr 1920 ruJBase) :=
  binds1920 rfl (by norm_num) sJ rfl bJ
theorem bindsR : Binds 1920 11 RuRS2.S 7 2 RuRS2.BP (ruField1920 4) (ruBaseArr 1920 ruRBase) :=
  binds1920 rfl (by norm_num) sR rfl bR
theorem bindsQ : Binds 80 7 RuQS.S 8 4 RuQS.BP ruField80 (ruBaseArr 80 ruCQuotient80Base) :=
  binds80 sQ rfl bQ
theorem bindsBC : Binds 6 3 RuBC.S 6 3 RuBC.BP ruCBlockStrong (ruBaseArr 6 [0, 2, 1]) :=
  bindsLit (by norm_num) sBC rfl bBC
theorem bindsBN : Binds 7 4 RuBN.S 5 3 RuBN.BP ruNBlockStrong (ruBaseArr 7 [1, 0, 2]) :=
  bindsLit (by norm_num) sBN rfl bBN

theorem cF : bAnd(Nat.beq (rcnt (RuFS.LR 0)) 1920, Nat.beq (rcnt (RuFS.LR 1)) 128) = true := by
  quickRfl
theorem cS : bAnd(Nat.beq (rcnt (RuSS2.LR 0)) 1024, Nat.beq (rcnt (RuSS2.LR 1)) 16) = true := by
  quickRfl
theorem cK : bAnd(Nat.beq (rcnt (RuKS.LR 0)) 512, Nat.beq (rcnt (RuKS.LR 1)) 4) = true := by
  quickRfl
theorem cJ : bAnd(Nat.beq (rcnt (RuJS2.LR 0)) 128, Nat.beq (rcnt (RuJS2.LR 1)) 16) = true := by
  quickRfl
theorem cR : bAnd(Nat.beq (rcnt (RuRS2.LR 0)) 256, Nat.beq (rcnt (RuRS2.LR 1)) 8) = true := by
  quickRfl
theorem cQ0 : Nat.beq (rcnt (RuQS.LR 0)) 80 = true := by quickRfl
theorem cQ1 : Nat.beq (rcnt (RuQS.LR 1)) 64 = true := by quickRfl
theorem cQ2 : Nat.beq (rcnt (RuQS.LR 2)) 12 = true := by quickRfl
theorem cQ3 : Nat.beq (rcnt (RuQS.LR 3)) 2 = true := by quickRfl
theorem cBC : bAnd(Nat.beq (rcnt (RuBC.LR 0)) 6, bAnd(Nat.beq (rcnt (RuBC.LR 1)) 5,
    Nat.beq (rcnt (RuBC.LR 2)) 4)) = true := by quickRfl
theorem cBN : bAnd(Nat.beq (rcnt (RuBN.LR 0)) 7, bAnd(Nat.beq (rcnt (RuBN.LR 1)) 6,
    Nat.beq (rcnt (RuBN.LR 2)) 4)) = true := by quickRfl

@[expose] noncomputable def siftSJ (i : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (RuT1920.L (Nat.add 24 i)) (1920 * 11)) 0,
    siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuSS2.LR RuSS2.TRI RuSS2.BP 2 0
      (RuT1920.L (Nat.add 24 i)))

@[expose] noncomputable def siftSK (i : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (RuT1920.L (Nat.add 14 i)) (1920 * 11)) 0,
    siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuSS2.LR RuSS2.TRI RuSS2.BP 2 0
      (RuT1920.L (Nat.add 14 i)))

theorem hSJ : allN 6 siftSJ = true := by quickRfl
theorem hSK : allN 8 siftSK = true := by quickRfl
theorem zHi : Nat.beq (Nat.shiftRight RuF.ZF (1920 * 11)) 0 = true := by quickRfl
theorem zRange : allN 1920 (fun i => Nat.blt (pg 11 (mask 11) RuF.ZF i) 1920) = true := by
  quickRfl
theorem rangeSJ : allN 6 (fun j => allN 1920 (fun i =>
    Nat.blt (pg 11 (mask 11) (RuT1920.L (Nat.add 24 j)) i) 1920)) = true := by
  quickRfl
theorem rangeSK : allN 8 (fun j => allN 1920 (fun i =>
    Nat.blt (pg 11 (mask 11) (RuT1920.L (Nat.add 14 j)) i) 1920)) = true := by
  quickRfl
theorem zK : siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuKS.LR RuKS.TRI RuKS.BP 2 0
    RuF.ZF = true := by quickRfl
theorem zJ : siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuJS2.LR RuJS2.TRI RuJS2.BP 2 0
    RuF.ZF = true := by quickRfl
theorem zR : siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuRS2.LR RuRS2.TRI RuRS2.BP 2 0
    RuF.ZF = true := by quickRfl

theorem zf_eq' : resA ruF ruFPos ruZA = unpack 1920 11 RuF.ZF := RuF.zf_eq

theorem resJ_eq {i : Nat} (hi : i < 6) :
    resA ruF ruFPos ruJGensA[i]! = unpack 1920 11 (RuT1920.L (Nat.add 24 i)) := by
  rw [RuCe.jg_eq hi]
  exact RuCe.resF_eq (RuCe.jok_spec hi).2 (RuCe.RJj.all i hi)

theorem resK_eq {i : Nat} (hi : i < 8) :
    resA ruF ruFPos ruKGensA[i]! = unpack 1920 11 (RuT1920.L (Nat.add 14 i)) := by
  rw [RuCe.kg_eq hi]
  exact RuCe.resF_eq (RuCe.kok_spec hi).2 (RuCe.RKj.all i hi)

theorem le_of {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem facts : (ruChainOK 1920 (ruField1920 0) 2 7 ruCFaithfulBase ruCFaithfulDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase) = [1920, 128])
    ∧ (ruChainOK 80 ruField80 2 8 ruCQuotient80Base ruCQuotient80Derivations = true ∧
      rawOrbitSizes 80 ruField80 (ruBaseArr 80 ruCQuotient80Base) = [80, 64, 12, 2])
    ∧ (ruChainOK 1920 (ruField1920 1) 4 7 ruSBase ruSDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 1) (ruBaseArr 1920 ruSBase) = [1024, 16] ∧
      (∀ i < 6, ruSift 1920 (ruField1920 1) ruSBase (resA ruF ruFPos ruJGensA[i]!) = true) ∧
      (∀ i < 8, ruSift 1920 (ruField1920 1) ruSBase (resA ruF ruFPos ruKGensA[i]!) = true))
    ∧ (ruChainOK 1920 (ruField1920 2) 8 10 ruKBase ruKDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 2) (ruBaseArr 1920 ruKBase) = [512, 4] ∧
      ruSift 1920 (ruField1920 2) ruKBase (resA ruF ruFPos ruZA) = true)
    ∧ (ruChainOK 1920 (ruField1920 3) 6 10 ruJBase ruJDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 3) (ruBaseArr 1920 ruJBase) = [128, 16] ∧
      ruSift 1920 (ruField1920 3) ruJBase (resA ruF ruFPos ruZA) = true)
    ∧ (ruChainOK 1920 (ruField1920 4) 5 7 ruRBase ruRDerivations = true ∧
      rawOrbitSizes 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase) = [256, 8] ∧
      ruSift 1920 (ruField1920 4) ruRBase (resA ruF ruFPos ruZA) = true)
    ∧ (ruChainOK 6 ruCBlockStrong 2 6 [0, 2, 1] [[-2, -1], [-1, -1, 2, 1], [3, -4], [3, 4, 3]] =
        true ∧
      rawOrbitSizes 6 ruCBlockStrong (ruBaseArr 6 [0, 2, 1]) = [6, 5, 4] ∧
      ruChainOK 7 ruNBlockStrong 2 5 [1, 0, 2] [[-1, 2, 1], [-2, 3, 1], [3, -4, -3, 4, 3]] = true ∧
      rawOrbitSizes 7 ruNBlockStrong (ruBaseArr 7 [1, 0, 2]) = [7, 6, 4]) := by
  have o2 : ∀ {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
      {base : Array Nat} {a b : Nat}, Binds n w PS kS 2 BP S base →
      allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true →
      LevelsOK n w PS PSI LR TR TRI kS 2 BP →
      bAnd(Nat.beq (rcnt (LR 0)) a, Nat.beq (rcnt (LR 1)) b) = true →
      rawOrbitSizes n S base = [a, b] := fun hb hp hl hc => by
    rw [rawOrbitSizesK_sound hb hp hl]
    obtain ⟨h0, h1⟩ := (bAnd_iff _ _).1 hc
    simp [List.range_succ, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1]
  have o3 : ∀ {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
      {base : Array Nat} {a b c : Nat}, Binds n w PS kS 3 BP S base →
      allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true →
      LevelsOK n w PS PSI LR TR TRI kS 3 BP →
      bAnd(Nat.beq (rcnt (LR 0)) a, bAnd(Nat.beq (rcnt (LR 1)) b, Nat.beq (rcnt (LR 2)) c)) =
        true → rawOrbitSizes n S base = [a, b, c] := fun hb hp hl hc => by
    rw [rawOrbitSizesK_sound hb hp hl]
    obtain ⟨h0, h⟩ := (bAnd_iff _ _).1 hc
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    simp [List.range_succ, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1,
      Nat.eq_of_beq_eq_true h2]
  have oQ : rawOrbitSizes 80 ruField80 (ruBaseArr 80 ruCQuotient80Base) = [80, 64, 12, 2] := by
    rw [rawOrbitSizesK_sound bindsQ pQ RuQS.hl]
    simp [List.range_succ, Nat.eq_of_beq_eq_true cQ0, Nat.eq_of_beq_eq_true cQ1,
      Nat.eq_of_beq_eq_true cQ2, Nat.eq_of_beq_eq_true cQ3]
  refine ⟨⟨rawChainK_sound (NS := RuFS.NS) bindsF RuFS.head RuFS.hl (le_of (by quickRfl)) RuFS.hs,
      o2 bindsF pF RuFS.hl cF⟩,
    ⟨rawChainK_sound (NS := RuQS.NS) bindsQ RuQS.head RuQS.hl (le_of (by quickRfl)) RuQS.hs, oQ⟩,
    ⟨rawChainK_sound (NS := RuSS2.NS) bindsS RuSS2.head RuSS2.hl (le_of (by quickRfl)) RuSS2.hs,
      o2 bindsS pS RuSS2.hl cS, fun i hi => ?_, fun i hi => ?_⟩,
    ⟨rawChainK_sound (NS := RuKS.NS) bindsK RuKS.head RuKS.hl (le_of (by quickRfl)) RuKS.hs,
      o2 bindsK pK RuKS.hl cK,
      siftK_soundR bindsK pK RuKS.hl zf_eq' (Nat.eq_of_beq_eq_true zHi) zRange zK⟩,
    ⟨rawChainK_sound (NS := RuJS2.NS) bindsJ RuJS2.head RuJS2.hl (le_of (by quickRfl)) RuJS2.hs,
      o2 bindsJ pJ RuJS2.hl cJ,
      siftK_soundR bindsJ pJ RuJS2.hl zf_eq' (Nat.eq_of_beq_eq_true zHi) zRange zJ⟩,
    ⟨rawChainK_sound (NS := RuRS2.NS) bindsR RuRS2.head RuRS2.hl (le_of (by quickRfl)) RuRS2.hs,
      o2 bindsR pR RuRS2.hl cR,
      siftK_soundR bindsR pR RuRS2.hl zf_eq' (Nat.eq_of_beq_eq_true zHi) zRange zR⟩,
    ⟨rawChainK_sound (NS := RuBC.NS) bindsBC RuBC.head RuBC.hl (le_of (by quickRfl)) RuBC.hs,
      o3 bindsBC pBC RuBC.hl cBC,
      rawChainK_sound (NS := RuBN.NS) bindsBN RuBN.head RuBN.hl (le_of (by quickRfl)) RuBN.hs,
      o3 bindsBN pBN RuBN.hl cBN⟩⟩
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hSJ i hi)
    exact siftK_soundR bindsS pS RuSS2.hl (resJ_eq hi) (Nat.eq_of_beq_eq_true h1)
      (allN_spec rangeSJ i hi) h2
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hSK i hi)
    exact siftK_soundR bindsS pS RuSS2.hl (resK_eq hi) (Nat.eq_of_beq_eq_true h1)
      (allN_spec rangeSK i hi) h2

end CertificateChecks.KernelSporSch.RuSF

end
