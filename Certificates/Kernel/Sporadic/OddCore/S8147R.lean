module

public import Certificates.Kernel.Sporadic.OddCore.S8147H

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KS.HNA CFSG.KC.PermTool CFSG.KS.EnumBase
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem lit2_get {a b : Array Nat} : (#[a, b] : Array (Array Nat))[0]! = a ∧
    (#[a, b] : Array (Array Nat))[1]! = b := ⟨rfl, rfl⟩

theorem arr2_eq {a : Array (Array Nat)} {x y : Array Nat} (hs : a.size = 2) (h0 : a[0]! = x)
    (h1 : a[1]! = y) : a = #[x, y] := by
  apply Array.ext
  · rw [hs]
    rfl
  · intro k h1' h2'
    have hk : k < 2 := by rwa [hs] at h1'
    rw [← getElem!_pos a k h1']
    interval_cases k
    · rw [h0]
      rfl
    · rw [h1]
      rfl

theorem cArrs_lit {i : Nat} (hi : i < 6) : suzFiveCArrs i =
    #[unpack 1782 11 (SFvT.F (Nat.add (6 + 2 * i) 0)), unpack 1782 11 (SFvT.F (Nat.add (6 + 2 * i) 1))] :=
  arr2_eq (cArrs_size hi) (cArrs_fv hi (by norm_num)) (cArrs_fv hi (by norm_num))

theorem pre_spec5 {G0 G1 : Nat} (h : bAnd(preChk G0 G1,
    strictB (pcomp 1782 11 (mask 11) G0 G0) fun Q =>
      bAnd(nB (Nat.beq Q (pidn 1782 11)), bAnd(nB (Nat.beq Q G0), bAnd(nB (Nat.beq Q G1),
      bAnd(nB (Nat.beq Q (pinvS 1782 11 (mask 11) G0)),
        nB (Nat.beq Q (pinvS 1782 11 (mask 11) G1))))))) = true) :
    preChk G0 G1 = true ∧
      (Nat.beq (pcomp 1782 11 (mask 11) G0 G0) (pidn 1782 11) = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) G0 = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) G1 = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) (pinvS 1782 11 (mask 11) G0) = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) (pinvS 1782 11 (mask 11) G1) = false) := by
  simp only [CFSG.KS.EnumBase.strictB_eq, bAnd_eq, Bool.and_eq_true, nB_eq, Bool.not_eq_true'] at h
  exact h

theorem cE0 : enumOK 1782 (suzFiveCArrs 0) suzFiveKeys (suzFiveCCert 0) = true ∧
    (suzFiveCCert 0).pts.size = 3600 ∧
    (∀ j < 3600, (suzFiveCCert 0).pts[j]! = unpack 1782 11 (SFC0.T j)) ∧
    ∀ j < 3600, PP 1782 11 (SFC0.T j) :=
  enumF (L := 48) (K := 75) (E := SFC0.E) (fuel := 3700) (cArrs_size (by norm_num))
    (fun k hk => by
      rw [cArrs_fv (by norm_num) hk]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true (allN_spec gC0 k hk)).symm)
    (by norm_num) (by norm_num) hC0 dC0 kC0 pC0 C0K.all (by norm_num)

theorem ccOK0 : suzFiveCCheck (suzFiveCArrs 0) (suzFiveLineArr 0) (suzFiveCCert 0)
    suzFiveCentOrders[0]! = true :=
  cCheck_of (i := 0) (G := fun k => SFvT.F (Nat.add 6 k)) (by norm_num) (fun _ _ => rfl) cE0 rfl
    cGen0 cX0

theorem bf0 : (suzFiveBfs 0)[1]! = unpack 1782 11 (SFvT.F 6) ∧
    (suzFiveBfs 0)[2]! = unpack 1782 11 (SFvT.F 7) ∧
    (suzFiveBfs 0)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 6)) ∧
    (suzFiveBfs 0)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 7)) :=
  bfs_get (cArrs_lit (i := 0) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num)) pre0

theorem hc0 : suzFiveCArrs 0 = #[unpack 1782 11 (SFvT.F 6), unpack 1782 11 (SFvT.F 7)] :=
  cArrs_lit (by norm_num)

theorem dA0 : (suzFiveDArrs 0).size = 2 ∧
    ∀ l < 2, (suzFiveDArrs 0)[l]! = unpack 1782 11 (SFD0.G l) := by
  have g := gD0
  rw [bAnd_eq, Bool.and_eq_true] at g
  have e : suzFiveDerivedPairs[0]! = #[(1, 1), (1, 3)] := rfl
  refine ⟨by unfold suzFiveDArrs; rw [Array.size_map, e]; rfl, fun l hl => ?_⟩
  unfold suzFiveDArrs
  simp only []
  rw [getElem!_pos _ l (by rw [Array.size_map, e]; simpa using hl), Array.getElem_map]
  interval_cases l
  · change commutatorA 1782 (suzFiveCArrs 0)[1]! (suzFiveBfs 0)[1]! = _
    rw [hc0, lit2_get.2, bf0.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)),
      Nat.eq_of_beq_eq_true g.1]
  · change commutatorA 1782 (suzFiveCArrs 0)[1]! (suzFiveBfs 0)[3]! = _
    rw [hc0, lit2_get.2, bf0.2.2.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)).inv,
      Nat.eq_of_beq_eq_true g.2]

theorem dP0 : ∀ l < 2, PP 1782 11 (SFD0.G l) := fun l hl => PP_of_permOK szk (allN_spec pD0 l hl)

theorem dM0 : ∀ l < 2, pm (SFD0.G l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 0)) := by
  have g := gD0
  rw [bAnd_eq, Bool.and_eq_true] at g
  have m0 : pm (SFvT.F 6) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 0)) :=
    pm_cGen (i := 0) (k := 0) (by norm_num) (by norm_num)
  have m1 : pm (SFvT.F 7) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 0)) :=
    pm_cGen (i := 0) (k := 1) (by norm_num) (by norm_num)
  have p6 : PP 1782 11 (SFvT.F 6) := fv_PP (by norm_num)
  have p7 : PP 1782 11 (SFvT.F 7) := fv_PP (by norm_num)
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true g.1, pm_commP p7 p6]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m0) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)
  · rw [Nat.eq_of_beq_eq_true g.2, pm_commP p7 p6.inv, pm_inv p6]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m0))
      (Subgroup.inv_mem _ m1)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m0))

theorem dE0 : enumOK 1782 (suzFiveDArrs 0) suzFiveKeys (suzFiveDCert 0) = true ∧
    (suzFiveDCert 0).pts.size = 360 ∧
    (∀ j < 360, (suzFiveDCert 0).pts[j]! = unpack 1782 11 (SFD0.T j)) ∧
    ∀ j < 360, PP 1782 11 (SFD0.T j) :=
  enumF (L := 40) (K := 9) (E := SFD0.E) (fuel := 400) dA0.1 dA0.2 (by norm_num) (by norm_num) hD0
    dD0 kD0 pD0 D0K.all (by norm_num)

theorem dOK0 : suzFiveDCheck (suzFiveCArrs 0) (suzFiveCCert 0) (suzFiveDArrs 0) (suzFiveDCert 0) 360
    (suzFiveLineArr 0) 5 = true :=
  dCheck_of (i := 0) (by norm_num) cE0 kC0 dE0 rfl dA0.1 (by norm_num) dA0.2 dP0 dM0 dFacts0
    (fun _ => dPow0)

theorem prOK0 : suzFivePairsCheck 0 = true := by
  have p := pairs0
  rw [bAnd_eq, Bool.and_eq_true] at p
  have e : suzFiveDerivedPairs[0]! = #[(1, 1), (1, 3)] := rfl
  refine pairs_of (by norm_num) cE0 fun l hl => ?_
  rw [e] at hl
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 0)[1]! = unpack 1782 11 Y ∧
      memK 3600 SFC0.T Y = true
    exact ⟨by norm_num, _, fv_PP (by norm_num), bf0.1, p.1⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 0)[3]! = unpack 1782 11 Y ∧
      memK 3600 SFC0.T Y = true
    exact ⟨by norm_num, _, (fv_PP (by norm_num)).inv, bf0.2.2.1, p.2⟩

theorem orOK0 : suzFiveOrbitCheck (suzFiveDArrs 0) suzFiveOrbits[0]! suzFiveOrbits[0]!.length 360
    (suzFiveOrbitCert 0) = true :=
  orbit_of (Ls := [0, 225, 211, 1263, 1557, 973]) (L := 40) (K := 9) rfl (by decide) (by norm_num)
    dA0.1 dA0.2 dP0 oFacts0 (by norm_num) (by norm_num) hO0 dO0 pO0 O0K.all (by norm_num)

theorem cE1 : enumOK 1782 (suzFiveCArrs 1) suzFiveKeys (suzFiveCCert 1) = true ∧
    (suzFiveCCert 1).pts.size = 600 ∧
    (∀ j < 600, (suzFiveCCert 1).pts[j]! = unpack 1782 11 (SFC1.T j)) ∧
    ∀ j < 600, PP 1782 11 (SFC1.T j) :=
  enumF (L := 40) (K := 15) (E := SFC1.E) (fuel := 3700) (cArrs_size (by norm_num))
    (fun k hk => by
      rw [cArrs_fv (by norm_num) hk]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true (allN_spec gC1 k hk)).symm)
    (by norm_num) (by norm_num) hC1 dC1 kC1 pC1 C1K.all (by norm_num)

theorem ccOK1 : suzFiveCCheck (suzFiveCArrs 1) (suzFiveLineArr 1) (suzFiveCCert 1)
    suzFiveCentOrders[1]! = true :=
  cCheck_of (i := 1) (G := fun k => SFvT.F (Nat.add 8 k)) (by norm_num) (fun _ _ => rfl) cE1 rfl
    cGen1 cX1

theorem bf1 : (suzFiveBfs 1)[1]! = unpack 1782 11 (SFvT.F 8) ∧
    (suzFiveBfs 1)[2]! = unpack 1782 11 (SFvT.F 9) ∧
    (suzFiveBfs 1)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 8)) ∧
    (suzFiveBfs 1)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 9)) :=
  bfs_get (cArrs_lit (i := 1) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num)) pre1

theorem hc1 : suzFiveCArrs 1 = #[unpack 1782 11 (SFvT.F 8), unpack 1782 11 (SFvT.F 9)] :=
  cArrs_lit (by norm_num)

theorem dA1 : (suzFiveDArrs 1).size = 2 ∧
    ∀ l < 2, (suzFiveDArrs 1)[l]! = unpack 1782 11 (SFD1.G l) := by
  have g := gD1
  rw [bAnd_eq, Bool.and_eq_true] at g
  have e : suzFiveDerivedPairs[1]! = #[(1, 1), (1, 3)] := rfl
  refine ⟨by unfold suzFiveDArrs; rw [Array.size_map, e]; rfl, fun l hl => ?_⟩
  unfold suzFiveDArrs
  simp only []
  rw [getElem!_pos _ l (by rw [Array.size_map, e]; simpa using hl), Array.getElem_map]
  interval_cases l
  · change commutatorA 1782 (suzFiveCArrs 1)[1]! (suzFiveBfs 1)[1]! = _
    rw [hc1, lit2_get.2, bf1.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)),
      Nat.eq_of_beq_eq_true g.1]
  · change commutatorA 1782 (suzFiveCArrs 1)[1]! (suzFiveBfs 1)[3]! = _
    rw [hc1, lit2_get.2, bf1.2.2.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)).inv,
      Nat.eq_of_beq_eq_true g.2]

theorem dP1 : ∀ l < 2, PP 1782 11 (SFD1.G l) := fun l hl => PP_of_permOK szk (allN_spec pD1 l hl)

theorem dM1 : ∀ l < 2, pm (SFD1.G l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 1)) := by
  have g := gD1
  rw [bAnd_eq, Bool.and_eq_true] at g
  have m0 : pm (SFvT.F 8) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 1)) :=
    pm_cGen (i := 1) (k := 0) (by norm_num) (by norm_num)
  have m1 : pm (SFvT.F 9) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 1)) :=
    pm_cGen (i := 1) (k := 1) (by norm_num) (by norm_num)
  have p0 : PP 1782 11 (SFvT.F 8) := fv_PP (by norm_num)
  have p1 : PP 1782 11 (SFvT.F 9) := fv_PP (by norm_num)
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true g.1, pm_commP p1 p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m0) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)
  · rw [Nat.eq_of_beq_eq_true g.2, pm_commP p1 p0.inv, pm_inv p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m0))
      (Subgroup.inv_mem _ m1)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m0))

theorem dE1 : enumOK 1782 (suzFiveDArrs 1) suzFiveKeys (suzFiveDCert 1) = true ∧
    (suzFiveDCert 1).pts.size = 60 ∧
    (∀ j < 60, (suzFiveDCert 1).pts[j]! = unpack 1782 11 (SFD1.T j)) ∧
    ∀ j < 60, PP 1782 11 (SFD1.T j) :=
  enumF (L := 20) (K := 3) (E := SFD1.E) (fuel := 400) dA1.1 dA1.2 (by norm_num) (by norm_num) hD1
    dD1 kD1 pD1 D1K.all (by norm_num)

theorem dOK1 : suzFiveDCheck (suzFiveCArrs 1) (suzFiveCCert 1) (suzFiveDArrs 1) (suzFiveDCert 1) 60
    (suzFiveLineArr 1) 10 = true :=
  dCheck_of (i := 1) (by norm_num) cE1 kC1 dE1 rfl dA1.1 (by norm_num) dA1.2 dP1 dM1 dFacts1
    (fun h => absurd h (by norm_num))

theorem prOK1 : suzFivePairsCheck 1 = true := by
  have p := pairs1
  rw [bAnd_eq, Bool.and_eq_true] at p
  have e : suzFiveDerivedPairs[1]! = #[(1, 1), (1, 3)] := rfl
  refine pairs_of (by norm_num) cE1 fun l hl => ?_
  rw [e] at hl
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 1)[1]! = unpack 1782 11 Y ∧
      memK 600 SFC1.T Y = true
    exact ⟨by norm_num, _, fv_PP (by norm_num), bf1.1, p.1⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 1)[3]! = unpack 1782 11 Y ∧
      memK 600 SFC1.T Y = true
    exact ⟨by norm_num, _, (fv_PP (by norm_num)).inv, bf1.2.2.1, p.2⟩

theorem orOK1 : suzFiveOrbitCheck (suzFiveDArrs 1) suzFiveOrbits[1]! suzFiveOrbits[1]!.length 60
    (suzFiveOrbitCert 1) = true :=
  orbit_of (Ls := [10, 1781, 445, 248, 1052]) (L := 20) (K := 3) rfl (by decide) (by norm_num)
    dA1.1 dA1.2 dP1 oFacts1 (by norm_num) (by norm_num) hO1 dO1 pO1 O1K.all (by norm_num)

theorem cE2 : enumOK 1782 (suzFiveCArrs 2) suzFiveKeys (suzFiveCCert 2) = true ∧
    (suzFiveCCert 2).pts.size = 600 ∧
    (∀ j < 600, (suzFiveCCert 2).pts[j]! = unpack 1782 11 (SFC2.T j)) ∧
    ∀ j < 600, PP 1782 11 (SFC2.T j) :=
  enumF (L := 40) (K := 15) (E := SFC2.E) (fuel := 3700) (cArrs_size (by norm_num))
    (fun k hk => by
      rw [cArrs_fv (by norm_num) hk]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true (allN_spec gC2 k hk)).symm)
    (by norm_num) (by norm_num) hC2 dC2 kC2 pC2 C2K.all (by norm_num)

theorem ccOK2 : suzFiveCCheck (suzFiveCArrs 2) (suzFiveLineArr 2) (suzFiveCCert 2)
    suzFiveCentOrders[2]! = true :=
  cCheck_of (i := 2) (G := fun k => SFvT.F (Nat.add 10 k)) (by norm_num) (fun _ _ => rfl) cE2 rfl
    cGen2 cX2

theorem bf2 : (suzFiveBfs 2)[1]! = unpack 1782 11 (SFvT.F 10) ∧
    (suzFiveBfs 2)[2]! = unpack 1782 11 (SFvT.F 11) ∧
    (suzFiveBfs 2)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 10)) ∧
    (suzFiveBfs 2)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 11)) :=
  bfs_get (cArrs_lit (i := 2) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num)) pre2

theorem hc2 : suzFiveCArrs 2 = #[unpack 1782 11 (SFvT.F 10), unpack 1782 11 (SFvT.F 11)] :=
  cArrs_lit (by norm_num)

theorem dA2 : (suzFiveDArrs 2).size = 2 ∧
    ∀ l < 2, (suzFiveDArrs 2)[l]! = unpack 1782 11 (SFD2.G l) := by
  have g := gD2
  rw [bAnd_eq, Bool.and_eq_true] at g
  have e : suzFiveDerivedPairs[2]! = #[(1, 1), (1, 3)] := rfl
  refine ⟨by unfold suzFiveDArrs; rw [Array.size_map, e]; rfl, fun l hl => ?_⟩
  unfold suzFiveDArrs
  simp only []
  rw [getElem!_pos _ l (by rw [Array.size_map, e]; simpa using hl), Array.getElem_map]
  interval_cases l
  · change commutatorA 1782 (suzFiveCArrs 2)[1]! (suzFiveBfs 2)[1]! = _
    rw [hc2, lit2_get.2, bf2.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)),
      Nat.eq_of_beq_eq_true g.1]
  · change commutatorA 1782 (suzFiveCArrs 2)[1]! (suzFiveBfs 2)[3]! = _
    rw [hc2, lit2_get.2, bf2.2.2.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)).inv,
      Nat.eq_of_beq_eq_true g.2]

theorem dP2 : ∀ l < 2, PP 1782 11 (SFD2.G l) := fun l hl => PP_of_permOK szk (allN_spec pD2 l hl)

theorem dM2 : ∀ l < 2, pm (SFD2.G l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 2)) := by
  have g := gD2
  rw [bAnd_eq, Bool.and_eq_true] at g
  have m0 : pm (SFvT.F 10) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 2)) :=
    pm_cGen (i := 2) (k := 0) (by norm_num) (by norm_num)
  have m1 : pm (SFvT.F 11) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 2)) :=
    pm_cGen (i := 2) (k := 1) (by norm_num) (by norm_num)
  have p0 : PP 1782 11 (SFvT.F 10) := fv_PP (by norm_num)
  have p1 : PP 1782 11 (SFvT.F 11) := fv_PP (by norm_num)
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true g.1, pm_commP p1 p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m0) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)
  · rw [Nat.eq_of_beq_eq_true g.2, pm_commP p1 p0.inv, pm_inv p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m0))
      (Subgroup.inv_mem _ m1)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m0))

theorem dE2 : enumOK 1782 (suzFiveDArrs 2) suzFiveKeys (suzFiveDCert 2) = true ∧
    (suzFiveDCert 2).pts.size = 60 ∧
    (∀ j < 60, (suzFiveDCert 2).pts[j]! = unpack 1782 11 (SFD2.T j)) ∧
    ∀ j < 60, PP 1782 11 (SFD2.T j) :=
  enumF (L := 20) (K := 3) (E := SFD2.E) (fuel := 400) dA2.1 dA2.2 (by norm_num) (by norm_num) hD2
    dD2 kD2 pD2 D2K.all (by norm_num)

theorem dOK2 : suzFiveDCheck (suzFiveCArrs 2) (suzFiveCCert 2) (suzFiveDArrs 2) (suzFiveDCert 2) 60
    (suzFiveLineArr 2) 10 = true :=
  dCheck_of (i := 2) (by norm_num) cE2 kC2 dE2 rfl dA2.1 (by norm_num) dA2.2 dP2 dM2 dFacts2
    (fun h => absurd h (by norm_num))

theorem prOK2 : suzFivePairsCheck 2 = true := by
  have p := pairs2
  rw [bAnd_eq, Bool.and_eq_true] at p
  have e : suzFiveDerivedPairs[2]! = #[(1, 1), (1, 3)] := rfl
  refine pairs_of (by norm_num) cE2 fun l hl => ?_
  rw [e] at hl
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 2)[1]! = unpack 1782 11 Y ∧
      memK 600 SFC2.T Y = true
    exact ⟨by norm_num, _, fv_PP (by norm_num), bf2.1, p.1⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 2)[3]! = unpack 1782 11 Y ∧
      memK 600 SFC2.T Y = true
    exact ⟨by norm_num, _, (fv_PP (by norm_num)).inv, bf2.2.2.1, p.2⟩

theorem orOK2 : suzFiveOrbitCheck (suzFiveDArrs 2) suzFiveOrbits[2]! suzFiveOrbits[2]!.length 60
    (suzFiveOrbitCert 2) = true :=
  orbit_of (Ls := [4, 730, 1579, 1514, 924]) (L := 20) (K := 3) rfl (by decide) (by norm_num)
    dA2.1 dA2.2 dP2 oFacts2 (by norm_num) (by norm_num) hO2 dO2 pO2 O2K.all (by norm_num)

theorem cE4 : enumOK 1782 (suzFiveCArrs 4) suzFiveKeys (suzFiveCCert 4) = true ∧
    (suzFiveCCert 4).pts.size = 3600 ∧
    (∀ j < 3600, (suzFiveCCert 4).pts[j]! = unpack 1782 11 (SFC4.T j)) ∧
    ∀ j < 3600, PP 1782 11 (SFC4.T j) :=
  enumF (L := 48) (K := 75) (E := SFC4.E) (fuel := 3700) (cArrs_size (by norm_num))
    (fun k hk => by
      rw [cArrs_fv (by norm_num) hk]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true (allN_spec gC4 k hk)).symm)
    (by norm_num) (by norm_num) hC4 dC4 kC4 pC4 C4K.all (by norm_num)

theorem ccOK4 : suzFiveCCheck (suzFiveCArrs 4) (suzFiveLineArr 4) (suzFiveCCert 4)
    suzFiveCentOrders[4]! = true :=
  cCheck_of (i := 4) (G := fun k => SFvT.F (Nat.add 14 k)) (by norm_num) (fun _ _ => rfl) cE4 rfl
    cGen4 cX4

theorem bf4 : (suzFiveBfs 4)[1]! = unpack 1782 11 (SFvT.F 14) ∧
    (suzFiveBfs 4)[2]! = unpack 1782 11 (SFvT.F 15) ∧
    (suzFiveBfs 4)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 14)) ∧
    (suzFiveBfs 4)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 15)) :=
  bfs_get (cArrs_lit (i := 4) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num)) pre4

theorem hc4 : suzFiveCArrs 4 = #[unpack 1782 11 (SFvT.F 14), unpack 1782 11 (SFvT.F 15)] :=
  cArrs_lit (by norm_num)

theorem dA4 : (suzFiveDArrs 4).size = 2 ∧
    ∀ l < 2, (suzFiveDArrs 4)[l]! = unpack 1782 11 (SFD4.G l) := by
  have g := gD4
  rw [bAnd_eq, Bool.and_eq_true] at g
  have e : suzFiveDerivedPairs[4]! = #[(1, 1), (1, 3)] := rfl
  refine ⟨by unfold suzFiveDArrs; rw [Array.size_map, e]; rfl, fun l hl => ?_⟩
  unfold suzFiveDArrs
  simp only []
  rw [getElem!_pos _ l (by rw [Array.size_map, e]; simpa using hl), Array.getElem_map]
  interval_cases l
  · change commutatorA 1782 (suzFiveCArrs 4)[1]! (suzFiveBfs 4)[1]! = _
    rw [hc4, lit2_get.2, bf4.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)),
      Nat.eq_of_beq_eq_true g.1]
  · change commutatorA 1782 (suzFiveCArrs 4)[1]! (suzFiveBfs 4)[3]! = _
    rw [hc4, lit2_get.2, bf4.2.2.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)).inv,
      Nat.eq_of_beq_eq_true g.2]

theorem dP4 : ∀ l < 2, PP 1782 11 (SFD4.G l) := fun l hl => PP_of_permOK szk (allN_spec pD4 l hl)

theorem dM4 : ∀ l < 2, pm (SFD4.G l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 4)) := by
  have g := gD4
  rw [bAnd_eq, Bool.and_eq_true] at g
  have m0 : pm (SFvT.F 14) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 4)) :=
    pm_cGen (i := 4) (k := 0) (by norm_num) (by norm_num)
  have m1 : pm (SFvT.F 15) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 4)) :=
    pm_cGen (i := 4) (k := 1) (by norm_num) (by norm_num)
  have p0 : PP 1782 11 (SFvT.F 14) := fv_PP (by norm_num)
  have p1 : PP 1782 11 (SFvT.F 15) := fv_PP (by norm_num)
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true g.1, pm_commP p1 p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m0) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)
  · rw [Nat.eq_of_beq_eq_true g.2, pm_commP p1 p0.inv, pm_inv p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m0))
      (Subgroup.inv_mem _ m1)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m0))

theorem dE4 : enumOK 1782 (suzFiveDArrs 4) suzFiveKeys (suzFiveDCert 4) = true ∧
    (suzFiveDCert 4).pts.size = 360 ∧
    (∀ j < 360, (suzFiveDCert 4).pts[j]! = unpack 1782 11 (SFD4.T j)) ∧
    ∀ j < 360, PP 1782 11 (SFD4.T j) :=
  enumF (L := 40) (K := 9) (E := SFD4.E) (fuel := 400) dA4.1 dA4.2 (by norm_num) (by norm_num) hD4
    dD4 kD4 pD4 D4K.all (by norm_num)

theorem dOK4 : suzFiveDCheck (suzFiveCArrs 4) (suzFiveCCert 4) (suzFiveDArrs 4) (suzFiveDCert 4) 360
    (suzFiveLineArr 4) 5 = true :=
  dCheck_of (i := 4) (by norm_num) cE4 kC4 dE4 rfl dA4.1 (by norm_num) dA4.2 dP4 dM4 dFacts4
    (fun _ => dPow4)

theorem prOK4 : suzFivePairsCheck 4 = true := by
  have p := pairs4
  rw [bAnd_eq, Bool.and_eq_true] at p
  have e : suzFiveDerivedPairs[4]! = #[(1, 1), (1, 3)] := rfl
  refine pairs_of (by norm_num) cE4 fun l hl => ?_
  rw [e] at hl
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 4)[1]! = unpack 1782 11 Y ∧
      memK 3600 SFC4.T Y = true
    exact ⟨by norm_num, _, fv_PP (by norm_num), bf4.1, p.1⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 4)[3]! = unpack 1782 11 Y ∧
      memK 3600 SFC4.T Y = true
    exact ⟨by norm_num, _, (fv_PP (by norm_num)).inv, bf4.2.2.1, p.2⟩

theorem orOK4 : suzFiveOrbitCheck (suzFiveDArrs 4) suzFiveOrbits[4]! suzFiveOrbits[4]!.length 360
    (suzFiveOrbitCert 4) = true :=
  orbit_of (Ls := [211, 1678, 1279, 1158, 1211, 497]) (L := 40) (K := 9) rfl (by decide)
    (by norm_num) dA4.1 dA4.2 dP4 oFacts4 (by norm_num) (by norm_num) hO4 dO4 pO4 O4K.all
    (by norm_num)

theorem cE5 : enumOK 1782 (suzFiveCArrs 5) suzFiveKeys (suzFiveCCert 5) = true ∧
    (suzFiveCCert 5).pts.size = 600 ∧
    (∀ j < 600, (suzFiveCCert 5).pts[j]! = unpack 1782 11 (SFC5.T j)) ∧
    ∀ j < 600, PP 1782 11 (SFC5.T j) :=
  enumF (L := 40) (K := 15) (E := SFC5.E) (fuel := 3700) (cArrs_size (by norm_num))
    (fun k hk => by
      rw [cArrs_fv (by norm_num) hk]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true (allN_spec gC5 k hk)).symm)
    (by norm_num) (by norm_num) hC5 dC5 kC5 pC5 C5K.all (by norm_num)

theorem ccOK5 : suzFiveCCheck (suzFiveCArrs 5) (suzFiveLineArr 5) (suzFiveCCert 5)
    suzFiveCentOrders[5]! = true :=
  cCheck_of (i := 5) (G := fun k => SFvT.F (Nat.add 16 k)) (by norm_num) (fun _ _ => rfl) cE5 rfl
    cGen5 cX5

theorem bf5 : (suzFiveBfs 5)[1]! = unpack 1782 11 (SFvT.F 16) ∧
    (suzFiveBfs 5)[2]! = unpack 1782 11 (SFvT.F 17) ∧
    (suzFiveBfs 5)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 16)) ∧
    (suzFiveBfs 5)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 17)) :=
  bfs_get (cArrs_lit (i := 5) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num)) pre5

theorem hc5 : suzFiveCArrs 5 = #[unpack 1782 11 (SFvT.F 16), unpack 1782 11 (SFvT.F 17)] :=
  cArrs_lit (by norm_num)

theorem dA5 : (suzFiveDArrs 5).size = 2 ∧
    ∀ l < 2, (suzFiveDArrs 5)[l]! = unpack 1782 11 (SFD5.G l) := by
  have g := gD5
  rw [bAnd_eq, Bool.and_eq_true] at g
  have e : suzFiveDerivedPairs[5]! = #[(1, 1), (1, 3)] := rfl
  refine ⟨by unfold suzFiveDArrs; rw [Array.size_map, e]; rfl, fun l hl => ?_⟩
  unfold suzFiveDArrs
  simp only []
  rw [getElem!_pos _ l (by rw [Array.size_map, e]; simpa using hl), Array.getElem_map]
  interval_cases l
  · change commutatorA 1782 (suzFiveCArrs 5)[1]! (suzFiveBfs 5)[1]! = _
    rw [hc5, lit2_get.2, bf5.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)),
      Nat.eq_of_beq_eq_true g.1]
  · change commutatorA 1782 (suzFiveCArrs 5)[1]! (suzFiveBfs 5)[3]! = _
    rw [hc5, lit2_get.2, bf5.2.2.1, commU (fv_PP (by norm_num)) (fv_PP (by norm_num)).inv,
      Nat.eq_of_beq_eq_true g.2]

theorem dP5 : ∀ l < 2, PP 1782 11 (SFD5.G l) := fun l hl => PP_of_permOK szk (allN_spec pD5 l hl)

theorem dM5 : ∀ l < 2, pm (SFD5.G l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 5)) := by
  have g := gD5
  rw [bAnd_eq, Bool.and_eq_true] at g
  have m0 : pm (SFvT.F 16) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 5)) :=
    pm_cGen (i := 5) (k := 0) (by norm_num) (by norm_num)
  have m1 : pm (SFvT.F 17) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 5)) :=
    pm_cGen (i := 5) (k := 1) (by norm_num) (by norm_num)
  have p0 : PP 1782 11 (SFvT.F 16) := fv_PP (by norm_num)
  have p1 : PP 1782 11 (SFvT.F 17) := fv_PP (by norm_num)
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true g.1, pm_commP p1 p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m0) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)
  · rw [Nat.eq_of_beq_eq_true g.2, pm_commP p1 p0.inv, pm_inv p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m0))
      (Subgroup.inv_mem _ m1)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m0))

theorem dE5 : enumOK 1782 (suzFiveDArrs 5) suzFiveKeys (suzFiveDCert 5) = true ∧
    (suzFiveDCert 5).pts.size = 60 ∧
    (∀ j < 60, (suzFiveDCert 5).pts[j]! = unpack 1782 11 (SFD5.T j)) ∧
    ∀ j < 60, PP 1782 11 (SFD5.T j) :=
  enumF (L := 20) (K := 3) (E := SFD5.E) (fuel := 400) dA5.1 dA5.2 (by norm_num) (by norm_num) hD5
    dD5 kD5 pD5 D5K.all (by norm_num)

theorem dOK5 : suzFiveDCheck (suzFiveCArrs 5) (suzFiveCCert 5) (suzFiveDArrs 5) (suzFiveDCert 5) 60
    (suzFiveLineArr 5) 10 = true :=
  dCheck_of (i := 5) (by norm_num) cE5 kC5 dE5 rfl dA5.1 (by norm_num) dA5.2 dP5 dM5 dFacts5
    (fun h => absurd h (by norm_num))

theorem prOK5 : suzFivePairsCheck 5 = true := by
  have p := pairs5
  rw [bAnd_eq, Bool.and_eq_true] at p
  have e : suzFiveDerivedPairs[5]! = #[(1, 1), (1, 3)] := rfl
  refine pairs_of (by norm_num) cE5 fun l hl => ?_
  rw [e] at hl
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 5)[1]! = unpack 1782 11 Y ∧
      memK 600 SFC5.T Y = true
    exact ⟨by norm_num, _, fv_PP (by norm_num), bf5.1, p.1⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 5)[3]! = unpack 1782 11 Y ∧
      memK 600 SFC5.T Y = true
    exact ⟨by norm_num, _, (fv_PP (by norm_num)).inv, bf5.2.2.1, p.2⟩

theorem orOK5 : suzFiveOrbitCheck (suzFiveDArrs 5) suzFiveOrbits[5]! suzFiveOrbits[5]!.length 60
    (suzFiveOrbitCert 5) = true :=
  orbit_of (Ls := [16, 992, 1162, 240, 845]) (L := 20) (K := 3) rfl (by decide) (by norm_num)
    dA5.1 dA5.2 dP5 oFacts5 (by norm_num) (by norm_num) hO5 dO5 pO5 O5K.all (by norm_num)

theorem cE3 : enumOK 1782 (suzFiveCArrs 3) suzFiveKeys (suzFiveCCert 3) = true ∧
    (suzFiveCCert 3).pts.size = 3600 ∧
    (∀ j < 3600, (suzFiveCCert 3).pts[j]! = unpack 1782 11 (SFC3.T j)) ∧
    ∀ j < 3600, PP 1782 11 (SFC3.T j) :=
  enumF (L := 48) (K := 75) (E := SFC3.E) (fuel := 3700) (cArrs_size (by norm_num))
    (fun k hk => by
      rw [cArrs_fv (by norm_num) hk]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true (allN_spec gC3 k hk)).symm)
    (by norm_num) (by norm_num) hC3 dC3 kC3 pC3 C3K.all (by norm_num)

theorem ccOK3 : suzFiveCCheck (suzFiveCArrs 3) (suzFiveLineArr 3) (suzFiveCCert 3)
    suzFiveCentOrders[3]! = true :=
  cCheck_of (i := 3) (G := fun k => SFvT.F (Nat.add 12 k)) (by norm_num) (fun _ _ => rfl) cE3 rfl
    cGen3 cX3

theorem bf3 : (suzFiveBfs 3)[1]! = unpack 1782 11 (SFvT.F 12) ∧
    (suzFiveBfs 3)[2]! = unpack 1782 11 (SFvT.F 13) ∧
    (suzFiveBfs 3)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 12)) ∧
    (suzFiveBfs 3)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) (SFvT.F 13)) :=
  bfs_get (cArrs_lit (i := 3) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num))
    (pre_spec5 pre3).1

theorem bf3' : (suzFiveBfs 3)[5]! =
    unpack 1782 11 (pcomp 1782 11 (mask 11) (SFvT.F 12) (SFvT.F 12)) :=
  bfs_get5 (cArrs_lit (i := 3) (by norm_num)) (fv_PP (by norm_num)) (fv_PP (by norm_num))
    (pre_spec5 pre3).1 (pre_spec5 pre3).2

theorem hc3 : suzFiveCArrs 3 = #[unpack 1782 11 (SFvT.F 12), unpack 1782 11 (SFvT.F 13)] :=
  cArrs_lit (by norm_num)

theorem dA3 : (suzFiveDArrs 3).size = 4 ∧
    ∀ l < 4, (suzFiveDArrs 3)[l]! = unpack 1782 11 (SFD3.G l) := by
  have g := gD3
  simp only [bAnd_eq, Bool.and_eq_true] at g
  obtain ⟨g0, g1, g2, g3⟩ := g
  have p12 : PP 1782 11 (SFvT.F 12) := fv_PP (by norm_num)
  have p13 : PP 1782 11 (SFvT.F 13) := fv_PP (by norm_num)
  have e : suzFiveDerivedPairs[3]! = #[(1, 1), (1, 3), (0, 4), (1, 5)] := rfl
  refine ⟨by unfold suzFiveDArrs; rw [Array.size_map, e]; rfl, fun l hl => ?_⟩
  unfold suzFiveDArrs
  simp only []
  rw [getElem!_pos _ l (by rw [Array.size_map, e]; simpa using hl), Array.getElem_map]
  interval_cases l
  · change commutatorA 1782 (suzFiveCArrs 3)[1]! (suzFiveBfs 3)[1]! = _
    rw [hc3, lit2_get.2, bf3.1, commU p13 p12, Nat.eq_of_beq_eq_true g0]
  · change commutatorA 1782 (suzFiveCArrs 3)[1]! (suzFiveBfs 3)[3]! = _
    rw [hc3, lit2_get.2, bf3.2.2.1, commU p13 p12.inv, Nat.eq_of_beq_eq_true g1]
  · change commutatorA 1782 (suzFiveCArrs 3)[0]! (suzFiveBfs 3)[4]! = _
    rw [hc3, lit2_get.1, bf3.2.2.2, commU p12 p13.inv, Nat.eq_of_beq_eq_true g2]
  · change commutatorA 1782 (suzFiveCArrs 3)[1]! (suzFiveBfs 3)[5]! = _
    rw [hc3, lit2_get.2, bf3', commU p13 (p12.mul p12), Nat.eq_of_beq_eq_true g3]

theorem dP3 : ∀ l < 4, PP 1782 11 (SFD3.G l) := fun l hl => PP_of_permOK szk (allN_spec pD3 l hl)

theorem dM3 : ∀ l < 4, pm (SFD3.G l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 3)) := by
  have g := gD3
  simp only [bAnd_eq, Bool.and_eq_true] at g
  obtain ⟨g0, g1, g2, g3⟩ := g
  have m0 : pm (SFvT.F 12) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 3)) :=
    pm_cGen (i := 3) (k := 0) (by norm_num) (by norm_num)
  have m1 : pm (SFvT.F 13) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs 3)) :=
    pm_cGen (i := 3) (k := 1) (by norm_num) (by norm_num)
  have p0 : PP 1782 11 (SFvT.F 12) := fv_PP (by norm_num)
  have p1 : PP 1782 11 (SFvT.F 13) := fv_PP (by norm_num)
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true g0, pm_commP p1 p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m0) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)
  · rw [Nat.eq_of_beq_eq_true g1, pm_commP p1 p0.inv, pm_inv p0]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m0))
      (Subgroup.inv_mem _ m1)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m0))
  · rw [Nat.eq_of_beq_eq_true g2, pm_commP p0 p1.inv, pm_inv p1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m0 (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m0)) (Subgroup.inv_mem _ (Subgroup.inv_mem _ m1))
  · rw [Nat.eq_of_beq_eq_true g3, pm_commP p1 (p0.mul p0), pm_mul p0 p0]
    have m00 := Subgroup.mul_mem _ m0 m0
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m00) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m00)

theorem dE3 : enumOK 1782 (suzFiveDArrs 3) suzFiveKeys (suzFiveDCert 3) = true ∧
    (suzFiveDCert 3).pts.size = 360 ∧
    (∀ j < 360, (suzFiveDCert 3).pts[j]! = unpack 1782 11 (SFD3.T j)) ∧
    ∀ j < 360, PP 1782 11 (SFD3.T j) :=
  enumF (L := 40) (K := 9) (E := SFD3.E) (fuel := 400) dA3.1 dA3.2 (by norm_num) (by norm_num) hD3
    dD3 kD3 pD3 D3K.all (by norm_num)

theorem dOK3 : suzFiveDCheck (suzFiveCArrs 3) (suzFiveCCert 3) (suzFiveDArrs 3) (suzFiveDCert 3) 360
    (suzFiveLineArr 3) 5 = true :=
  dCheck_of (i := 3) (by norm_num) cE3 kC3 dE3 rfl dA3.1 (by norm_num) dA3.2 dP3 dM3 dFacts3
    (fun _ => dPow3)

theorem prOK3 : suzFivePairsCheck 3 = true := by
  have p := pairs3
  simp only [bAnd_eq, Bool.and_eq_true] at p
  obtain ⟨q0, q1, q2, q3⟩ := p
  have p12 : PP 1782 11 (SFvT.F 12) := fv_PP (by norm_num)
  have p13 : PP 1782 11 (SFvT.F 13) := fv_PP (by norm_num)
  have e : suzFiveDerivedPairs[3]! = #[(1, 1), (1, 3), (0, 4), (1, 5)] := rfl
  refine pairs_of (by norm_num) cE3 fun l hl => ?_
  rw [e] at hl
  have hl' : l < 4 := by simpa using hl
  interval_cases l
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 3)[1]! = unpack 1782 11 Y ∧
      memK 3600 SFC3.T Y = true
    exact ⟨by norm_num, _, p12, bf3.1, q0⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 3)[3]! = unpack 1782 11 Y ∧
      memK 3600 SFC3.T Y = true
    exact ⟨by norm_num, _, p12.inv, bf3.2.2.1, q1⟩
  · change 0 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 3)[4]! = unpack 1782 11 Y ∧
      memK 3600 SFC3.T Y = true
    exact ⟨by norm_num, _, p13.inv, bf3.2.2.2, q2⟩
  · change 1 < 2 ∧ ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs 3)[5]! = unpack 1782 11 Y ∧
      memK 3600 SFC3.T Y = true
    exact ⟨by norm_num, _, p12.mul p12, bf3', q3⟩

theorem orOK3 : suzFiveOrbitCheck (suzFiveDArrs 3) suzFiveOrbits[3]! suzFiveOrbits[3]!.length 360
    (suzFiveOrbitCert 3) = true :=
  orbit_of (Ls := [211, 515, 714, 1336, 646, 1708]) (L := 40) (K := 9) rfl (by decide)
    (by norm_num) dA3.1 dA3.2 dP3 oFacts3 (by norm_num) (by norm_num) hO3 dO3 pO3 O3K.all
    (by norm_num)

end CertificateChecks.KernelSpor.S8147

end
