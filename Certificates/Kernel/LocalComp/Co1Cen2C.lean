module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CTests
public import Certificates.Kernel.LocalComp.Co1Cen2CChk
public import Certificates.Kernel.Co1B.C2047
public import CFSG.Certificates.Kernel.LocalCompCo1PWSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co1Cen2C

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KD.Co1B CFSG.KC.Co1PW
open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative
open CFSG.ComponentClassification.RankTwoSporadic.Co1 CertificateChecks.KernelSporSch.Co1Packed
open CFSG.KC.Co1End
open CertificateChecks.KernelCo1B.C2047 (IC QM RK iotaC_u qRows_get qRows_len gt_eq hN
  root_getD roots_len)
open CFSG.KC.Co1B (mulWK)

theorem mulU (X Y : Nat) : mul (unpack 24 24 X) (unpack 24 24 Y) = unpack 24 24 (mulWK X Y) :=
  CFSG.KS.SporSch.M24.mul_unpackW X Y

theorem q_eq (h : allN 11 (fun l => Nat.beq (G.M (3 + l)) (QM l)) = true) :
    twoCQRows = (List.range 11).map fun l => unpack 24 24 (G.M (3 + l)) := by
  apply List.ext_getElem (by simp [qRows_len])
  intro l hl _
  have hl' : l < 11 := by rwa [qRows_len] at hl
  have hq := qRows_get hl'
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hq
  rw [hq, List.getElem_map, List.getElem_range, Nat.eq_of_beq_eq_true (MatL.allN_iff.1 h l hl')]

theorem map_range11 {α : Type} (f : Nat → α) :
    (List.range 11).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] := rfl

theorem map_range14 {α : Type} (f : Nat → α) : (List.range 14).map f =
    [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13] := rfl

theorem base_eq : co1Cen2CBase = (List.range 14).map fun i => unpack 24 24 (G.M i) := by
  have h := kG0
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have ha : PA = SA := rfl
  have hb : PB = SB := rfl
  unfold co1Cen2CBase
  rw [aR_u, bR_u, iotaC_u, q_eq h3, ha, hb, ← h0, ← h1, ← h2]
  simp only [map_range11, map_range14, Nat.reduceAdd]

theorem glob_eq : dag co1Cen2CBase (co1Cen2CGlobal.map decWord) =
    (rowsOf G.M G.N, rowsOf G.MI G.N, true) := dagK_sound base_eq kG

theorem e1 : entriesR co1Cen2CBase (co1Cen2CGlobal.map decWord) co1Cen2CS1 =
    [G.M 222, G.M 223, G.M 231].map (unpack 24 24) := by
  have h := kS
  rw [List.all_append, Bool.and_eq_true] at h
  rw [entriesR_of glob_eq h.1]
  simp only [co1Cen2CS1, List.map_cons, List.map_nil, Nat.reduceSub]

theorem e2 : entriesR co1Cen2CBase (co1Cen2CGlobal.map decWord) co1Cen2CS2 =
    [G.M 226, G.M 228].map (unpack 24 24) := by
  have h := kS
  rw [List.all_append, Bool.and_eq_true] at h
  rw [entriesR_of glob_eq h.2]
  simp only [co1Cen2CS2, List.map_cons, List.map_nil, Nat.reduceSub]

theorem map_range2 {α : Type} (f : Nat → α) : (List.range 2).map f = [f 0, f 1] := rfl

theorem map_range3 {α : Type} (f : Nat → α) : (List.range 3).map f = [f 0, f 1, f 2] := rfl

theorem map_range5 {α : Type} (f : Nat → α) :
    (List.range 5).map f = [f 0, f 1, f 2, f 3, f 4] := rfl

theorem d1_eq : dag ([G.M 222, G.M 223, G.M 231].map (unpack 24 24)) (co1Cen2CD1.map decWord) =
    (rowsOf P1.M P1.N, rowsOf P1.MI P1.N, true) := by
  refine dagK_sound ?_ kD1
  have h := kP1
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  rw [map_range3, ← h0, ← h1, ← h2, List.map_cons, List.map_cons, List.map_cons, List.map_nil]

theorem d2_eq : dag ([G.M 226, G.M 228].map (unpack 24 24)) (co1Cen2CD2.map decWord) =
    (rowsOf P2.M P2.N, rowsOf P2.MI P2.N, true) := by
  refine dagK_sound ?_ kD2
  have h := kP2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h1⟩ := h
  rw [map_range2, ← h0, ← h1, List.map_cons, List.map_cons, List.map_nil]

theorem SK_map : SK.map (unpack 24 24) =
    [G.M 222, G.M 223, G.M 231].map (unpack 24 24) ++ [G.M 226, G.M 228].map (unpack 24 24) :=
  rfl

theorem r_eq : dag ([G.M 222, G.M 223, G.M 231].map (unpack 24 24) ++
    [G.M 226, G.M 228].map (unpack 24 24)) (co1Cen2CRD.map decWord) =
    (rowsOf R.M R.N, rowsOf R.MI R.N, true) := by
  refine dagK_sound ?_ kR
  have e : ∀ i < 5, R.M i = SK.getD i 0 := fun i hi =>
    Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kR0 i hi)
  rw [← SK_map, map_range5, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e 4 (by decide)]
  rfl

theorem roots_eq : twoCRoots = [unpack 24 24 (RK 0), unpack 24 24 (RK 1), unpack 24 24 (RK 2)] := by
  apply List.ext_getElem (by rw [roots_len]; rfl)
  intro i hi _
  have hi3 : i < 3 := by rwa [roots_len] at hi
  rw [← List.getD_eq_getElem _ (one ()) hi, root_getD hi3]
  interval_cases i <;> rfl

theorem re_eq : entriesR ([G.M 222, G.M 223, G.M 231].map (unpack 24 24) ++
    [G.M 226, G.M 228].map (unpack 24 24)) (co1Cen2CRD.map decWord) co1Cen2CRE = twoCRoots := by
  have h := kRe
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hk, h0⟩, h1⟩, h2⟩ := h
  rw [entriesR_of r_eq hk, roots_eq]
  simp only [co1Cen2CRE, List.map_cons, List.map_nil, Nat.reduceSub]
  rw [h0, h1, h2]

@[expose] noncomputable def QTree : GTree :=
  bfsTree CertificateChecks.KernelCo1B.C2047.QT.N CertificateChecks.KernelCo1B.C2047.QT.P
    CertificateChecks.KernelCo1B.C2047.QT.PAR CertificateChecks.KernelCo1B.C2047.QT.LAB

theorem scan_ok : co1QcScanOK QTree.pts (unpack 24 24 IC)
    ([G.M 222, G.M 223, G.M 231].map (unpack 24 24) ++ [G.M 226, G.M 228].map (unpack 24 24)) =
    true := by
  unfold co1QcScanOK
  rw [← SK_map, Bool.and_eq_true, Array.all_eq_true, List.all_map]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [List.all_eq_true]
    intro s _
    rw [Function.comp_apply, ← unpackR_eq_unpack]
    exact CFSG.KC.Co1F2.validRows_unpackR _
  · have hi' : i < 2048 := by simpa [QTree, bfsTree, hN.2.1] using hi
    have h := MatL.allN_iff.1 kScan i hi'
    simp only [QTree, bfsTree, Array.getElem_ofFn]
    rw [← unpackR_eq_unpack (CertificateChecks.KernelCo1B.C2047.QT.P i), CFSG.KC.Co1F2.validRows_unpackR, unpackR_eq_unpack,
      Bool.true_and, List.any_map]
    unfold scanPt at h
    simp only [Function.comp_def, commR, mulU, ← MatL.unpack_idM]
    exact h

theorem check : co1Cen2CCheck co1Cen2CGlobal co1Cen2CS1 co1Cen2CS2 co1Cen2CD1 co1Cen2CD2
    co1Cen2CZH1 co1Cen2CZH2 co1Cen2CDec1 co1Cen2CDec2 co1Cen2CRD co1Cen2CRE = true := by
  unfold co1Cen2CCheck pwOK CFSG.ComponentClassification.RankTwoSporadic.Co1.wordsOK
  rw [e1, e2, glob_eq, d1_eq, d2_eq, r_eq, re_eq, gt_eq, iotaC_u]
  simp only [Bool.true_and, beq_self_eq_true, Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨pwCoreOK_of kD1 kW1, pwCoreOK_of kD2 kW2⟩, scan_ok⟩

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
open Certificates in
theorem cert15046 : co1Cen2CCheck co1Cen2CGlobal co1Cen2CS1 co1Cen2CS2 co1Cen2CD1 co1Cen2CD2 co1Cen2CZH1
    co1Cen2CZH2 co1Cen2CDec1 co1Cen2CDec2 co1Cen2CRD co1Cen2CRE = true := check

end CertificateChecks.KernelLC.Co1Cen2C

end
