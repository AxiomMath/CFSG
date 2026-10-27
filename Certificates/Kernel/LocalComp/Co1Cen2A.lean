module

public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.LocalCompCo1PWSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2ATests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2AData
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.LocalComp.Co1Cen2AIn
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData
public import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.Iota
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelLC.Co1Cen2A.I CertificateChecks.KernelLC.Co1Cen2A.iotaDag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2A.G CertificateChecks.KernelLC.Co1Cen2A.globDag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2A.P1 CertificateChecks.KernelLC.Co1Cen2A.pw1Dag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2A.P2 CertificateChecks.KernelLC.Co1Cen2A.pw2Dag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2A.Q CertificateChecks.KernelLC.Co1Cen2A.qDag

namespace CertificateChecks.KernelLC.Co1Cen2A

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1 CertificateChecks.KernelSporSch.Co1Packed
open CFSG.KC.Co1End CFSG.KC.Co1PW

@[expose] def encI (i : Int) : Nat := if 0 ≤ i then 2 * i.toNat else 2 * (-i).toNat + 1

theorem decLetter_encI (i : Int) : decLetter (encI i) = i := by
  unfold decLetter encI
  split_ifs <;> omega

@[expose] def iotaWs : List (List Nat) := iotaDerivs.map (List.map encI)

theorem iotaWs_dec : iotaWs.map decWord = iotaDerivs := by
  unfold iotaWs decWord
  rw [List.map_map]
  conv_rhs => rw [← List.map_id iotaDerivs]
  apply List.map_congr_left
  intro w _
  rw [Function.comp_apply, List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun i _ => decLetter_encI i

theorem kH : (wordEqK PA PB CFSG.Sporadic.Co1Schreier.Data.stabWord0 (I.M 0) &&
    wordEqK PA PB CFSG.Sporadic.Co1Schreier.Data.stabWord1 (I.M 1)) = true := by quickRfl

theorem kI : dagK I.M I.MI 2 I.N iotaWs = true := by quickRfl

theorem kIN : (Nat.blt 51 I.N) = true := by quickRfl

theorem kG0 : (Nat.beq (G.M 0) PA && Nat.beq (G.M 1) PB && Nat.beq (G.M 2) (I.M 23) &&
    Nat.beq (G.M 3) (I.M 36) && Nat.beq (G.M 4) (I.M 37) && Nat.beq (G.M 5) (I.M 38) &&
    Nat.beq (G.M 6) (I.M 39) && Nat.beq (G.M 7) (I.M 40) && Nat.beq (G.M 8) (I.M 41) &&
    Nat.beq (G.M 9) (I.M 42) && Nat.beq (G.M 10) (I.M 43)) = true := by quickRfl

theorem kG : dagK G.M G.MI 11 G.N co1Cen2AGlobal = true := by quickRfl

theorem kS : ((co1Cen2AS1 ++ co1Cen2AS2).all (okK G.N)) = true := by quickRfl

theorem kP1 : (Nat.beq (P1.M 0) (G.M 163) && Nat.beq (P1.M 1) (G.M 165) &&
    Nat.beq (P1.M 2) (G.M 176) && Nat.beq (P1.M 3) (G.M 179)) = true := by quickRfl

theorem kP2 : (Nat.beq (P2.M 0) (G.M 169) && Nat.beq (P2.M 1) (G.M 173) &&
    Nat.beq (P2.M 2) (G.M 182) && Nat.beq (P2.M 3) (G.M 185)) = true := by quickRfl

theorem kD1 : dagK P1.M P1.MI 4 P1.N co1Cen2AD1 = true := by quickRfl

theorem kD2 : dagK P2.M P2.MI 4 P2.N co1Cen2AD2 = true := by quickRfl

theorem kW1 : pwCoreK P1.M P1.MI P1.N [G.M 163, G.M 165, G.M 176, G.M 179] co1Cen2AZH1.1
    co1Cen2AZH1.2 co1Cen2ADec1 (I.M 23) = true := by quickRfl

theorem kW2 : pwCoreK P2.M P2.MI P2.N [G.M 169, G.M 173, G.M 182, G.M 185] co1Cen2AZH2.1
    co1Cen2AZH2.2 co1Cen2ADec2 (I.M 23) = true := by quickRfl

theorem kQ0 : (Nat.beq (Q.M 0) (G.M 163) && Nat.beq (Q.M 1) (G.M 165) &&
    Nat.beq (Q.M 2) (G.M 176) && Nat.beq (Q.M 3) (G.M 179) && Nat.beq (Q.M 4) (G.M 169) &&
    Nat.beq (Q.M 5) (G.M 173) && Nat.beq (Q.M 6) (G.M 182) && Nat.beq (Q.M 7) (G.M 185)) =
    true := by quickRfl

theorem kQ : dagK Q.M Q.MI 8 Q.N co1Cen2AQD = true := by quickRfl

theorem kQe : (co1Cen2AQE.all (okK Q.N) && Nat.beq (Q.M 8) (I.M 36) &&
    Nat.beq (Q.M 9) (I.M 37) && Nat.beq (Q.M 10) (I.M 38) && Nat.beq (Q.M 11) (I.M 39) &&
    Nat.beq (Q.M 12) (I.M 40) && Nat.beq (Q.M 13) (I.M 41) && Nat.beq (Q.M 14) (I.M 42) &&
    Nat.beq (Q.M 15) (I.M 43)) = true := by quickRfl

theorem iota_eq : iotaRows = rowsOf I.M I.N := by
  have h := kH
  simp only [Bool.and_eq_true] at h
  have h0 := wordEqK_sound h.1 [inv aR, inv bR]
  have h1 := wordEqK_sound h.2 [inv aR, inv bR]
  rw [← aR_u, ← bR_u] at h0 h1
  have hb : [hRows0, hRows1] = (List.range 2).map fun i => unpack 24 24 (I.M i) := by
    unfold hRows0 hRows1
    rw [h0, h1]
    rfl
  have := dagK_sound hb kI
  rw [iotaWs_dec] at this
  unfold iotaRows
  rw [this]

theorem iotaRow {k : Nat} (hk : k < I.N) :
    iotaRows.getD k one = unpack 24 24 (I.M k) := by
  rw [iota_eq]
  simp [List.getD_eq_getElem?_getD, hk]

theorem hIN : 51 < I.N := by
  have h := kIN
  rwa [Nat.blt_eq] at h

theorem map_range4 {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

theorem map_range8 {α : Type} (f : Nat → α) :
    (List.range 8).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := rfl

theorem map_range11 {α : Type} (f : Nat → α) :
    (List.range 11).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] := rfl

theorem iotaA_u : iotaARows = unpack 24 24 (I.M 23) := iotaRow (by have := hIN; omega)

theorem iotaQ_u {k : Nat} (hk : k < 8) : iotaQRows k = unpack 24 24 (I.M (36 + k)) :=
  iotaRow (by have := hIN; omega)

theorem base_eq : co1Cen2ABase = (List.range 11).map fun i => unpack 24 24 (G.M i) := by
  have h := kG0
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  unfold co1Cen2ABase co1Cen2AQRows
  rw [aR_u, bR_u, iotaA_u, iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num),
    iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num),
    iotaQ_u (by norm_num), map_range11, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem glob_eq : dag co1Cen2ABase (co1Cen2AGlobal.map decWord) =
    (rowsOf G.M G.N, rowsOf G.MI G.N, true) := dagK_sound base_eq kG

theorem e1 : entriesR co1Cen2ABase (co1Cen2AGlobal.map decWord) co1Cen2AS1 =
    [G.M 163, G.M 165, G.M 176, G.M 179].map (unpack 24 24) := by
  have h := kS
  rw [List.all_append, Bool.and_eq_true] at h
  rw [entriesR_of glob_eq h.1]
  simp only [co1Cen2AS1, List.map_cons, List.map_nil, Nat.reduceSub]

theorem e2 : entriesR co1Cen2ABase (co1Cen2AGlobal.map decWord) co1Cen2AS2 =
    [G.M 169, G.M 173, G.M 182, G.M 185].map (unpack 24 24) := by
  have h := kS
  rw [List.all_append, Bool.and_eq_true] at h
  rw [entriesR_of glob_eq h.2]
  simp only [co1Cen2AS2, List.map_cons, List.map_nil, Nat.reduceSub]

theorem d1_eq : dag ([G.M 163, G.M 165, G.M 176, G.M 179].map (unpack 24 24))
    (co1Cen2AD1.map decWord) = (rowsOf P1.M P1.N, rowsOf P1.MI P1.N, true) := by
  refine dagK_sound ?_ kD1
  have h := kP1
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  rw [map_range4, ← h0, ← h1, ← h2, ← h3, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_nil]

theorem d2_eq : dag ([G.M 169, G.M 173, G.M 182, G.M 185].map (unpack 24 24))
    (co1Cen2AD2.map decWord) = (rowsOf P2.M P2.N, rowsOf P2.MI P2.N, true) := by
  refine dagK_sound ?_ kD2
  have h := kP2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  rw [map_range4, ← h0, ← h1, ← h2, ← h3, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_nil]

theorem q_eq : dag ([G.M 163, G.M 165, G.M 176, G.M 179].map (unpack 24 24) ++
    [G.M 169, G.M 173, G.M 182, G.M 185].map (unpack 24 24)) (co1Cen2AQD.map decWord) =
    (rowsOf Q.M Q.N, rowsOf Q.MI Q.N, true) := by
  refine dagK_sound ?_ kQ
  have h := kQ0
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [map_range8, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]

theorem qe_eq : entriesR ([G.M 163, G.M 165, G.M 176, G.M 179].map (unpack 24 24) ++
    [G.M 169, G.M 173, G.M 182, G.M 185].map (unpack 24 24)) (co1Cen2AQD.map decWord)
    co1Cen2AQE = co1Cen2AQRows := by
  have h := kQe
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [entriesR_of q_eq hk]
  unfold co1Cen2AQRows
  rw [iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num),
    iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num), iotaQ_u (by norm_num)]
  simp only [co1Cen2AQE, List.map_cons, List.map_nil, Nat.reduceSub, Nat.reduceAdd]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem check : co1Cen2ACheck co1Cen2AGlobal co1Cen2AS1 co1Cen2AS2 co1Cen2AD1 co1Cen2AD2
    co1Cen2AZH1 co1Cen2AZH2 co1Cen2ADec1 co1Cen2ADec2 co1Cen2AQD co1Cen2AQE = true := by
  unfold co1Cen2ACheck pwOK wordsOK
  rw [e1, e2, glob_eq, d1_eq, d2_eq, q_eq, qe_eq, iotaA_u]
  simp only [Bool.true_and, beq_self_eq_true, Bool.and_true, Bool.and_eq_true]
  exact ⟨pwCoreOK_of kD1 kW1, pwCoreOK_of kD2 kW2⟩

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
open Certificates in
theorem cert15044 : co1Cen2ACheck co1Cen2AGlobal co1Cen2AS1 co1Cen2AS2 co1Cen2AD1 co1Cen2AD2 co1Cen2AZH1
    co1Cen2AZH2 co1Cen2ADec1 co1Cen2ADec2 co1Cen2AQD co1Cen2AQE = true := check

end CertificateChecks.KernelLC.Co1Cen2A

end
