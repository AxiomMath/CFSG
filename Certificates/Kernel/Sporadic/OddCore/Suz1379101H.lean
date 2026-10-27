module

public import Certificates.Kernel.Sporadic.OddCore.Suz1379101G
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelSpor.S1379101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem n3Check_ok : n3Check (rArrs ()) ((rArrs ()).map (invCand 1782)) (n2Arrs ()) (g3uArrs ())
    (g3vArrs ()) (n3Arrs ()) (rEnum ()) (n2Enum ()) (idxR ()) (idxN2 ()) (n3Enum ()) = true := by
  unfold n3Check idxR idxN2
  rw [encR.1, enc2.1, enc3.1, enc3.2, rec_size]
  have hA : allBelow 5 (fun k => CFSG.Sporadic.SuzOddCore.permOK 1782 (g3uArrs ())[k]! &&
      CFSG.Sporadic.SuzOddCore.permOK 1782 (g3vArrs ())[k]!) = true :=
    allB fun k hk => by
      rw [(g3u_facts hk).1, (g3v_facts hk).1, mperm_of_ok (g3u_facts hk).2.1,
        mperm_of_ok (g3v_facts hk).2.1]
      rfl
  have hB : allBelow 5 (fun k =>
      found (indexOf (penumRec 1782 11 8192 RT RPL).tabs) (penumRec 1782 11 8192 RT RPL).tabs
        (g3uArrs ())[k]! &&
      found (indexOf (penumRec 1782 11 512 N2T N2PL).tabs) (penumRec 1782 11 512 N2T N2PL).tabs
        (g3vArrs ())[k]!) = true :=
    allB fun k hk => by
      rw [(g3u_facts hk).1, (g3v_facts hk).1, foundR (X := fr (14 + k)) (g3u_facts hk).2.2 rfl,
        found2 (X := f2 k) (g3v_facts hk).2.2 rfl]
      rfl
  have hC : allBelow 5 (fun k => CFSG.Sporadic.SuzOddCore.permOK 1782 (n3Arrs ())[k]!) = true :=
    allB fun k hk => by rw [(n3_facts hk).1]; exact mperm_of_ok (n3_facts hk).2
  have hE : normalOK 1782 (penumRec 1782 11 64 N3T N3PL).tabs (rArrs ())
      ((rArrs ()).map (invCand 1782)) (n3Arrs ()) = true := by
    unfold normalOK
    rw [invsR, Bool.true_and, rA_size, show (n3Arrs ()).size = 5 by unfold n3Arrs n3ArrOf; simp]
    refine allB fun j hj => allB fun i hi => ?_
    have h := kN3All (5 * j + i) (by have : 5 * j + i < 20 := (by omega); exact this)
    unfold kN3 conjIn at h
    rw [show (5 * j + i) / 5 = j by omega, show (5 * j + i) % 5 = i by omega] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨q1, e1, q2, e2⟩ := h
    obtain ⟨cG, cGI, -⟩ := ok_spec (rA_facts hj).2
    obtain ⟨cX, -, -⟩ := ok_spec (n3_facts hi).2
    unfold conjTab
    rw [(rA_facts hj).1, rI_get hj, (n3_facts hi).1, comp_u cG cX, comp_u (cpc cG cX) cGI,
      comp_u cGI cX, comp_u (cpc cGI cX) cG, found3 q1 (Nat.eq_of_beq_eq_true e1),
      found3 q2 (Nat.eq_of_beq_eq_true e2)]
    rfl
  have hF : allBelow 7 (fun i => allBelow 4 (fun j =>
      found (indexOf (penumRec 1782 11 64 N3T N3PL).tabs) (penumRec 1782 11 64 N3T N3PL).tabs
        (commA (n2Arrs ())[i]! (rArrs ())[j]!))) = true := by
    refine allB fun i hi => allB fun j hj => ?_
    have h := kC3All (4 * i + j) (by have : 4 * i + j < 28 := (by omega); exact this)
    unfold kC3 at h
    rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    rw [commA_u (n2_facts hi).1 (rA_facts hj).1 (n2_facts hi).2 (rA_facts hj).2,
      found3 h.1 (Nat.eq_of_beq_eq_true h.2)]
  rw [hA, hB, hC, hE, hF]
  rfl

theorem cqT : allN 8 (fun t => canonK 1782 11 (mask 11) (1782 * 11) (QT t)) = true := by
  decide +kernel

theorem kq_parts : (allN 3 fun i => Nat.beq (pc (QG i) (QG i)) e) = true ∧
    (allN 3 fun i => allN 3 fun j => Nat.beq (pc (QG i) (QG j)) (pc (QG j) (QG i))) = true ∧
    (allN 8 fun t => Nat.beq (pc (QT t) (QT t)) e) = true ∧
    (allN 6 fun i => allN 3 fun j => Nat.beq (pc (QG j) (CW i)) (pc (CW i) (QG j))) = true := by
  have h : ((allN 3 fun i => Nat.beq (pc (QG i) (QG i)) e) &&
      ((allN 3 fun i => allN 3 fun j => Nat.beq (pc (QG i) (QG j)) (pc (QG j) (QG i))) &&
      ((allN 8 fun t => Nat.beq (pc (QT t) (QT t)) e) &&
        (allN 6 fun i => allN 3 fun j => Nat.beq (pc (QG j) (CW i)) (pc (CW i) (QG j)))))) =
      true := kOne1
  simp only [Bool.and_eq_true] at h
  exact h

theorem qCheck_ok : qCheck (rArrs ()) (qArrs ()) (cArrs ()) (rEnum ()) (idxR ()) (qEnum ()) =
    true := by
  unfold qCheck idxR
  rw [encR.1, encQ.1, encQ.2, rec_size]
  obtain ⟨k1, k2, k3, k4⟩ := kq_parts
  have cq : ∀ i < 3, Cn (QG i) := fun i hi => (ok_spec (q_facts hi).2.1).1
  have cc : ∀ i < 6, Cn (CW i) := fun i hi => (ok_spec (c_facts hi).2).1
  have h1 : allBelow 3 (fun i => CFSG.Sporadic.SuzOddCore.permOK 1782 (qArrs ())[i]!) = true :=
    allB fun i hi => by rw [(q_facts hi).1]; exact mperm_of_ok (q_facts hi).2.1
  have h2 : allBelow 3 (fun i =>
      found (indexOf (penumRec 1782 11 8192 RT RPL).tabs) (penumRec 1782 11 8192 RT RPL).tabs
        (qArrs ())[i]!) = true :=
    allB fun i hi => by
      rw [(q_facts hi).1]
      exact foundR (q_facts hi).2.2.1 (q_facts hi).2.2.2.symm
  have h3 : allBelow 3 (fun i => comp 1782 (qArrs ())[i]! (qArrs ())[i]! == idTab 1782) = true :=
    allB fun i hi => by
      rw [(q_facts hi).1, comp_u (cq i hi) (cq i hi), idT,
        beq_u (cpc (cq i hi) (cq i hi)) cE]
      exact CFSG.KS.Raw.Orb.allN_iff.1 k1 i hi
  have h4 : allBelow 3 (fun i => allBelow 3 (fun j => comp 1782 (qArrs ())[i]! (qArrs ())[j]! ==
      comp 1782 (qArrs ())[j]! (qArrs ())[i]!)) = true :=
    allB fun i hi => allB fun j hj => by
      rw [(q_facts hi).1, (q_facts hj).1, comp_u (cq i hi) (cq j hj), comp_u (cq j hj) (cq i hi),
        beq_u (cpc (cq i hi) (cq j hj)) (cpc (cq j hj) (cq i hi))]
      exact CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 k2 i hi) j hj
  have h5 : allBelow 8 (fun k =>
      comp 1782 (penumRec 1782 11 8 QT QPL).tabs[k]! (penumRec 1782 11 8 QT QPL).tabs[k]! ==
        idTab 1782) = true := by
    refine allB fun k hk => ?_
    have ck : Cn (QT k) := CFSG.KS.Raw.Orb.allN_iff.1 cqT k hk
    rw [penumRec_eq]
    simp only
    rw [ofFn_get _ hk]
    simp only
    rw [comp_u ck ck, idT, beq_u (cpc ck ck) cE]
    exact CFSG.KS.Raw.Orb.allN_iff.1 k3 k hk
  have h6 : allBelow 6 (fun i => CFSG.Sporadic.SuzOddCore.permOK 1782 (cArrs ())[i]!) = true :=
    allB fun i hi => by rw [(c_facts hi).1]; exact mperm_of_ok (c_facts hi).2
  have h7 : allBelow 6 (fun i => allBelow 3 (fun j => comp 1782 (qArrs ())[j]! (cArrs ())[i]! ==
      comp 1782 (cArrs ())[i]! (qArrs ())[j]!)) = true :=
    allB fun i hi => allB fun j hj => by
      rw [(q_facts hj).1, (c_facts hi).1, comp_u (cq j hj) (cc i hi), comp_u (cc i hi) (cq j hj),
        beq_u (cpc (cq j hj) (cc i hi)) (cpc (cc i hi) (cq j hj))]
      exact CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 k4 i hi) j hj
  rw [h1, h2, h3, h4, h5, h6, h7]
  rfl

end CertificateChecks.KernelSpor.S1379101

end
