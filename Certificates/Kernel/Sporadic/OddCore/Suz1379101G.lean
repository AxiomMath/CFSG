module

public import Certificates.Kernel.Sporadic.OddCore.Suz1379101F

public section

namespace CertificateChecks.KernelSpor.S1379101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem foundR {a X : Nat} (hq : r32 FR a < 8192) (hX : RT (r32 FR a) = X) :
    found (indexOf (penumRec 1782 11 8192 RT RPL).tabs) (penumRec 1782 11 8192 RT RPL).tabs
      (unpack 1782 11 X) = true :=
  penum_found_sound ptR hq hX

theorem found2 {a X : Nat} (hq : r32 F2 a < 512) (hX : N2T (r32 F2 a) = X) :
    found (indexOf (penumRec 1782 11 512 N2T N2PL).tabs) (penumRec 1782 11 512 N2T N2PL).tabs
      (unpack 1782 11 X) = true :=
  penum_found_sound pt2 hq hX

theorem found3 {a X : Nat} (hq : r32 F3 a < 64) (hX : N3T (r32 F3 a) = X) :
    found (indexOf (penumRec 1782 11 64 N3T N3PL).tabs) (penumRec 1782 11 64 N3T N3PL).tabs
      (unpack 1782 11 X) = true :=
  penum_found_sound pt3 hq hX

theorem invsR : invsOK 1782 (rArrs ()) ((rArrs ()).map (invCand 1782)) = true := by
  unfold invsOK
  rw [Array.size_map, rA_size]
  simp only [beq_self_eq_true, Bool.true_and]
  refine allB fun k hk => ?_
  obtain ⟨cR, cRI, -⟩ := ok_spec (rA_facts hk).2
  have h := kRIAll k hk
  unfold kRI at h
  rw [rI_get hk, (rA_facts hk).1, CFSG.KC.L34KSnd.size_unpack, comp_u cRI cR, idT,
    Nat.eq_of_beq_eq_true h]
  simp

theorem rCheck_ok : rCheck (rArrs ()) (rEnum ()) = true := by
  unfold rCheck
  have h1 : allBelow 4 (fun i => CFSG.Sporadic.SuzOddCore.permOK 1782 (rArrs ())[i]!) = true :=
    allB fun i hi => by rw [(rA_facts hi).1]; exact mperm_of_ok (rA_facts hi).2
  rw [h1, encR.1, encR.2, rec_size]
  rfl

theorem n2Check_ok : n2Check (rArrs ()) ((rArrs ()).map (invCand 1782)) (g2uArrs ()) (g2vArrs ())
    (n2Arrs ()) (rEnum ()) (idxR ()) (n2Enum ()) = true := by
  unfold n2Check idxR
  rw [encR.1, enc2.1, enc2.2, rec_size]
  have hA : allBelow 7 (fun j => CFSG.Sporadic.SuzOddCore.permOK 1782 (g2uArrs ())[j]! &&
      CFSG.Sporadic.SuzOddCore.permOK 1782 (g2vArrs ())[j]!) = true :=
    allB fun j hj => by
      rw [(g2u_facts hj).1, (g2v_facts hj).1, mperm_of_ok (g2u_facts hj).2.1,
        mperm_of_ok (g2v_facts hj).2.1]
      rfl
  have hB : allBelow 7 (fun j =>
      found (indexOf (penumRec 1782 11 8192 RT RPL).tabs) (penumRec 1782 11 8192 RT RPL).tabs
        (g2uArrs ())[j]! &&
      found (indexOf (penumRec 1782 11 8192 RT RPL).tabs) (penumRec 1782 11 8192 RT RPL).tabs
        (g2vArrs ())[j]!) = true :=
    allB fun j hj => by
      rw [(g2u_facts hj).1, (g2v_facts hj).1, foundR (X := fr j) (g2u_facts hj).2.2 rfl,
        foundR (X := fr (7 + j)) (g2v_facts hj).2.2 rfl]
      rfl
  have hC : allBelow 7 (fun j => CFSG.Sporadic.SuzOddCore.permOK 1782 (n2Arrs ())[j]!) = true :=
    allB fun j hj => by rw [(n2_facts hj).1]; exact mperm_of_ok (n2_facts hj).2
  have hE : normalOK 1782 (penumRec 1782 11 512 N2T N2PL).tabs (rArrs ())
      ((rArrs ()).map (invCand 1782)) (n2Arrs ()) = true := by
    unfold normalOK
    rw [invsR, Bool.true_and, rA_size, show (n2Arrs ()).size = 7 by unfold n2Arrs n2ArrOf; simp]
    refine allB fun j hj => allB fun i hi => ?_
    have h := kN2All (7 * j + i) (by have : 7 * j + i < 28 := (by omega); exact this)
    unfold kN2 conjIn at h
    rw [show (7 * j + i) / 7 = j by omega, show (7 * j + i) % 7 = i by omega] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨q1, e1, q2, e2⟩ := h
    obtain ⟨cG, cGI, -⟩ := ok_spec (rA_facts hj).2
    obtain ⟨cX, -, -⟩ := ok_spec (n2_facts hi).2
    unfold conjTab
    rw [(rA_facts hj).1, rI_get hj, (n2_facts hi).1, comp_u cG cX, comp_u (cpc cG cX) cGI,
      comp_u cGI cX, comp_u (cpc cGI cX) cG, found2 q1 (Nat.eq_of_beq_eq_true e1),
      found2 q2 (Nat.eq_of_beq_eq_true e2)]
    rfl
  have hF : allBelow 4 (fun i => allBelow 4 (fun j =>
      found (indexOf (penumRec 1782 11 512 N2T N2PL).tabs) (penumRec 1782 11 512 N2T N2PL).tabs
        (commA (rArrs ())[i]! (rArrs ())[j]!))) = true := by
    refine allB fun i hi => allB fun j hj => ?_
    have h := kC2All (4 * i + j) (by have : 4 * i + j < 16 := (by omega); exact this)
    unfold kC2 at h
    rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    rw [commA_u (rA_facts hi).1 (rA_facts hj).1 (rA_facts hi).2 (rA_facts hj).2,
      found2 h.1 (Nat.eq_of_beq_eq_true h.2)]
  rw [hA, hB, hC, hE, hF]
  rfl

end CertificateChecks.KernelSpor.S1379101

end
