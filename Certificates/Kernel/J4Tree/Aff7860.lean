module

public import Certificates.Data.CFSGNative.J4Tree.Aff
public import CFSG.Milestones.ASVolI.C31.J4NP.AffNative
public import CFSG.Certificates.Kernel.J4Tree.CodeSound
public import Certificates.Kernel.J4Q.QTBase
public import Certificates.Kernel.J4Q.MaskU
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Tree

open CFSG.KC.J4Tree CFSG.J4Tree.Native CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native
open CFSG.Sporadic.J4.QT CertificateChecks.KernelJ4Q

theorem x_wf : xCode.toList.all Code.wf = true := by quickRfl
theorem xi_wf : xiCode.toList.all Code.wf = true := by quickRfl
theorem u_wf : uCode.toList.all Code.wf = true := by quickRfl
theorem k_wf : kCode.toList.all Code.wf = true := by quickRfl
theorem sec_wf : secCb.toList.all V2.wf = true := by quickRfl

theorem sec_ok : secOK = true := by quickRfl

theorem shape_ok : shapeOK = true := by
  unfold shapeOK
  simp only [← Array.all_toList]
  quickRfl

theorem literals_ok : literalsOK = true := by
  unfold literalsOK
  simp only [← Array.all_toList]
  quickRfl

theorem efaith_k : (List.range 2047).all (fun c =>
    etaCK (tblC uCode) (c + 1) / 2 ^ (12 * 0) % 2 ^ 12 != 1) = true := by quickRfl

theorem efaith_ok : eFaithOK = true :=
  (all_range_congr fun c _ => by rw [rc_row (rc_etaCode u_wf (c + 1)) (by omega)]).trans efaith_k

theorem etaInE_k : (List.range 2048).all (fun c => (List.range 11).all fun i =>
    etaCK (tblC uCode) c / 2 ^ (12 * (i + 1)) % 2 ^ 12 == 2 ^ (i + 1)) = true := by quickRfl

theorem etaInE_ok : etaInEOK = true :=
  (all_range_congr fun c _ => inE_eq (rc_etaCode u_wf c)).trans etaInE_k

theorem tau_k : (List.range 2048).all (fun t =>
    etaCK (tblC uCode) (tauInv t) / 2 ^ (12 * 0) % 2 ^ 12 == 1 + 2 * t) = true := by quickRfl

theorem tau_ok : tauOK = true :=
  (all_range_congr fun t _ => by rw [rc_row (rc_etaCode u_wf (tauInv t)) (by omega)]).trans tau_k

theorem rho_k : (List.range 3).all (fun k =>
    (secCb.toList.map (fun v => projN (vecJ rm (v2N v) (getN one [L0, L1, L2] k))) ==
      (xCode[k]?.getD 1).rows.toList) &&
    (secCb.toList.map (fun v => projN (vecJ rm (v2N v) (getN one [L0i, L1i, L2i] k))) ==
      (xiCode[k]?.getD 1).rows.toList)) = true := by quickRfl

theorem compat_k : (List.range 3).all (fun k => (List.range 112).all fun i =>
    projN (rowJ rm (getN one [L0, L1, L2] k) i) ==
      CFSG.Sporadic.SmallF2.Native.vecMulN 12 (xCode[k]?.getD 1).rows (projP[i]?.getD 0)) = true := by
  quickRfl

theorem loc_ok : locCodesOK (locMats ()) (locInvs ()) = true := by
  unfold locCodesOK
  refine List.all_eq_true.2 fun k hk => ?_
  have hk3 := List.mem_range.1 hk
  have hr := List.all_eq_true.1 rho_k k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  have hX : rho12 ((locMats ())[k]?.getD (idRows ())) = xCode[k]?.getD 1 :=
    rows_eq_of_toList ((rho12_rows hK sec_wf (loc_gens k)).trans hr.1)
  have hXi : rho12 ((locInvs ())[k]?.getD (idRows ())) = xiCode[k]?.getD 1 :=
    rows_eq_of_toList ((rho12_rows hK sec_wf (loc_invs k)).trans hr.2)
  have hc : compatOK ((locMats ())[k]?.getD (idRows ())) = true := by
    unfold compatOK
    simp only [hX]
    refine (all_range_congr fun i hi => ?_).trans (List.all_eq_true.1 compat_k k hk)
    rw [proj12_eq, row_v2N hK (loc_gens k) hi]
  rw [hc, hX, hXi, beq_self_eq_true, beq_self_eq_true]
  rfl

theorem affChecks_ok : affChecks () = true := by
  unfold affChecks
  rw [sec_ok, loc_ok, efaith_ok, etaInE_ok, tau_ok, shape_ok, literals_ok]
  rfl

theorem wordsU_k : (List.range 11).all (fun j => Nat.beq
    (wordCK (tblC xCode) (tblC xiCode) (uWordK j)) ((tblC uCode).getD j oneK)) = true := by
  quickRfl

theorem wordsK_k : (List.range 4).all (fun i => Nat.beq
    (wordCK (tblC xCode) (tblC xiCode) (mkKW.getD i [])) ((tblC kCode).getD i oneK)) = true := by
  quickRfl

theorem affData_ok : CFSG.ASVolI.burnsideJ4NP_affDataOK () = true := by
  unfold CFSG.ASVolI.burnsideJ4NP_affDataOK
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun i hi => ?_⟩
  · rw [uWord_eq]
    exact rc_beq (rc_codeOfWord x_wf xi_wf _) (rc_get u_wf j) (List.all_eq_true.1 wordsU_k j hj)
  · rw [kWords_eq]
    exact rc_beq (rc_codeOfWord x_wf xi_wf _) (rc_get k_wf i) (List.all_eq_true.1 wordsK_k i hi)

theorem c7860 : CFSG.J4Tree.Native.affChecks () = true ∧ CFSG.ASVolI.burnsideJ4NP_affDataOK () = true := ⟨affChecks_ok, affData_ok⟩

end CertificateChecks.KernelJ4Tree

end
