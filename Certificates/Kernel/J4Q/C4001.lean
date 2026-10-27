module

public import CFSG.Sporadic.J4.QT2ARadNative
public import Certificates.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.QT2AData
import Certificates.Kernel.J4Q.Strs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] noncomputable def Q5s : List Nat := [Q5_0, Q5_1, Q5_2, Q5_3, Q5_4, Q5_5]

@[expose] noncomputable def Q5is : List Nat := [Q5i_0, Q5i_1, Q5i_2, Q5i_3, Q5i_4, Q5i_5]

theorem q5_chk : CFSG.KC.Enum.allN 6 (fun j =>
    andB (Nat.beq (getN one Q5s j) (wordJ c rm one G5 G5i (qGenK.getD (qSub5.getD j 0) [])))
      (Nat.beq (getN one Q5is j) (wordJ c rm one G5 G5i (negRev (qGenK.getD (qSub5.getD j 0) []))))) =
    true := by
  quickRfl

theorem q5_enc {j : Nat} (hj : j < 6) :
    (WfA (wR (qGenW.getD (qSub5.getD j 0) [])) ∧
      encR (wR (qGenW.getD (qSub5.getD j 0) [])) = getN one Q5s j) ∧
    (WfA (wR (invW (qGenW.getD (qSub5.getD j 0) []))) ∧
      encR (wR (invW (qGenW.getD (qSub5.getD j 0) []))) = getN one Q5is j) := by
  have h := CFSG.KS.allN_spec q5_chk j hj
  rw [andB_eq, Bool.and_eq_true] at h
  refine ⟨⟨(wR_enc _).1, ?_⟩, ⟨(wR_enc _).1, ?_⟩⟩
  · rw [(wR_enc _).2, qGenW_eq]
    exact (Nat.eq_of_beq_eq_true h.1).symm
  · rw [(wR_enc _).2, qGenW_eq, invW_eq]
    exact (Nat.eq_of_beq_eq_true h.2).symm

@[expose] noncomputable def PQ5 : List (Nat × Nat) := (List.range 6).map fun j => (j, getN one Q5s j)

@[expose] noncomputable def PQ5i : List (Nat × Nat) :=
  (List.range 6).reverse.map fun j => (j, getN one Q5is j)

theorem qWord5_enc (t : Nat) : encR (wR (qWordG qSub5 t)) = selPK c rm PQ5 t one := by
  have hP : PQ5.map Prod.fst = List.range 6 := by
    rw [PQ5, List.map_map]
    exact List.map_id _
  have := enc_selRows hK (fun j => wR (qGenW.getD (qSub5.getD j 0) [])) t PQ5 (by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact (q5_enc (List.mem_range.1 hj)).1) (idRows ()) wf_idRows
  rw [hP, enc_idRows hK] at this
  rw [wR_qWordG]
  exact this.2

theorem qWord5i_enc (t : Nat) : encR (wR (invW (qWordG qSub5 t))) = selPK c rm PQ5i t one := by
  have hP : PQ5i.map Prod.fst = (List.range 6).reverse := by
    rw [PQ5i, List.map_map]
    exact List.map_id _
  have := enc_selRows hK (fun j => wR (invW (qGenW.getD (qSub5.getD j 0) []))) t PQ5i (by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact (q5_enc (List.mem_range.1 (List.mem_reverse.1 hj))).2) (idRows ()) wf_idRows
  rw [hP, enc_idRows hK] at this
  rw [wR_invW_qWordG]
  exact this.2

theorem conj5_chk : strictB (powJ c rm one (wordJ c rm one G5 G5i y5K) y5e) (fun x =>
    distinctK (smapK (fun t => mulJ c rm (mulJ c rm (selPK c rm PQ5 t one) x) (selPK c rm PQ5i t one))
      (rangeK 64))) = true := by
  quickRfl

theorem qconj5 : chkQconj5 = true :=
  conjDistinct_of _ _ _ qWord5_enc qWord5i_enc _ _ y5R_enc.1 y5R_enc.2 conj5_chk

theorem qlet : chkQlet = true := by
  unfold chkQlet
  rw [qGenW_eq]
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A in
theorem c4001 : (chkQconj5 = true)
    ∧ (chkQlet = true) := ⟨qconj5, qlet⟩

end CertificateChecks.KernelJ4Q

end
