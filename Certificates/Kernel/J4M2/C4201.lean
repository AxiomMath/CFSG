module

public import Certificates.Data.J4M2.QStruct
public import Certificates.Kernel.J4M2.Base
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q

theorem enc_ite {b : Bool} {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x)
    (hY : WfA Y ∧ encR Y = y) :
    WfA (if b then X else Y) ∧ encR (if b then X else Y) = if b then x else y := by
  cases b
  · exact hY
  · exact hX

theorem any_range_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).any f = (List.range n).any g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.any_append, List.any_append,
      any_range_congr fun i hi => h i (Nat.lt_succ_of_lt hi), List.any_cons, List.any_cons,
      h n (Nat.lt_succ_self n), List.any_nil, List.any_nil]

theorem qq_enc {i j : Nat} (hi : i < 12) (hj : j < 12) :
    WfA (mulT qM[i]! qT[j]!) ∧ encR (mulT qM[i]! qT[j]!) = mulJ c rm (getN one QAs i) (getN one QAs j) := by
  rw [qT_get hj, mulT_frTable]
  exact mul_enc hK (qM_enc hi) (qM_enc hj)

@[expose] noncomputable def bcK (j : Nat) : Nat :=
  (List.range 12).foldl (fun m i =>
    if (!Nat.beq (mulJ c rm (getN one QAs i) (getN one QAs j))
      (mulJ c rm (getN one QAs j) (getN one QAs i))) = true then m + 2 ^ i else m) 0

@[expose] def ndOf (bs : List Nat) : Bool :=
  (List.range 4096).all fun e => e == 0 || (List.range 12).any fun j => parity12 (e &&& bs.getD j 0)

theorem bcol_eq {j : Nat} (hj : j < 12) : bcol j = bcK j := by
  unfold bcol bcK
  refine foldl_congr_mem _ _ fun i hi m => ?_
  have hi' := List.mem_range.1 hi
  unfold qNC
  rw [eqRows_of (qq_enc hi' hj) (qq_enc hj hi')]

theorem nondeg_eq : chkNondeg = ndOf (smapK bcK (rangeK 12)) := by
  unfold chkNondeg ndOf
  rw [smapK_eq, rangeK_eq]
  refine all_range_congr fun e _ => ?_
  congr 1
  refine any_range_congr fun j hj => ?_
  have e1 : bcols[j]! = bcK j := by
    rw [bcols, get!_range_map bcol hj, bcol_eq hj]
  have e2 : ((List.range 12).map bcK).getD j 0 = bcK j := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  rw [e1, e2]

theorem nondeg_ok : ndOf (smapK bcK (rangeK 12)) = true := by quickRfl

theorem zComm_enc : WfA zComm ∧ encR zComm = mulJ c rm (mulJ c rm (mulJ c rm (getN one QAs 0)
    (getN one QAs 1)) (getN one QIs 0)) (getN one QIs 1) := by
  unfold zComm
  rw [qIT_get (by decide), qIT_get (by decide), mulT_frTable, mulT_frTable]
  exact mul_enc hK (mul_enc hK (qq_enc (by decide) (by decide)) (qI_enc (by decide)))
    (qI_enc (by decide))

@[expose] noncomputable def relK (k : Nat) : Bool :=
  Nat.beq (mulJ c rm (getN one QAs k) (getN one QIs k)) one &&
    Nat.beq (mulJ c rm (getN one QAs k) ZM) (mulJ c rm ZM (getN one QAs k)) &&
    (Nat.beq (mulJ c rm (getN one QAs k) (getN one QAs k)) one ||
      Nat.beq (mulJ c rm (getN one QAs k) (getN one QAs k)) ZM)

@[expose] noncomputable def pairK (i j : Nat) : Bool :=
  Nat.beq (mulJ c rm (getN one QAs i) (getN one QAs j)) (mulJ c rm (getN one QAs j) (getN one QAs i)) ||
    Nat.beq (mulJ c rm (getN one QAs i) (getN one QAs j))
      (mulJ c rm (mulJ c rm (getN one QAs j) (getN one QAs i)) ZM)

theorem rel_ok : (Nat.beq (mulJ c rm (mulJ c rm (mulJ c rm (getN one QAs 0)
    (getN one QAs 1)) (getN one QIs 0)) (getN one QIs 1)) ZM && !Nat.beq ZM one &&
    Nat.beq (mulJ c rm ZM ZM) one && (List.range 12).all relK &&
    (List.range 12).all fun i => (List.range 12).all fun j => pairK i j) = true := by
  quickRfl

theorem qrel_ok : chkQRel = true := by
  have hz := zM_enc
  have rel := rel_ok
  simp only [Bool.and_eq_true] at rel
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := rel
  unfold chkQRel
  have hw : wfR zM = true := wf_bool hz.1
  rw [nondeg_eq, nondeg_ok, Bool.and_true, eqRows_of zComm_enc hz, h1, hw,
    eqRows_of hz (id_enc hK), zT_eq, mulT_frTable, eqRows_of (mul_enc hK hz hz) (id_enc hK)]
  simp only [Bool.true_and]
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨h2, h3⟩, ?_⟩, ?_⟩
  · rw [← h4]
    refine all_range_congr fun k hk => ?_
    rw [qIT_get hk, qT_get hk]
    simp only [mulT_frTable]
    rw [eqRows_of (mul_enc hK (qM_enc hk) (qI_enc hk)) (id_enc hK),
      eqRows_of (mul_enc hK (qM_enc hk) hz) (mul_enc hK hz (qM_enc hk)),
      eqRows_of (mul_enc hK (qM_enc hk) (qM_enc hk)) (id_enc hK),
      eqRows_of (mul_enc hK (qM_enc hk) (qM_enc hk)) hz]
    rfl
  · rw [← h5]
    refine all_range_congr fun i hi => all_range_congr fun j hj => ?_
    rw [mulT_frTable, eqRows_of (qq_enc hi hj) (qq_enc hj hi),
      eqRows_of (qq_enc hi hj) (mul_enc hK (qq_enc hj hi) hz)]
    rfl

@[expose] noncomputable def cmiK : Nat := mulJ c rm (mulJ c rm (mulJ c rm YB YA) (oiK 1)) (oiK 0)

theorem cinv_chk : (canonJ pad cmiK && Nat.beq (mulJ c rm cmK cmiK) one) = true := by quickRfl

theorem cInv_enc : WfA (invRows cMat) ∧ encR (invRows cMat) = cmiK := by
  have h := cinv_chk
  rw [Bool.and_eq_true] at h
  exact invRows_enc hK cMat_enc.1 h.1 (by rw [cMat_enc.2]; exact h.2)

theorem qc_chk : (Nat.beq (mulJ c rm cmK cmiK) one && (List.range 12).all fun i =>
    Nat.beq (mulJ c rm (mulJ c rm cmK (getN one QAs i)) cmiK)
      (qProdK cNormData[i]!.1 cNormData[i]!.2)) = true := by
  quickRfl

theorem qc_ok : chkQC = true := by
  rw [← qc_chk]
  unfold chkQC
  dsimp only
  rw [mulT_frTable, eqRows_of (mul_enc hK cMat_enc cInv_enc) (id_enc hK)]
  congr 1
  refine all_range_congr fun i hi => ?_
  rw [qT_get hi, mulT_frTable, mulT_frTable,
    eqRows_of (mul_enc hK (mul_enc hK cMat_enc (qM_enc hi)) cInv_enc) (qProd_enc _ _)]

@[expose] noncomputable def commK (l : List (Nat × Nat)) : Nat :=
  l.foldl (fun acc p => mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm acc (gmK p.1))
    (getN one QAs p.2)) (oiK (p.1 - 12))) (getN one QIs p.2)) one

theorem commProd_enc (l : List (Nat × Nat)) (hl : ∀ p ∈ l, 12 ≤ p.1 ∧ p.1 < 17 ∧ p.2 < 12) :
    WfA (commProd l) ∧ encR (commProd l) = commK l := by
  have key : ∀ (l : List (Nat × Nat)), (∀ p ∈ l, 12 ≤ p.1 ∧ p.1 < 17 ∧ p.2 < 12) →
      ∀ (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
      WfA (l.foldl (fun acc p => mulT (mulT (mulT (mulT acc gtabs[p.1]!) qT[p.2]!)
        oIT[p.1 - 12]!) qIT[p.2]!) acc) ∧
      encR (l.foldl (fun acc p => mulT (mulT (mulT (mulT acc gtabs[p.1]!) qT[p.2]!)
        oIT[p.1 - 12]!) qIT[p.2]!) acc) =
        l.foldl (fun acc p => mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm acc (gmK p.1))
          (getN one QAs p.2)) (oiK (p.1 - 12))) (getN one QIs p.2)) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons p l ih =>
      intro hl acc a h
      obtain ⟨h1, h2, h3⟩ := hl p List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      have ho := oInv_enc (i := p.1 - 12) (by omega)
      have e : 12 + (p.1 - 12) = p.1 := by omega
      rw [e] at ho
      rw [gtabs_get (by omega), qT_get h3, oIT_get (by omega), oI_get (by omega), e,
        qIT_get h3, mulT_frTable, mulT_frTable, mulT_frTable, mulT_frTable]
      exact mul_enc hK (mul_enc hK (mul_enc hK (mul_enc hK h (gm_enc (by omega))) (qM_enc h3)) ho)
        (qI_enc h3)
  exact key l hl (idRows ()) one (id_enc hK)

@[expose] def perfB (k : Nat) : Bool := perfData[k]!.1.all fun p => 12 ≤ p.1 && p.1 < 17 && p.2 < 12

theorem perf_chk : ((List.range 5).all (fun i => Nat.beq (mulJ c rm (gmK (12 + i)) (oiK i)) one) &&
    (List.range 12).all fun k => perfB k && Nat.beq (if perfData[k]!.2 then
      mulJ c rm (commK perfData[k]!.1) ZM else commK perfData[k]!.1) (getN one QAs k)) = true := by
  quickRfl

theorem qperf_ok : chkQPerf = true := by
  rw [← perf_chk]
  unfold chkQPerf
  congr 1
  · refine all_range_congr fun i hi => ?_
    rw [oIT_get hi, oI_get hi, mulT_frTable,
      eqRows_of (mul_enc hK (gm_enc (by omega)) (oInv_enc hi)) (id_enc hK)]
  · refine all_range_congr fun k hk => ?_
    change (perfB k && _) = (perfB k && _)
    cases hb : perfB k
    · rfl
    · have hl : ∀ p ∈ perfData[k]!.1, 12 ≤ p.1 ∧ p.1 < 17 ∧ p.2 < 12 := by
        intro p hp
        have := List.all_eq_true.1 hb p hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact ⟨this.1.1, this.1.2, this.2⟩
      rw [Bool.true_and, Bool.true_and, zT_eq, mulT_frTable,
        eqRows_of (enc_ite (mul_enc hK (commProd_enc _ hl) zM_enc) (commProd_enc _ hl)) (qM_enc hk)]

open CFSG.Quasithin.J4M2 in
theorem c4201 : chkQRel = true ∧ chkQC = true ∧ chkQPerf = true := ⟨qrel_ok, qc_ok, qperf_ok⟩

end CertificateChecks.KernelJ4M2

end
