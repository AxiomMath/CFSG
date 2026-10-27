
module

public import CFSG.Certificates.Kernel.ONOut.InvVSound
public import Certificates.Kernel.Sporadic.ONC.ChainBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.ONC
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Kernel
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK)

theorem lt_of_shr {p : ℕ} (h : (p >>> 154 == 0) = true) : p < 2 ^ 256 := by
  rw [beq_iff_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 154)] at h
  exact lt_trans h (by norm_num)

theorem mul_one_comm' {d K : Type*} [Fintype d] [DecidableEq d] [Field K] {U X : Matrix d d K}
    (h : X * U = 1) : U * X = 1 :=
  mul_eq_one_comm.1 h

theorem invW_eq : invW 154 (basisRows (orbitData ())) = basisXLit := by
  have hU : toMat 154 (toVM (basisRows (orbitData ()))) * toMat 154 (toVM basisXLit) = 1 :=
    mul_one_comm' Xmat_mul_Umat0
  have hsz0 : (toVM (basisRows (orbitData ()))).size = 154 := by
    rw [toVM_size, basisR_size0]
  have hcan : canonM 154 (toVM (basisRows (orbitData ()))) = true := by
    refine CFSG.KS.ONOut.canonM_of hsz0 fun i hi => ?_
    rw [toVM_getElem!, basisR_getElem0 hi]
    exact CFSG.KS.ONOut.rowC_iff.1 (canon154_spec (orbit_parts.2.2.2 _
      (chainQ_lt0 (by rw [basis_parts0.1]; exact hi))).1)
  obtain ⟨hc, hm⟩ := CFSG.KS.ONOut.invV_sound hcan hU
  obtain ⟨hcs, hcr⟩ := canonM_spec hc
  have hsz : basisXLit.size = 154 := basis_parts0.2.2.1
  unfold invW
  apply Array.ext (by rw [Array.size_map, hcs, hsz])
  intro i h1 h2
  have hi : i < 154 := by rwa [hsz] at h2
  have hrow := hcr i (by rw [hcs]; exact hi)
  have hb : (basisXLit[i]!.toV.wf && basisXLit[i]!.toV.p >>> 154 == 0 &&
      basisXLit[i]!.toV.m >>> 154 == 0) = true := by
    rw [CertificateChecks.KernelSpor.ON2.X_get hi]
    exact canon154_spec (canon_sound (CertificateChecks.KernelSpor.ON2.X_canon hi))
  have hp : (invV 154 (toVM (basisRows (orbitData ()))))[i]!.p < 2 ^ 256 := by
    simp only [Bool.and_eq_true] at hrow
    exact lt_of_shr hrow.1.2
  have hmm : (invV 154 (toVM (basisRows (orbitData ()))))[i]!.m < 2 ^ 256 := by
    simp only [Bool.and_eq_true] at hrow
    exact lt_of_shr hrow.2
  rw [Array.getElem_map, ← getElem!_pos _ i (by rw [hcs]; exact hi),
    ← getElem!_pos basisXLit i h2]
  apply W.toV_inj
  rw [W.toV_ofV hp hmm]
  apply V.eq_of_canon hrow hb
  intro j hj
  have := congrFun (congrFun hm ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, toMat_apply, toVM_getElem!] at this
  exact this

theorem tabs_lt {x : ℕ} (hx : x < 245520) : tab ONW.A x < 245520 ∧ tab ONW.B x < 245520 :=
  ⟨(CertificateChecks.KernelSpor.ON2.inv_facts CertificateChecks.KernelSpor.ON2.invAll hx).1,
    (CertificateChecks.KernelSpor.ON2.inv_facts CertificateChecks.KernelSpor.ON2.invAll hx).2.1⟩

theorem alpha_ap {x : ℕ} (hx : x < 245520) : ap (orbitData ()).alpha x = tab ONW.A x :=
  ((CertificateChecks.KernelSpor.ON2.natTab_TR
    (CertificateChecks.KernelSpor.ON2.orb_tabs CertificateChecks.KernelSpor.ON2.mvAll
      CertificateChecks.KernelSpor.ON2.ordAll CertificateChecks.KernelSpor.ON2.sortAll).1
    fun i hi => (tabs_lt hi).1).2 x hx).1

theorem beta_ap {x : ℕ} (hx : x < 245520) : ap (orbitData ()).beta x = tab ONW.B x :=
  ((CertificateChecks.KernelSpor.ON2.natTab_TR
    (CertificateChecks.KernelSpor.ON2.orb_tabs CertificateChecks.KernelSpor.ON2.mvAll
      CertificateChecks.KernelSpor.ON2.ordAll CertificateChecks.KernelSpor.ON2.sortAll).2
    fun i hi => (tabs_lt hi).2).2 x hx).1

theorem QL_lt' : ∀ x ∈ QL, x < 245520 := CFSG.KS.PC.QL_lt chain_hyp

theorem img_toList {T : Table} {f : ℕ → ℕ} (hf : ∀ x < 245520, ap T x = f x) :
    (apT T chainQ).toList = mapK f QL := by
  rw [CFSG.KS.TW.apT_map, Array.toList_map, mapK_eq]
  exact List.map_congr_left fun x hx => hf x (QL_lt' x hx)

theorem img_lt {T : Table} (hT : ∀ x < 245520, ap T x < 245520) :
    ∀ x ∈ apT T chainQ, x < 245520 := by
  intro x hx
  rw [CFSG.KS.TW.apT_map, Array.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hT y (Q_lt chain_hyp y hy)

theorem iterK_eq (f : ℕ → ℕ) : ∀ e x, iterK f e x = f^[e] x
  | 0, _ => rfl
  | e + 1, x => by
    change strictN (iterK f e x) f = _
    rw [strictN_eq', iterK_eq f e x, Function.iterate_succ_apply']

theorem idx_pow {g : J0} {f : ℕ → ℕ} (hf : ∀ x < 245520, idx nPts g x = f x) :
    ∀ e, ∀ x < 245520, idx nPts (g ^ e) x = f^[e] x
  | 0, x, _ => by rw [pow_zero, idx_one]; rfl
  | e + 1, x, hx => by
    rw [pow_succ', idx_mul, idx_pow hf e x hx, Function.iterate_succ_apply',
      ← hf _ (by rw [← idx_pow hf e x hx]; exact idx_lt _ hx)]

theorem fixK_eq {T : Table} {g : J0} {f : ℕ → ℕ} (hT : Rep nPts T g)
    (hf : ∀ x < 245520, idx nPts g x = f x) (e : ℕ) :
    tupleEq (apT (powT nPts e T) chainQ) chainQ = fixK f e := by
  apply Bool.eq_iff_iff.2
  rw [tupleEq_iff_toList, fixK, listEqK_iff, mapK_eq, CFSG.KS.TW.apT_map, Array.toList_map]
  have e1 : chainQ.toList.map (ap (powT nPts e T)) = QL.map (iterK f e) := by
    apply List.map_congr_left
    intro x hx
    have hx' := QL_lt' x hx
    rw [Rep.powT nPts_lt hT e x hx', idx_pow hf e x hx', iterK_eq]
  rw [e1]
  rfl

theorem ordOK_of {T : Table} {g : J0} {f : ℕ → ℕ} (hT : Rep nPts T g)
    (hf : ∀ x < 245520, idx nPts g x = f x) {p e : ℕ} (he : 0 < e) (h : ordQ f p e = true) :
    ordOK nPts chainQ T (p, e) = true := by
  unfold ordQ at h
  rw [bAnd_iff'] at h
  unfold ordOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨he, ?_⟩, ?_⟩
  · rw [fixK_eq hT hf]
    exact h.1
  · rw [fixK_eq hT hf]
    exact notB_true h.2

theorem idx_a {x : ℕ} (hx : x < 245520) : idx nPts ga0 x = aQ x := by
  rw [← rep_ga0 x hx, alpha_ap hx]
  rfl

theorem idx_b {x : ℕ} (hx : x < 245520) : idx nPts (gb0 * ga0 * gb0) x = bQ x := by
  have h1 := (tabs_lt hx).2
  have h2 := (tabs_lt h1).1
  rw [idx_mul, idx_mul, ← rep_gb0 x hx, beta_ap hx, ← rep_ga0 _ h1, alpha_ap h1,
    ← rep_gb0 _ h2, beta_ap h2]
  rfl

theorem bQ_lt {x : ℕ} (hx : x < 245520) : bQ x < 245520 :=
  (tabs_lt (tabs_lt (tabs_lt hx).2).1).2

theorem regs_get0 : Rep nPts (regs0 (orbitData ()))[0]! ga0 := by
  have := regs_rep 0 (by rw [regs_size]; norm_num)
  simpa [regs0G] using this

theorem regs_get1 : Rep nPts (regs0 (orbitData ()))[1]! (gb0 * ga0 * gb0) := by
  have := regs_rep 1 (by rw [regs_size]; norm_num)
  simpa [regs0G] using this

theorem ord_ok : ordChecks (regs0 (orbitData ())) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, o1, o2, o3⟩ := misc_parts
  unfold ordChecks
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨ordOK_of regs_get0 (fun x hx => idx_a hx) (by norm_num) o1,
    ordOK_of regs_get1 (fun x hx => idx_b hx) (by norm_num) o2⟩, ?_⟩
  refine ordOK_of (Rep.compT regs_get0 regs_get1) (fun x hx => ?_) (by norm_num) o3
  rw [idx_mul, idx_b hx, idx_a (bQ_lt hx)]

end CertificateChecks.KernelSpor.ONC

end
