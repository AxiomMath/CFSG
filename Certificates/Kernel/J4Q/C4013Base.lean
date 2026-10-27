
module

public import CFSG.Sporadic.J4.QT2LocX0KNative
public import Certificates.Kernel.J4Q.KOrbOk
public import Certificates.Kernel.J4Q.C4027I
public import Certificates.Kernel.J4Q.D4K
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem kq_chk : allR 6 (fun i => andB (andB (Nat.beq (mulJ c rm (getN one KG i) (getN one KG (i + 6))) one)
      (Nat.beq (mulJ c rm (getN one KG (i + 6)) (getN one KG i)) one))
    (Nat.beq (vecJ rm (v2N x0Q1) (getN one KG i)) (v2N x0Q1))) = true := by
  quickRfl

theorem x0Q1_wf : x0Q1.wf = true := by decide

theorem kq_pts : inLK (v2N x0Q1) XPTS = true := by quickRfl

theorem kq_diff : neN (v2N x0Q1) (v2N rootV) = true := by quickRfl

theorem kletters : (kWK.all fun w => w.all fun l => letters.contains l) = true := by quickRfl

theorem kgens_ok : chkKGens = true := by
  have hs := kGen_size
  have hsi := kInv_size
  have hl : CFSG.Sporadic.J4.QT2.kWords.length = 6 := by
    rw [kqWords_eq]
    rfl
  have h5 : ((List.range 6).all fun i => CFSG.Sporadic.J4.QT2.wfRows kGenRows[i]! &&
      CFSG.Sporadic.J4.QT2.wfRows kInvRows[i]! &&
      eqRows (mulRows kGenRows[i]! kInvRows[i]!) idRows &&
      eqRows (mulRows kInvRows[i]! kGenRows[i]!) idRows &&
      (frApply (frTable kGenRows[i]!) x0Q1).beq x0Q1) = true := by
    refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have hg := kGen_enc hi'
    have hv := kInv_enc hi'
    have k := allR_spec kq_chk i hi'
    simp only [andB_eq, Bool.and_eq_true] at k
    have w1 : CFSG.Sporadic.J4.QT2.wfRows (kGenRows[i]!) = true := wf_bool hg.1
    have w2 : CFSG.Sporadic.J4.QT2.wfRows (kInvRows[i]!) = true := wf_bool hv.1
    rw [w1, w2, eqRows_of (mul_enc hK hg hv) (id_enc hK), eqRows_of (mul_enc hK hv hg) (id_enc hK),
      beq_v2N, v2N_frApply hK hg.1 x0Q1_wf, hg.2, k.1.1, k.1.2, k.2]
    rfl
  have hpts : x0Pts.contains x0Q1 = true := by
    rw [List.contains_iff_mem]
    have hm := inLK_mem kq_pts
    rw [← d4pts_map] at hm
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
    rw [← v2N_inj hpe]
    exact List.mem_eraseDups.1 hp
  have hdiff : differs x0Q1 rootV = true := by
    rw [differs_eq x0Q1_wf rootV_wf']
    exact kq_diff
  have hlet : (CFSG.Sporadic.J4.QT2.kWords.all fun w => w.all fun l => letters.contains l) = true := by
    rw [kqWords_eq]
    exact kletters
  unfold chkKGens
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨hl, hs⟩, hsi⟩, hlet⟩, h5⟩, hpts⟩, hdiff⟩

@[expose] noncomputable def commQ (m : Nat) : Bool :=
  Nat.beq (mulJ c rm m (getN one XG 0)) (mulJ c rm (getN one XG 0) m)

theorem kcomm_chk : eqLK ((List.range 15360).filter fun k => inLK k KCOMM) KCOMM = true := by quickRfl

theorem kcomm_len : KCOMM.length = 40 := rfl

theorem efix_eq {v : V2} (hv : v.wf = true) :
    eFixMasks (uTab (locMats ()) (locInvs ())) v =
      (List.range 2048).filter fun k => notB (neN (vecEtaK rm Us k (v2N v)) (v2N v)) := by
  unfold eFixMasks
  apply List.filter_congr
  intro k _
  rw [differs_eq (etaVec_enc hv k).1 hv, (etaVec_enc hv k).2, notB_eq]

theorem efq_chk : Nat.beq ((List.range 2048).filter fun k => notB (neN (vecEtaK rm Us k (v2N x0Q1)) (v2N x0Q1))).length
    2 = true := by
  quickRfl

theorem efp_chk : allR 7 (fun l => (fun x => Nat.beq ((List.range 2048).filter fun k =>
    notB (neN (vecEtaK rm Us k x) x)).length (getN 0 [2048, 2, 1, 1, 16, 512, 128] l))
    (pathVK rm one [A, B] (repPaths.getD l []) (v2N rootV))) = true := by
  quickRfl

theorem estab_ok : chkEStab = true := by
  unfold chkEStab
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, List.all_eq_true.2 fun l hl => ?_⟩
  · rw [efix_eq x0Q1_wf]
    exact Nat.eq_of_beq_eq_true efq_chk
  · have hl' := List.mem_range.1 hl
    have k := allR_spec efp_chk l hl'
    beta_reduce at k
    rw [getN_eq_getD] at k
    rw [beq_iff_eq, efix_eq (pathVec_enc _).1, (pathVec_enc _).2]
    exact Nat.eq_of_beq_eq_true k

end CertificateChecks.KernelJ4Q

end
