module

public import CFSG.Sporadic.J4.QTOutObsNative
public import CFSG.Sporadic.J4.QTOutCocNative
public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.Sporadic.J4.QTOutActNative
public import CFSG.Sporadic.J4.QTNative
public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem etaR_enc (m : Nat) : WfA (etaR m) ∧ encR (etaR m) = etaK c rm one Us m := eta_enc m

theorem e5_enc : WfA e5Rows ∧ encR e5Rows = etaK c rm one Us cA := eta_enc cA

theorem h_enc : WfA hRows ∧ encR hRows = wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] wObs :=
  enc_wordRows hK loc_gens loc_invs wObs

theorem g_enc : WfA gRows ∧ encR gRows = mulJ c rm (etaK c rm one Us (cB ^^^ aObs))
    (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] wObs) :=
  mul_enc hK (eta_enc (cB ^^^ aObs)) h_enc

theorem y_enc : WfA yRows ∧ encR yRows = mulJ c rm (mulJ c rm B A) Bi :=
  mul_enc hK (mul_enc hK rowsB_enc rowsA_enc) (base_invs 1)

theorem fv_chk : strictB (etaK c rm one Us cA) (fun E => fvs.toList.all fun f =>
    andB (Nat.blt (v2N f) (Nat.shiftLeft 1 112)) (Nat.beq (vecJ rm (v2N f) E) (v2N f))) = true := by
  quickRfl

theorem xv_chk : xvs.toList.all (fun x => Nat.blt (v2N x) (Nat.shiftLeft 1 112)) = true := by
  quickRfl

theorem fvTri_chk : triK (fvs.toList.map v2N) fps.toList = true := by quickRfl

theorem xTri_chk : strictB (mulJ c rm (etaK c rm one Us (cB ^^^ aObs))
    (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] wObs)) (fun G =>
      triK (xvs.toList.map fun x => Nat.xor (vecJ rm (v2N x) G) (v2N x)) xps.toList) = true := by
  quickRfl

theorem ximgs_tri : triOK ximgs xps = true := by
  apply triOK_of
  have h := xTri_chk
  rw [strictB_eq] at h
  have hx : ximgs.toList.map v2N = xvs.toList.map fun x => Nat.xor (vecJ rm (v2N x)
      (mulJ c rm (etaK c rm one Us (cB ^^^ aObs)) (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] wObs)))
      (v2N x) := by
    rw [ximgs, Array.toList_map, List.map_map]
    apply List.map_congr_left
    intro x hx
    have hw : x.wf = true :=
      wf_of_lt (lt_of_blt (List.all_eq_true.1 xv_chk x hx))
    change v2N ((frApply (frTable gRows) x).xor x) = _
    rw [v2N_xor, v2N_frApply hK g_enc.1 hw, g_enc.2]
  rw [hx]
  exact h

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem c4023 : (wfRows e5Rows = true ∧ wfRows gRows = true ∧ wfRows yRows = true)
    ∧ (eqRows (mulRows yRows yRows) idRows = true)
    ∧ (eqRows (mulRows (mulRows yRows e5Rows) yRows) (mulRows (etaR cB) hRows) = true)
    ∧ (∀ ℓ ∈ wObs, ℓ ∈ letters)
    ∧ (∀ f ∈ fvs, (frApply (frTable e5Rows) f).beq f = true)
    ∧ (triOK fvs fps = true)
    ∧ (triOK ximgs xps = true)
    ∧ (fvs.size = 62 ∧ xvs.size = 51)
    ∧ (cA < 2 ^ 11 ∧ cB < 2 ^ 11) := by
  refine ⟨⟨wf_bool e5_enc.1, wf_bool g_enc.1, wf_bool y_enc.1⟩, ?_, ?_, by decide, ?_,
    triOK_of _ _ fvTri_chk, ximgs_tri, ⟨rfl, rfl⟩, by decide⟩
  · rw [eqRows_of (mul_enc hK y_enc y_enc) (id_enc hK)]
    quickRfl
  · rw [eqRows_of (mul_enc hK (mul_enc hK y_enc e5_enc) y_enc) (mul_enc hK (etaR_enc cB) h_enc)]
    quickRfl
  · intro f hf
    have h := fv_chk
    rw [strictB_eq] at h
    have hf' := List.all_eq_true.1 h f (Array.mem_def.1 hf)
    rw [andB_eq, Bool.and_eq_true] at hf'
    have hw : f.wf = true := wf_of_lt (lt_of_blt hf'.1)
    rw [beq_v2N, v2N_frApply hK e5_enc.1 hw, e5_enc.2]
    exact hf'.2

end CertificateChecks.KernelJ4Q

end
