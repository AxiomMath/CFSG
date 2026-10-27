module

public import CFSG.Sporadic.J4.QT2LocZNative
public import Certificates.Kernel.J4Q.QTBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem mix_gens (k : Nat) : WfA (mixMats[k]?.getD (idRows ())) ∧
    encR (mixMats[k]?.getD (idRows ())) = getN one ([A, B] ++ [L0, L1, L2]) k :=
  gens_append (by rfl) base_gens loc_gens k

theorem mix_invs (k : Nat) : WfA (mixInvs[k]?.getD (idRows ())) ∧
    encR (mixInvs[k]?.getD (idRows ())) = getN one ([Ai, Bi] ++ [L0i, L1i, L2i]) k :=
  gens_append (by simp [baseInvs, baseMats]) base_invs loc_invs k

theorem rootV_wf : rootV.wf = true := by decide

theorem commRoot_of (w : List Int)
    (h : (Nat.beq (mulJ c rm (wordJ c rm one ([A, B] ++ [L0, L1, L2]) ([Ai, Bi] ++ [L0i, L1i, L2i]) w)
          (etaK c rm one Us 1131))
        (mulJ c rm (etaK c rm one Us 1131)
          (wordJ c rm one ([A, B] ++ [L0, L1, L2]) ([Ai, Bi] ++ [L0i, L1i, L2i]) w)) &&
      neN (vecJ rm (v2N rootV)
          (wordJ c rm one ([A, B] ++ [L0, L1, L2]) ([Ai, Bi] ++ [L0i, L1i, L2i]) w)) (v2N rootV)) = true) :
    chkCommRoot (locMats ()) (locInvs ()) w = true := by
  obtain ⟨hgw, hge⟩ := enc_wordRows hK mix_gens mix_invs w
  obtain ⟨hzw, hze⟩ := eta_enc 1131
  unfold chkCommRoot mixRowsOf
  simp only []
  rw [eqRows_eq (wf_mulRows hgw hzw) (wf_mulRows hzw hgw), enc_mulRows hK hgw hzw,
    enc_mulRows hK hzw hgw, differs_eq (wf_frApply hgw _) rootV_wf, v2N_frApply hK hgw rootV_wf,
    hge, hze]
  exact h

theorem order_of (w : List Int) (p : Nat) (h1 : chkCommRoot (locMats ()) (locInvs ()) w = true)
    (h2 : Nat.beq (powJ c rm one
        (wordJ c rm one ([A, B] ++ [L0, L1, L2]) ([Ai, Bi] ++ [L0i, L1i, L2i]) w) p) one = true) :
    chkOrder (locMats ()) (locInvs ()) w p = true := by
  obtain ⟨hgw, hge⟩ := enc_wordRows hK mix_gens mix_invs w
  unfold chkOrder mixRowsOf
  rw [h1, eqRows_eq (wf_powRows hgw p) wf_idRows, enc_powRows hK hgw, hge, enc_idRows hK, h2]
  rfl

theorem g_comm : chkCommRoot (locMats ()) (locInvs ()) gWord = true := commRoot_of _ (by quickRfl)
theorem y7_comm : chkCommRoot (locMats ()) (locInvs ()) y7Word = true := commRoot_of _ (by quickRfl)
theorem y11_comm : chkCommRoot (locMats ()) (locInvs ()) y11Word = true := commRoot_of _ (by quickRfl)

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem c4016 : (chkCommRoot (locMats ()) (locInvs ()) gWord = true)
    ∧ (chkOrder (locMats ()) (locInvs ()) y7Word 7 = true)
    ∧ (chkOrder (locMats ()) (locInvs ()) y11Word 11 = true) :=
  ⟨g_comm, order_of _ _ y7_comm (by quickRfl), order_of _ _ y11_comm (by quickRfl)⟩

end CertificateChecks.KernelJ4Q

end
