module

public import CFSG.Sporadic.J4.QTRankWitNative
public import Certificates.Kernel.J4Q.QTBase
public import Certificates.Kernel.J4Q.RankData
public import CFSG.Certificates.Kernel.J4Q.RepRank
public import Certificates.Kernel.J4Q.Orbits
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000


namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def R0 : List Nat := [A, B] ++ List.replicate 29 one

theorem getN_replicate (d : Nat) : ∀ (n k : Nat), getN d (List.replicate n d) k = d
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, k + 1 => getN_replicate d n k

theorem init_enc (r : Nat) : WfA (init11 r) ∧ encR (init11 r) = getN one R0 r := by
  unfold init11
  rcases r with _ | _ | r
  · exact rowsA_enc
  · exact rowsB_enc
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.reduceEqDiff]
    rw [R0, getN_append]
    simp only [List.length_cons, List.length_nil]
    split_ifs with h2
    · omega
    · rw [getN_replicate]
      exact id_enc hK

theorem tgt_ok : ∀ ins ∈ prog11, insTgt ins < R0.length := by decide

theorem x_chk : Nat.beq X11L (getN one (runL c rm one R0 prog11) 22) = true := by quickRfl

theorem y_chk : Nat.beq Y11L (getN one (runL c rm one R0 prog11) 30) = true := by quickRfl

theorem X_enc : WfA (X11 ()) ∧ encR (X11 ()) = X11L := by
  have h := runN_enc hK prog11 init11 R0 init_enc tgt_ok 22
  exact ⟨h.1, h.2.trans (Nat.eq_of_beq_eq_true x_chk).symm⟩

theorem Y_enc : WfA (Y11 ()) ∧ encR (Y11 ()) = Y11L := by
  have h := runN_enc hK prog11 init11 R0 init_enc tgt_ok 30
  exact ⟨h.1, h.2.trans (Nat.eq_of_beq_eq_true y_chk).symm⟩

theorem Z_enc : WfA (Z11 ()) ∧ encR (Z11 ()) = mulJ c rm (mulJ c rm (mulJ c rm X11L Y11L)
    (powJ c rm one X11L 10)) (powJ c rm one Y11L 10) :=
  mul_enc hK (mul_enc hK (mul_enc hK X_enc Y_enc) (pow_enc hK X_enc 10)) (pow_enc hK Y_enc 10)

theorem gMat0_enc : WfA (gMat 0) ∧ encR (gMat 0) = A := base_gens 0

theorem gMat1_enc : WfA (gMat 1) ∧ encR (gMat 1) = B := base_gens 1

theorem gInv0_enc : WfA (gInv 0) ∧ encR (gInv 0) = Ai := base_invs 0

theorem gInv1_enc : WfA (gInv 1) ∧ encR (gInv 1) = Bi := base_invs 1

theorem C_enc : WfA (C37 ()) ∧ encR (C37 ()) = mulJ c rm (etaK c rm one Us 1)
    (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm Ai Bi) Ai) Bi) Ai)
      (etaK c rm one Us 1)) (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm A B) A) B) A)) :=
  mul_enc hK (eta_enc 1) (mul_enc hK (mul_enc hK (mul_enc hK (mul_enc hK (mul_enc hK
    (mul_enc hK gInv0_enc gInv1_enc) gInv0_enc) gInv1_enc) gInv0_enc) (eta_enc 1))
    (mul_enc hK (mul_enc hK (mul_enc hK (mul_enc hK gMat0_enc gMat1_enc) gMat0_enc) gMat1_enc)
      gMat0_enc))

theorem AE_enc : WfA (AE5 ()) ∧ encR (AE5 ()) = mulJ c rm A (etaK c rm one Us 5) :=
  mul_enc hK gMat0_enc (eta_enc 5)

theorem orbit_chk : (orbits.any fun o => o.1 == 3 && o.2.1.any fun p => p.1 == 5) = true := by
  rw [OR.eq]
  simp only [ptsOfString_ofList]
  quickRfl

theorem z_ne : neN (mulJ c rm (mulJ c rm (mulJ c rm X11L Y11L) (powJ c rm one X11L 10))
    (powJ c rm one Y11L 10)) one = true := by quickRfl

theorem c_ne : neN (mulJ c rm (etaK c rm one Us 1)
    (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm Ai Bi) Ai) Bi) Ai)
      (etaK c rm one Us 1)) (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm A B) A) B) A))) one = true := by
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem c4026 : (eqRows (powRows (X11 ()) 11) idRows = true)
    ∧ (eqRows (powRows (Y11 ()) 11) idRows = true)
    ∧ (eqRows (powRows (Z11 ()) 11) idRows = true)
    ∧ (eqRows (Z11 ()) idRows = false)
    ∧ (wfRows (Z11 ()) = true ∧ wfRows idRows = true)
    ∧ (eqRows (mulRows (X11 ()) (Z11 ())) (mulRows (Z11 ()) (X11 ())) = true)
    ∧ (eqRows (mulRows (Y11 ()) (Z11 ())) (mulRows (Z11 ()) (Y11 ())) = true)
    ∧ (eqRows (mulRows (mulRows rowsA (X11 ())) rowsA) (powRows (X11 ()) 10) = true)
    ∧ (eqRows (mulRows rowsA (Z11 ())) (mulRows (Z11 ()) rowsA) = true)
    ∧ (eqRows (powRows (C37 ()) 37) idRows = true)
    ∧ (eqRows (C37 ()) idRows = false)
    ∧ (wfRows (C37 ()) = true)
    ∧ (eqRows (powRows (AE5 ()) 11) idRows = true)
    ∧ (∃ o ∈ orbits, o.1 = 3 ∧ ∃ p ∈ o.2.1, p.1 = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ⟨wf_bool Z_enc.1, wf_bool wf_idRows⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    wf_bool C_enc.1, ?_, ?_⟩
  · rw [eqRows_of (pow_enc hK X_enc 11) (id_enc hK)]
    quickRfl
  · rw [eqRows_of (pow_enc hK Y_enc 11) (id_enc hK)]
    quickRfl
  · rw [eqRows_of (pow_enc hK Z_enc 11) (id_enc hK)]
    quickRfl
  · rw [eqRows_of Z_enc (id_enc hK)]
    exact beq_false z_ne
  · rw [eqRows_of (mul_enc hK X_enc Z_enc) (mul_enc hK Z_enc X_enc)]
    quickRfl
  · rw [eqRows_of (mul_enc hK Y_enc Z_enc) (mul_enc hK Z_enc Y_enc)]
    quickRfl
  · rw [eqRows_of (mul_enc hK (mul_enc hK rowsA_enc X_enc) rowsA_enc) (pow_enc hK X_enc 10)]
    quickRfl
  · rw [eqRows_of (mul_enc hK rowsA_enc Z_enc) (mul_enc hK Z_enc rowsA_enc)]
    quickRfl
  · rw [eqRows_of (pow_enc hK C_enc 37) (id_enc hK)]
    quickRfl
  · rw [eqRows_of C_enc (id_enc hK)]
    exact beq_false c_ne
  · rw [eqRows_of (pow_enc hK AE_enc 11) (id_enc hK)]
    quickRfl
  · simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] using orbit_chk

end CertificateChecks.KernelJ4Q

end
