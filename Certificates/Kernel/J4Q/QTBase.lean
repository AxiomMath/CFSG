module

public import Certificates.Kernel.J4Q.Mat
public import Certificates.Kernel.J4Q.QTData
public import CFSG.Certificates.Kernel.J4Q.RepQT
public import CFSG.Certificates.Kernel.Spor.Loops
import Certificates.Kernel.J4Q.Strs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.ZW CFSG.Sporadic.J4.QT.zWord
#j4q_strs CFSG.KD.J4Q.CW CFSG.Sporadic.J4.QT.conjWords

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def cwK : List (List Int) :=
  [lettersK CW.s0, lettersK CW.s1, lettersK CW.s2, lettersK CW.s3, lettersK CW.s4, lettersK CW.s5,
    lettersK CW.s6, lettersK CW.s7, lettersK CW.s8, lettersK CW.s9, lettersK CW.s10]

@[expose] noncomputable def uWordK (j : Nat) : List Int :=
  cwK.getD j [] ++ lettersK ZW.s0 ++ negRev (cwK.getD j [])

theorem uWord_eq (j : Nat) : uWord j = uWordK j := by
  unfold uWord uWordK
  rw [ZW.eq, CW.eq]
  simp only [List.map_cons, List.map_nil, lettersOfString_ofList, invWord_eq]
  rfl

@[expose] noncomputable def Us : List Nat := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

theorem u_chk : CFSG.KC.Enum.allN 11 (fun j =>
    Nat.beq (getN one Us j) (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] (uWordK j))) = true := by
  quickRfl

theorem uTab_enc : ∀ j < Us.length,
    WfA ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ())) ∧
      encR ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ())) = getN one Us j := by
  intro j hj
  have hj' : j < 11 := hj
  have hget : (uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ()) =
      wordRows (locMats ()) (locInvs ()) (uWord j) := by
    simp [uTab, hj']
  rw [hget]
  obtain ⟨hw, he⟩ := enc_wordRows hK loc_gens loc_invs (uWord j)
  refine ⟨hw, ?_⟩
  rw [he, uWord_eq]
  exact (Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec u_chk j hj')).symm

theorem Us_length : Us.length = 11 := rfl

theorem rowsA_enc : WfA (rowsA ()) ∧ encR (rowsA ()) = A := base_gens 0

theorem rowsB_enc : WfA (rowsB ()) ∧ encR (rowsB ()) = B := base_gens 1

theorem eta_enc (m : Nat) : WfA (etaRows (uTab (locMats ()) (locInvs ())) 11 m) ∧
    encR (etaRows (uTab (locMats ()) (locInvs ())) 11 m) = etaK c rm one Us m :=
  enc_etaRows hK uTab_enc m

end CertificateChecks.KernelJ4Q

end
