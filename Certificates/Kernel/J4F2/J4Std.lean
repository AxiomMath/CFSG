module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.SquaresNative
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11Native
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModLiftNative
public import Certificates.Kernel.J4Q.MaskRep
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.QTBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CertificateChecks.KernelJ4Q

@[expose] noncomputable def wK (w : List Int) : Nat := wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] w

@[expose] noncomputable def eK (m : Nat) : Nat := etaK c rm one Us m

theorem word_enc (w : List Int) : WfA (wordRows (locMats ()) (locInvs ()) w) ∧
    encR (wordRows (locMats ()) (locInvs ()) w) = wK w :=
  enc_wordRows hK loc_gens loc_invs w

theorem etaU_enc (m : Nat) : WfA (etaRows (uTab (locMats ()) (locInvs ())) 11 m) ∧
    encR (etaRows (uTab (locMats ()) (locInvs ())) 11 m) = eK m :=
  eta_enc m

open CFSG.EvenSporadicStandard.J4Std in
theorem sqB_chk : Nat.beq (mulJ c rm (wK sqWordB) (wK sqWordB)) (eK 1) = true := by quickRfl

open CFSG.EvenSporadicStandard.J4Std in
theorem sqA_chk : Nat.beq (mulJ c rm (wK sqWordA) (wK sqWordA)) (eK 3) = true := by quickRfl

open CFSG.EvenSporadicStandard.J4Std in
open CFSG.Sporadic.J4.Native CFSG.EvenSporadicStandard.J4Std in
theorem c25120 : chkSq (locMats ()) (locInvs ()) = true := by
  unfold chkSq chkSqRoot
  rw [mkEq (mkMul (word_enc _) (word_enc _)) (etaU_enc _),
    mkEq (mkMul (word_enc _) (word_enc _)) (etaU_enc _), sqB_chk, sqA_chk]
  rfl

open CFSG.EvenSporadicStandard.J4Std.Data11 in
@[expose] noncomputable def QK : Nat := mulJ c rm (eK qMask) (wK qWord)

open CFSG.EvenSporadicStandard.J4Std.Data11 in
theorem p11_chk : Nat.beq (powJ c rm one (wK pWord) 11) one = true := by quickRfl

open CFSG.EvenSporadicStandard.J4Std.Data11 in
theorem qp_chk : Nat.beq (mulJ c rm QK (wK pWord))
    (mulJ c rm (mulJ c rm (wK pWord) (wK pWord)) QK) = true := by quickRfl

open CFSG.EvenSporadicStandard.J4Std.Data11 in
open CFSG.Sporadic.J4.Native CFSG.EvenSporadicStandard.J4Std.Data11 in
theorem c25130 : chkPQ (locMats ()) (locInvs ()) = true := by
  unfold chkPQ
  simp only []
  have hQ := mkMul (etaU_enc qMask) (word_enc qWord)
  rw [mkEq (mkPow (word_enc _) 11) mkId, mkEq (mkMul hQ (word_enc _))
    (mkMul (mkMul (word_enc _) (word_enc _)) hQ), p11_chk]
  exact qp_chk

open CFSG.EvenSporadicStandard.J4Std.DataMod in
@[expose] noncomputable def SK : Nat := mulJ c rm (wK liftWordS) (eK liftMaskS)

open CFSG.EvenSporadicStandard.J4Std.DataMod in
@[expose] noncomputable def TK : Nat := mulJ c rm (wK liftWordT) (eK liftMaskT)

theorem s2_chk : Nat.beq (mulJ c rm SK SK) one = true := by quickRfl

theorem t2_chk : Nat.beq (mulJ c rm TK TK) one = true := by quickRfl

theorem st2_chk : Nat.beq (mulJ c rm (mulJ c rm SK TK) (mulJ c rm SK TK)) one = true := by quickRfl

open CFSG.EvenSporadicStandard.J4Std.DataMod in
open CFSG.Sporadic.J4.Native CFSG.EvenSporadicStandard.J4Std.DataMod in
theorem c25142 : chkLift (locMats ()) (locInvs ()) = true := by
  unfold chkLift liftRows
  simp only []
  have hS := mkMul (word_enc liftWordS) (etaU_enc liftMaskS)
  have hT := mkMul (word_enc liftWordT) (etaU_enc liftMaskT)
  rw [mkEq (mkMul hS hS) mkId, mkEq (mkMul hT hT) mkId,
    mkEq (mkMul (mkMul hS hT) (mkMul hS hT)) mkId]
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨s2_chk, t2_chk⟩, st2_chk⟩

end CertificateChecks.KernelJ4F2

end
