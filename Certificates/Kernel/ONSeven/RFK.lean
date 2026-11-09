module

public import Certificates.Data.Kernel.ONSevenR
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.ONR

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def fKpt (n nC nF w ng nfg : Nat) (TC TF G FG PX : Nat → Nat) : Bool :=
  bAnd(allN nfg (fun l => memK nC TC (FG l)),
  bAnd(allN ng (fun k => allN nfg fun l =>
      memK nF TF (pcomp n w (mask w) (G k) (pcomp n w (mask w) (FG l)
        (pinvS n w (mask w) (G k))))),
  bAnd(memK nF TF (PX 1),
    allN nC (fun k => Bool.rec (motive := fun _ => Bool)
      (CFSG.KC.LQT.P.anyN nfg fun l => CFSG.KC.LQT.P.anyN n fun i =>
        !(Nat.beq (pg w (mask w) (TC k) (pg w (mask w) (FG l) i))
          (pg w (mask w) (FG l) (pg w (mask w) (TC k) i))))
      true (CFSG.KC.LQT.P.anyN (nat_lit 7) fun e => Nat.beq (TC k) (PX e))))))

theorem fK_of_fKpt {n nC nF w ng nfg : Nat} {TC TF G FG PX : Nat → Nat} (hn : n < 2 ^ 32)
    (h : fKpt n nC nF w ng nfg TC TF G FG PX = true) :
    fK n nC nF w ng nfg TC TF G FG PX = true := by
  unfold fKpt at h
  unfold fK
  simp only [bAnd_iff] at h ⊢
  refine ⟨h.1, h.2.1, h.2.2.1, CFSG.KC.BfsPin.allN_intro fun k hk => ?_⟩
  have hk' := allN_spec h.2.2.2 k hk
  cases hA : CFSG.KC.LQT.P.anyN (nat_lit 7) (fun e => Nat.beq (TC k) (PX e))
  · rw [hA] at hk'
    obtain ⟨l, hl, hl'⟩ := (CFSG.KC.LQT.P.anyN_iff _ _).1 hk'
    obtain ⟨i, hi, hi'⟩ := (CFSG.KC.LQT.P.anyN_iff _ _).1 hl'
    have hc : allN nfg (fun l => Nat.beq (pcomp n w (mask w) (TC k) (FG l))
        (pcomp n w (mask w) (FG l) (TC k))) = false := by
      cases hb : allN nfg (fun l => Nat.beq (pcomp n w (mask w) (TC k) (FG l))
          (pcomp n w (mask w) (FG l) (TC k)))
      · rfl
      · have he := Nat.eq_of_beq_eq_true (allN_spec hb l hl)
        have hp := congrArg (fun p => pg w (mask w) p i) he
        simp only [CFSG.KS.PF.pg_pcomp hn hi] at hp
        rw [hp, Nat.beq_refl] at hi'
        exact absurd hi' (by decide)
    rw [hc]
  · cases allN nfg (fun l => Nat.beq (pcomp n w (mask w) (TC k) (FG l))
        (pcomp n w (mask w) (FG l) (TC k))) <;> rfl

end CFSG.KC.ONR

end
