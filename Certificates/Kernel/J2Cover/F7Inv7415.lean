module

public import Certificates.Kernel.J2Cover.K19A
public import CFSG.Quasithin.Background.F7TwoInvSporJ2Inputs
import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover CFSG.Quasithin.F7Two

noncomputable abbrev pc315 (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

theorem comm_K {X Y : Nat} (cX : CnN 315 9 X) (cY : CnN 315 9 Y) :
    eqA 315 (compA 315 (unpack 315 9 X) (unpack 315 9 Y))
      (compA 315 (unpack 315 9 Y) (unpack 315 9 X)) = Nat.beq (pc315 X Y) (pc315 Y X) := by
  rw [compA_unpackN cX cY, compA_unpackN cY cX, eqA_unpackN (canon_pcN cX cY) (canon_pcN cY cX)]

theorem commB_K {X : Nat} (cX : CnN 315 9 X) :
    j2CommB (unpack 315 9 X) = unpack 315 9 (pc315 (pc315 (pc315 X (PA.S 1)) X) (PA.SI 1)) ∧
      CnN 315 9 (pc315 (pc315 (pc315 X (PA.S 1)) X) (PA.SI 1)) := by
  have c1 := cPA 1 (by omega)
  have cI : CnN 315 9 (PA.SI 1) := by quickRfl
  have hi : invCand 315 autStrong[1]! = unpack 315 9 (PA.SI 1) := by
    rw [hb']
    exact CFSG.KC.LQT.Cov.T.invCand_unpack (allN_spec perm 1 (by omega))
  have c2 := canon_pcN cX c1
  have c3 := canon_pcN c2 cX
  unfold j2CommB
  rw [hi, hb', compA_unpackN cX c1, compA_unpackN c2 cX, compA_unpackN c3 cI]
  exact ⟨rfl, canon_pcN c3 cI⟩

theorem orderThree_K {C : Nat} (cC : CnN 315 9 C) :
    j2OrderThree (unpack 315 9 C) =
      (Nat.beq (pc315 C (pc315 C C)) (pidn 315 9) && !Nat.beq C (pidn 315 9)) := by
  have cid : CnN 315 9 (pidn 315 9) := by quickRfl
  have hid : idA 315 = unpack 315 9 (pidn 315 9) := idA_eq (by quickRfl)
  have c2 := canon_pcN cC cC
  unfold j2OrderThree
  rw [hid, compA_unpackN cC cC, compA_unpackN cC c2, eqA_unpackN (canon_pcN cC c2) cid,
    eqA_unpackN cC cid]

theorem j2InvChk_K : j2InvChk () = true := by
  have c0 := cPA 0 (by omega)
  unfold j2InvChk
  rw [hou, hta, ha, comm_K cOU c0, comm_K cTA c0, (commB_K cOU).1, (commB_K cTA).1,
    orderThree_K (commB_K cOU).2, orderThree_K (commB_K cTA).2]
  quickRfl

end CertificateChecks.KernelJ2Cover

end
